import ClippedSGD.HingeGeometry
import ClippedSGD.MomentumRun

/-! Gradient-only rules in one dimension, the oracles of the instance and of the
reference, and the coupling of their runs. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower
open HingeGeometry

abbrev Rule (S : Type*) := (t : ℕ) → ((Fin (t+1) → ℝ) × S) → ℝ

def Nonnegative {S : Type*} (R : Rule S) : Prop := ∀ t h, 0 ≤ R t h

def asMomentum {S : Type*} (R : Rule S) : MomentumRun.Rule ℝ S :=
  fun t h => (0, R t h, 1)

def position {S : Type*} (R : Rule S) (oracle : ℕ → ℝ → ℝ) (seed : S) (t : ℕ) : ℝ :=
  MomentumRun.position (asMomentum R) oracle seed t

def response {S : Type*} (R : Rule S) (oracle : ℕ → ℝ → ℝ) (seed : S) (t : ℕ) : ℝ :=
  R t (Fin.snoc (MomentumRun.trajectory (asMomentum R) oracle seed t).2.2
    (oracle t (position R oracle seed t)), seed)

lemma position_zero {S : Type*} (R : Rule S) (o : ℕ → ℝ → ℝ) (seed : S) :
    position R o seed 0 = 0 := rfl

lemma position_step {S : Type*} (R : Rule S) (o : ℕ → ℝ → ℝ) (seed : S) (t : ℕ) :
    position R o seed (t+1) = position R o seed t -
      response R o seed t * o t (position R o seed t) := by
  simp only [position, MomentumRun.position_step, MomentumRun.velocity_step,
    MomentumRun.damping, MomentumRun.gain, MomentumRun.scale, MomentumRun.controls,
    asMomentum, zero_smul, one_smul, zero_add, smul_eq_mul, response, zero_mul, one_mul]

lemma response_nonneg {S : Type*} {R : Rule S} (hR : Nonnegative R)
    (o : ℕ → ℝ → ℝ) (seed : S) (t : ℕ) : 0 ≤ response R o seed t := hR t _

def referenceOracle (A : ℝ) (ω : ℕ → Bool) (t : ℕ) (_x : ℝ) : ℝ :=
  -(if ω t then A else 0)

def actualOracle (μ y A : ℝ) (ω : ℕ → Bool) (t : ℕ) (x : ℝ) : ℝ :=
  sampleGrad μ y (if ω t then A else 0) x

lemma reference_step {S : Type*} (R : Rule S) (A : ℝ) (ω : ℕ → Bool)
    (seed : S) (t : ℕ) :
    position R (referenceOracle A ω) seed (t+1) =
      position R (referenceOracle A ω) seed t +
        response R (referenceOracle A ω) seed t * (if ω t then A else 0) := by
  rw [position_step]
  simp only [referenceOracle]
  ring

lemma reference_monotone {S : Type*} {R : Rule S} (hR : Nonnegative R)
    {A : ℝ} (hA : 0 ≤ A) (ω : ℕ → Bool) (seed : S) :
    Monotone (position R (referenceOracle A ω) seed) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [reference_step]
  have h := mul_nonneg (response_nonneg hR (referenceOracle A ω) seed t)
    (show 0 ≤ if ω t then A else 0 by split_ifs <;> positivity)
  linarith

lemma reference_no_arrival {S : Type*} (R : Rule S) (A : ℝ) (ω : ℕ → Bool)
    (seed : S) (t : ℕ) (ht : ω t = false) :
    position R (referenceOracle A ω) seed (t+1) =
      position R (referenceOracle A ω) seed t := by simp [reference_step, ht]

/-- While the reference run stays at most `y - μ`, the run on the instance coincides
with it. -/
theorem flat_coupling {S : Type*} (R : Rule S) (μ y A : ℝ)
    (ω : ℕ → Bool) (seed : S) (T : ℕ)
    (hflat : ∀ t < T, position R (referenceOracle A ω) seed t ≤ y-μ) :
    ∀ t ≤ T, position R (actualOracle μ y A ω) seed t =
      position R (referenceOracle A ω) seed t := by
  have hh := MomentumRun.coupled_trajectory (asMomentum R)
    (actualOracle μ y A ω) (referenceOracle A ω) seed T (by
      intro t ht
      exact sample_flat_gradient μ y _ _ (hflat t ht))
  intro t ht
  exact congrArg Prod.fst (hh t ht)

/-- If the reference run jumps from at most `z` to above `z + μ + √(2b)`, the run on the
instance with minimizer `z + μ` has gap greater than `b` after that step. -/
theorem overshoot_failure {S : Type*} {R : Rule S} (hR : Nonnegative R)
    {μ A b z : ℝ} (hμ : 0 ≤ μ) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (ω : ℕ → Bool) (seed : S) (t : ℕ)
    (hbefore : position R (referenceOracle A ω) seed t ≤ z)
    (hafter : z+μ+Real.sqrt (2*b) < position R (referenceOracle A ω) seed (t+1)) :
    b < populationLoss μ (z+μ) (position R (actualOracle μ (z+μ) A ω) seed (t+1)) -
      populationLoss μ (z+μ) (z+μ) := by
  have hm := reference_monotone hR hA ω seed
  have hc := flat_coupling R μ (z+μ) A ω seed (t+1) (by
    intro j hj
    have hh := (hm (show j ≤ t by omega)).trans hbefore
    linarith) (t+1) le_rfl
  rw [hc, population_gap_quadratic μ (z+μ) _ hμ (by
    have := Real.sqrt_nonneg (2*b); linarith)]
  have hs := Real.sq_sqrt (show 0 ≤ 2*b by positivity)
  have hn := Real.sqrt_nonneg (2*b)
  have hx : Real.sqrt (2*b) < position R (referenceOracle A ω) seed (t+1)-(z+μ) := by
    linarith
  nlinarith

/-- If the reference run stays at most one half up to time `N`, the run on the endpoint
instance has gap greater than `b` at time `N`. -/
theorem endpoint_failure {S : Type*} {R : Rule S} (hR : Nonnegative R)
    {μ A b : ℝ} (hμ : 0 ≤ μ) (hμhalf : μ ≤ 1/2) (hA : 0 ≤ A)
    (hb : b < μ/4) (ω : ℕ → Bool) (seed : S) (N : ℕ)
    (hN : position R (referenceOracle A ω) seed N ≤ 1/2) :
    b < populationLoss μ 1 (position R (actualOracle μ 1 A ω) seed N) -
      populationLoss μ 1 1 := by
  have hm := reference_monotone hR hA ω seed
  have hc := flat_coupling R μ 1 A ω seed N (by
    intro j hj
    have hh := (hm (Nat.le_of_lt hj)).trans hN
    linarith) N le_rfl
  rw [hc]
  exact hb.trans_le (gap_before_half μ _ hμ hμhalf hN)

section Measurability
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

lemma asMomentum_measurable (R : Rule S) (hR : ∀ t, Measurable (R t)) (t : ℕ) :
    Measurable (asMomentum R t) := measurable_const.prodMk ((hR t).prodMk measurable_const)

lemma position_measurable (R : Rule S) (hR : ∀ t, Measurable (R t))
    (o : Ω → ℕ → ℝ → ℝ)
    (ho : ∀ t, Measurable (fun z : Ω × ℝ => o z.1 t z.2))
    (seed : Ω → S) (hs : Measurable seed) (t : ℕ) :
    Measurable (fun ω => position R (o ω) (seed ω) t) :=
  (MomentumRun.trajectory_measurable _ (asMomentum_measurable R hR) o ho seed hs t).fst

lemma actualOracle_measurable (μ y A : ℝ) (bits : Ω → ℕ → Bool)
    (hbits : Measurable bits) (t : ℕ) :
    Measurable (fun z : Ω × ℝ => actualOracle μ y A (bits z.1) t z.2) := by
  have hb : Measurable (fun z : Ω × ℝ => bits z.1 t) :=
    (measurable_pi_apply t).comp (hbits.comp measurable_fst)
  exact (((measurable_snd.sub_const y).add_const μ).max measurable_const).sub
    ((measurable_from_top (f := fun b : Bool => if b then A else 0)).comp hb)

lemma populationLoss_continuous (μ y : ℝ) : Continuous (populationLoss μ y) :=
  ((hinge_continuous.comp ((continuous_id.sub continuous_const).add continuous_const)).sub
    (continuous_const.mul continuous_id))

end Measurability
end ClippedSGD.AnytimeLower
