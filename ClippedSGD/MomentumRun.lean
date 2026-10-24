import ClippedSGD.MomentumOracle
import ClippedSGD.MomentumTail

/-! Heavy-ball runs of a controller, and the coupling of the run on the instance with
the reference run. -/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.MomentumRun
open MomentumGeometry MomentumProbability MomentumOracle
noncomputable section

abbrev Control := ℝ × (ℝ × ℝ)
def damping (c : Control) : ℝ := c.1
def gain (c : Control) : ℝ := c.2.1
def scale (c : Control) : ℝ := c.2.2

/-- A controller maps the gradient transcript, including the current gradient, and a
seed to the controls. -/
abbrev Rule (E S : Type*) := (t : ℕ) → ((Fin (t + 1) → E) × S) → Control
abbrev State (E : Type*) (t : ℕ) := E × (E × (Fin t → E))

section General
variable {E S : Type*} [AddCommGroup E] [Module ℝ E]

def trajectory (R : Rule E S) (oracle : ℕ → E → E) (seed : S) : (t : ℕ) → State E t
  | 0 => (0, 0, Fin.elim0)
  | t + 1 =>
    let q := trajectory R oracle seed t
    let g := oracle t q.1
    let hist := Fin.snoc q.2.2 g
    let ctrl := R t (hist, seed)
    let v := damping ctrl • q.2.1 + scale ctrl • g
    (q.1 - gain ctrl • v, v, hist)

def position (R : Rule E S) (oracle : ℕ → E → E) (seed : S) (t : ℕ) : E :=
  (trajectory R oracle seed t).1

def velocity (R : Rule E S) (oracle : ℕ → E → E) (seed : S) (t : ℕ) : E :=
  (trajectory R oracle seed t).2.1

def controls (R : Rule E S) (oracle : ℕ → E → E) (seed : S) (t : ℕ) : Control :=
  R t (Fin.snoc (trajectory R oracle seed t).2.2 (oracle t (position R oracle seed t)), seed)

lemma position_zero (R : Rule E S) (oracle : ℕ → E → E) (seed : S) :
    position R oracle seed 0 = 0 := rfl

lemma velocity_zero (R : Rule E S) (oracle : ℕ → E → E) (seed : S) :
    velocity R oracle seed 0 = 0 := rfl

lemma velocity_step (R : Rule E S) (oracle : ℕ → E → E) (seed : S) (t : ℕ) :
    velocity R oracle seed (t + 1) =
      damping (controls R oracle seed t) • velocity R oracle seed t +
      scale (controls R oracle seed t) • oracle t (position R oracle seed t) := rfl

lemma position_step (R : Rule E S) (oracle : ℕ → E → E) (seed : S) (t : ℕ) :
    position R oracle seed (t + 1) = position R oracle seed t -
      gain (controls R oracle seed t) • velocity R oracle seed (t + 1) := rfl

/-- Two oracles that agree along the run produce the same states and transcripts. -/
theorem coupled_trajectory (R : Rule E S) (legal reference : ℕ → E → E)
    (seed : S) (T : ℕ)
    (same : ∀ t < T, legal t (position R reference seed t) = reference t (position R reference seed t)) :
    ∀ t ≤ T, trajectory R legal seed t = trajectory R reference seed t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (by omega)
    have ho := same t (by omega)
    simp only [trajectory, he]
    change legal t (position R reference seed t) = reference t (position R reference seed t) at ho
    simp only [position] at ho
    rw [ho]

end General

variable {S : Type*}

def referenceOracle (A B : ℝ) (ω : ℕ → Sample d) (t : ℕ) (x : Space d) : Space d :=
  coordinateVector (Fin.cases (-(if (ω t).1 then A else 0))
    (fun j => x j.succ + pulse A B (ω t) j))

def legalOracle (μ A B : ℝ) (ω : ℕ → Sample d) (t : ℕ) : Space d → Space d :=
  grad μ A B (ω t)

lemma reference_first (A B : ℝ) (ω : ℕ → Sample d) (t : ℕ) (x : Space d) :
    referenceOracle A B ω t x 0 = -(if (ω t).1 then A else 0) := rfl

lemma reference_nuisance (A B : ℝ) (ω : ℕ → Sample d) (t : ℕ) (x : Space d) :
    nuisance (referenceOracle A B ω t x) = nuisance x + pulse A B (ω t) := by
  apply PiLp.ext
  intro j
  rfl

lemma nuisance_add (x y : Space d) : nuisance (x + y) = nuisance x + nuisance y := by
  apply PiLp.ext
  intro i
  rfl
lemma nuisance_sub (x y : Space d) : nuisance (x - y) = nuisance x - nuisance y := by
  apply PiLp.ext
  intro i
  rfl
lemma nuisance_smul (a : ℝ) (x : Space d) : nuisance (a • x) = a • nuisance x := by
  apply PiLp.ext
  intro i
  rfl
lemma nuisance_zero : nuisance (0 : Space d) = 0 := by
  apply PiLp.ext
  intro i
  rfl

theorem legal_reference_coupling (R : Rule (Space d) S) (μ A B : ℝ)
    (ω : ℕ → Sample d) (seed : S) (T : ℕ)
    (flat : ∀ t < T, position R (referenceOracle A B ω) seed t 0 ≤ 1 - μ) :
    ∀ t ≤ T, trajectory R (legalOracle μ A B ω) seed t =
      trajectory R (referenceOracle A B ω) seed t := by
  apply coupled_trajectory
  intro t ht
  exact flat_gradient μ (if (ω t).1 then A else 0) (pulse A B (ω t))
    (position R (referenceOracle A B ω) seed t) (flat t ht)

/-- If the run on the instance keeps its gap below `b` up to time `N`, the reference run
first exceeds one half in the first coordinate at some time `T ≤ N`. -/
theorem success_forces_crossing (R : Rule (Space d) S) (μ A B : ℝ)
    (ω : ℕ → Sample d) (seed : S) (N : ℕ) (hN : 0 < N)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1/2) (b : ℕ → ℝ)
    (hfinal : b N < μ / 4)
    (good : ∀ t, 0 < t → t ≤ N →
      populationLoss μ (position R (legalOracle μ A B ω) seed t) -
        populationLoss μ (target d) ≤ b t) :
    ∃ T, 0 < T ∧ T ≤ N ∧ 1/2 < position R (referenceOracle A B ω) seed T 0 ∧
      ∀ t < T, position R (referenceOracle A B ω) seed t 0 ≤ 1/2 := by
  have hex : ∃ T, T ≤ N ∧ 1/2 < position R (referenceOracle A B ω) seed T 0 := by
    by_contra! hn
    have he := legal_reference_coupling R μ A B ω seed N
      (fun t ht => (hn t (by omega)).trans (by linarith)) N le_rfl
    have hp : position R (legalOracle μ A B ω) seed N =
        position R (referenceOracle A B ω) seed N := congrArg Prod.fst he
    have hl := MomentumGeometry.gap_before_half μ hμ0 hμhalf
      (position R (legalOracle μ A B ω) seed N) (by rw [hp]; exact hn N le_rfl)
    linarith [good N hN le_rfl]
  let T := Nat.find hex
  have hs := Nat.find_spec hex
  refine ⟨T, ?_, hs.1, hs.2, ?_⟩
  · by_contra hn
    have he : T = 0 := by omega
    have hx : 1 / 2 < position R (referenceOracle A B ω) seed T 0 := hs.2
    rw [he, position_zero] at hx
    norm_num at hx
  · intro t ht
    have hn := Nat.find_min hex ht
    have htN : t ≤ N := by have := hs.1; omega
    exact le_of_not_gt (fun h => hn ⟨htN, h⟩)

/-- A gap of at most `b` bounds the nuisance component by `√(2b)`. -/
lemma nuisance_radius_of_gap (μ : ℝ) (hμ : 0 ≤ μ) (x : Space d) (b : ℝ)
    (hb : populationLoss μ x - populationLoss μ (target d) ≤ b) :
    ‖nuisance x‖ ≤ Real.sqrt (2 * b) := by
  have hn := nuisance_gap_lower μ hμ x
  have hb0 : 0 ≤ 2*b := by nlinarith [sq_nonneg ‖nuisance x‖]
  have hs := Real.sq_sqrt hb0
  have hs0 := Real.sqrt_nonneg (2*b)
  nlinarith [norm_nonneg (nuisance x)]

/-- A progress bound on a successful path without collisions or early rare pulses. -/
theorem pathwise_progress (R : Rule (Space d) S) (μ A B H : ℝ)
    (ω : ℕ → Sample d) (seed : S) (N n₀ : ℕ) (hN : 0 < N)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1/2) (hA : 0 ≤ A) (hB : 0 < B) (hBA : B ≤ A)
    (hH : 0 ≤ H) (b g : ℕ → ℝ) (w : ℕ → ℕ)
    (bmono : Antitone b) (hfinal : b N < μ / 4)
    (bound : ∀ t, let q := controls R (referenceOracle A B ω) seed t
      0 ≤ damping q ∧ damping q ≤ 1 ∧ 0 ≤ scale q ∧ scale q ≤ 1 ∧
        0 ≤ gain q ∧ (t < N → gain q ≤ H))
    (forget : ∀ j, n₀ ≤ j → j < N → ∀ i ∈ Finset.Ico (j + 1) (j + w j + 1),
      damping (controls R (referenceOracle A B ω) seed i) ≤ 1 - g j)
    (small : ∀ j, n₀ ≤ j → j < N →
      Real.sqrt (2 * b (j + 1)) * Real.sqrt (w j : ℝ) ≤ B / 2)
    (good : ∀ t, 0 < t → t ≤ N →
      populationLoss μ (position R (legalOracle μ A B ω) seed t) -
        populationLoss μ (target d) ≤ b t)
    (distinct : ∀ i < N, ∀ j < N, i ≠ j → (ω i).2.1 ≠ (ω j).2.1)
    (early : ∀ i < n₀, (ω i).1 = false) :
    1 / 2 < ∑ j ∈ Finset.range N, if (ω j).1 then
      2 * Real.sqrt (2 * b (j + 1)) + A * H * N * Real.exp (-(w j : ℝ) * g j) else 0 := by
  obtain ⟨T, hT0, hTN, hcross, hpre⟩ :=
    success_forces_crossing R μ A B ω seed N hN hμ0 hμhalf b hfinal good
  let ctrl := controls R (referenceOracle A B ω) seed
  let β := fun t => damping (ctrl t)
  let c := fun t => scale (ctrl t)
  let η := fun t => gain (ctrl t)
  let v := fun t => nuisance (velocity R (referenceOracle A B ω) seed t)
  let y := fun t => nuisance (position R (referenceOracle A B ω) seed t)
  let z := fun t => pulse A B (ω t)
  have hv0 : v 0 = 0 := nuisance_zero
  have hy0 : y 0 = 0 := nuisance_zero
  have hvstep : ∀ i < T, v (i+1) = β i • v i + c i • (y i + z i) := by
    intro i _
    dsimp [v, β, c, y, z, ctrl]
    rw [velocity_step, nuisance_add, nuisance_smul, nuisance_smul, reference_nuisance]
  have hystep : ∀ i < T, y (i+1) = y i - η i • v (i+1) := by
    intro i _
    dsimp [y, η, v, ctrl]
    rw [position_step, nuisance_sub, nuisance_smul]
  have hcouple := legal_reference_coupling R μ A B ω seed T
    (fun t ht => (hpre t ht).trans (by linarith))
  have pulsebound (j : ℕ) (hj : j < T) (hY : (ω j).1 = true) :
      A * Resolvent.kernel β c η T j ≤
        2 * Real.sqrt (2 * b (j+1)) + A * H * N * Real.exp (-(w j : ℝ) * g j) := by
    have hjn : n₀ ≤ j := by
      by_contra hn
      have := early j (by omega)
      simp_all
    have hjN : j < N := hj.trans_le hTN
    apply MomentumTail.pulse_response_bound β c η v y z N T j (w j) hj hTN hv0 hy0 hvstep hystep
      (fun i _ => (bound i).1) (fun i _ => (bound i).2.1)
      (fun i _ => (bound i).2.2.1) (bound j).2.2.2.1
      (fun i _ => (bound i).2.2.2.2.1)
      A B (Real.sqrt (2*b (j+1))) H (g j)
    · simp only [z, pulse_norm A B hA hB.le, amplitude, hY, ↓reduceIte]
    · exact hB
    · exact hH
    · intro i hi; exact (bound i).2.2.2.2.2 (hi.trans_le hTN)
    · exact forget j hjn hjN
    · intro i hi k hk hik
      exact pulse_orthogonal A B (ω i) (ω k) (distinct i (hi.trans_le hTN) k (hk.trans_le hTN) hik)
    · intro i _
      dsimp [z]
      rw [pulse_norm A B hA hB.le]
      cases (ω i).1 <;> simp [amplitude, hBA]
    · let e := min T (j + w j + 1)
      have heT : e ≤ T := min_le_left _ _
      have he0 : 0 < e := lt_min hT0 (by omega)
      have hje : j + 1 ≤ e := le_min (by omega) (by omega)
      have heN := heT.trans hTN
      have hpos : position R (legalOracle μ A B ω) seed e =
          position R (referenceOracle A B ω) seed e := congrArg Prod.fst (hcouple e heT)
      have hr := nuisance_radius_of_gap μ hμ0
        (position R (legalOracle μ A B ω) seed e) (b (j+1))
        ((good e he0 heN).trans (bmono hje))
      rw [hpos] at hr
      exact hr
    · exact small j hjn hjN
  have hx := MomentumTail.flat_displacement β c η
    (fun i => velocity R (referenceOracle A B ω) seed i 0)
    (fun i => position R (referenceOracle A B ω) seed i 0)
    (fun i => (ω i).1) A T rfl rfl
    (by
      intro i _
      dsimp only
      rw [velocity_step]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, reference_first]
      dsimp [β, c, ctrl]
      cases (ω i).1 <;> simp
      <;> ring)
    (by
      intro i _
      dsimp only
      rw [position_step]
      rfl)
  dsimp only at hx
  rw [hx] at hcross
  apply hcross.trans_le
  calc
    _ ≤ ∑ j ∈ Finset.range T, if (ω j).1 then
        2 * Real.sqrt (2*b (j+1)) + A * H * N * Real.exp (-(w j : ℝ)*g j) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      cases he : (ω j).1
      · simp
      · simpa using pulsebound j (Finset.mem_range.mp hj) he
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hTN)
      intro i _ _
      split_ifs <;> positivity

section Measurability
variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace S] [MeasurableSpace Ω]

lemma measurable_snoc {n : ℕ} (f : Ω → Fin n → E) (g : Ω → E)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => (Fin.snoc (f ω) (g ω) : Fin (n + 1) → E)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hg
  · simpa using (measurable_pi_iff.mp hf j)

/-- The trajectory is measurable when the controller and the oracle are. -/
theorem trajectory_measurable (R : Rule E S) (hR : ∀ t, Measurable (R t))
    (oracle : Ω → ℕ → E → E)
    (ho : ∀ t, Measurable (fun z : Ω × E => oracle z.1 t z.2))
    (seed : Ω → S) (hs : Measurable seed) :
    ∀ t, Measurable (fun ω => trajectory R (oracle ω) (seed ω) t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let state : Ω → State E t := fun ω => trajectory R (oracle ω) (seed ω) t
    let raw : Ω → E := fun ω => oracle ω t (state ω).1
    have hg : Measurable raw := (ho t).comp (measurable_id.prodMk ih.fst)
    have hh : Measurable (fun ω => (Fin.snoc (state ω).2.2 (raw ω) : Fin (t + 1) → E)) :=
      measurable_snoc _ _ ih.snd.snd hg
    have hc : Measurable (fun ω => R t (Fin.snoc (state ω).2.2 (raw ω), seed ω)) :=
      (hR t).comp (hh.prodMk hs)
    have hv : Measurable (fun ω =>
        damping (R t (Fin.snoc (state ω).2.2 (raw ω), seed ω)) • (state ω).2.1 +
        scale (R t (Fin.snoc (state ω).2.2 (raw ω), seed ω)) • raw ω) :=
      (hc.fst.smul ih.snd.fst).add (hc.snd.snd.smul hg)
    exact ((ih.fst.sub (hc.snd.fst.smul hv)).prodMk (hv.prodMk hh))

end Measurability

lemma grad_continuous (μ A B : ℝ) (a : Sample d) : Continuous (grad μ A B a) := by
  apply LipschitzWith.continuous (K := 1)
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  simpa using sampleGrad_lipschitz μ (if a.1 then A else 0) (pulse A B a) x y

lemma grad_joint_measurable (μ A B : ℝ) :
    Measurable (fun z : Sample d × Space d => grad μ A B z.1 z.2) := by
  have hm : Measurable (fun z : Space d × Sample d => grad μ A B z.2 z.1) :=
    measurable_from_prod_countable (fun a => (grad_continuous μ A B a).measurable)
  exact hm.comp measurable_swap

def prefixSamples {N d : ℕ} (ω : Fin N → Sample d) (t : ℕ) : Sample d :=
  if ht : t < N then ω ⟨t, ht⟩ else (false, (0, false))

lemma prefixSamples_at {N d : ℕ} (ω : Fin N → Sample d) (t : ℕ) (ht : t < N) :
    prefixSamples ω t = ω ⟨t, ht⟩ := by simp [prefixSamples, ht]

/-- Every iterate is a measurable function of the samples and the seed. -/
theorem legal_position_measurable [MeasurableSpace S] (R : Rule (Space d) S)
    (hR : ∀ t, Measurable (R t)) (μ A B : ℝ) (N t : ℕ) :
    Measurable (fun q : (Fin N → Sample d) × S =>
      position R (legalOracle μ A B (prefixSamples q.1)) q.2 t) := by
  apply Measurable.fst
  apply trajectory_measurable R hR _ _ _ measurable_snd t
  intro k
  have hp : Measurable (fun q : ((Fin N → Sample d) × S) × Space d => prefixSamples q.1.1 k) :=
    (show Measurable (fun ω : Fin N → Sample d => prefixSamples ω k) from .of_discrete).comp
      (measurable_fst.comp measurable_fst)
  exact (grad_joint_measurable μ A B).comp (hp.prodMk measurable_snd)

end
end ClippedSGD.MomentumRun
