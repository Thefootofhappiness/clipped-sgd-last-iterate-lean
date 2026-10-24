import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter
open scoped BigOperators
namespace ClippedSGD.UpperConcentration
noncomputable section
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]

lemma exp_quadratic_bound (z : ℝ) (hz : |z| ≤ 1) : Real.exp z ≤ 1+z+z^2 := by
  have hh := (le_abs_self (Real.exp z-1-z)).trans (Real.abs_exp_sub_one_sub_id_le hz)
  linarith

/-- Ville's inequality on a finite horizon, by stopping the supermartingale at its first
crossing. -/
theorem ville_finite (𝓕 : Filtration ℕ m₀) (Z : ℕ → Ω → ℝ)
    (hZ : Supermartingale Z 𝓕 ν) (hpos : ∀ n ω, 0 ≤ Z n ω)
    (hinit : ∫ω, Z 0 ω ∂ν ≤ 1) (a : ℝ) (ha : 0 < a) (T : ℕ) :
    ν {ω | ∃ n ≤ T, a ≤ Z n ω} ≤ ENNReal.ofReal (1/a) := by
  let τ := hitting Z (Ici a) 0 T
  have hτ : IsStoppingTime 𝓕 τ := hitting_isStoppingTime hZ.adapted measurableSet_Ici
  have hτT : ∀ ω, τ ω ≤ T := hitting_le
  have hi : Integrable (stoppedValue Z τ) ν :=
    integrable_stoppedValue ℕ hτ hZ.integrable hτT
  have he := hZ.neg.expected_stoppedValue_mono (isStoppingTime_const 𝓕 0) hτ
    (fun ω => Nat.zero_le _) hτT
  have he' : ∫ω, stoppedValue Z τ ω ∂ν ≤ ∫ω, Z 0 ω ∂ν := by
    simpa only [stoppedValue_const, stoppedValue, Pi.neg_apply, integral_neg, neg_le_neg_iff] using he
  have hp : 0 ≤ᵐ[ν] (fun ω => (1/a)*stoppedValue Z τ ω) :=
    Eventually.of_forall (fun ω => mul_nonneg (one_div_pos.mpr ha).le (hpos _ _))
  have hm := (hi.const_mul (1/a)).measure_le_integral hp (s := {ω | ∃ n ≤ T, a ≤ Z n ω}) (by
    intro ω hω
    have hh : stoppedValue Z τ ω ∈ Ici a := stoppedValue_hitting_mem (by
      obtain ⟨n, hn, hzn⟩ := hω
      exact ⟨n, ⟨Nat.zero_le _, hn⟩, hzn⟩)
    change a ≤ stoppedValue Z τ ω at hh
    have hh' : 1 ≤ stoppedValue Z τ ω/a := (one_le_div ha).mpr hh
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul, mul_one] using hh')
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (he'.trans hinit) (one_div_pos.mpr ha).le
  simpa only [mul_one] using hh

lemma integrable_of_abs_bound (X : Ω → ℝ) (hX : Measurable X) (b : ℝ)
    (hb : ∀ᵐ ω ∂ν, |X ω| ≤ b) : Integrable X ν := by
  apply Integrable.mono' (integrable_const b) hX.aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using hb

lemma integrable_exp_of_abs_bound (X : Ω → ℝ) (hX : Measurable X) (b θ : ℝ) (hθ : 0 ≤ θ)
    (hb : ∀ᵐ ω ∂ν, |X ω| ≤ b) : Integrable (fun ω => Real.exp (θ*X ω)) ν := by
  apply Integrable.mono' (integrable_const (Real.exp (θ*b)))
    ((hX.const_mul θ).exp.aestronglyMeasurable)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) hθ)

/-- A conditional exponential-moment bound for a bounded increment with conditional mean
zero. -/
theorem conditional_mgf (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ m₀ _ X) (b v θ : ℝ)
    (hb0 : 0 ≤ b) (hθ : 0 ≤ θ) (hθb : θ*b ≤ 1)
    (hb : ∀ᵐ ω ∂ν, |X ω| ≤ b)
    (hmean : ν[X|m] =ᵐ[ν] 0)
    (hsecond : ν[fun ω => (X ω)^2|m] ≤ᵐ[ν] fun _ => v) :
    ν[fun ω => Real.exp (θ*X ω)|m] ≤ᵐ[ν] fun _ => Real.exp (θ^2*v) := by
  letI : MeasurableSpace Ω := m₀
  have hi := integrable_of_abs_bound ν X hX b hb
  have hi2 : Integrable (fun ω => (X ω)^2) ν := by
    apply integrable_of_abs_bound ν _ (hX.pow_const 2) (b^2)
    filter_upwards [hb] with ω hω
    have hh := (sq_le_sq₀ (abs_nonneg _) hb0).mpr hω
    simpa only [sq_abs, abs_of_nonneg (sq_nonneg (X ω))] using hh
  have he := integrable_exp_of_abs_bound ν X hX b θ hθ hb
  have hip := ((integrable_const (1 : ℝ)).add (hi.const_mul θ)).add (hi2.const_mul (θ^2))
  have hbound : (fun ω => Real.exp (θ*X ω)) ≤ᵐ[ν] fun ω => 1+θ*X ω+θ^2*(X ω)^2 := by
    filter_upwards [hb] with ω hω
    have habs : |θ*X ω| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hθ]
      exact (mul_le_mul_of_nonneg_left hω hθ).trans hθb
    simpa only [mul_pow] using exp_quadratic_bound (θ*X ω) habs
  have hmono := condExp_mono (m := m) he hip hbound
  change ν[fun ω => Real.exp (θ*X ω)|m] ≤ᵐ[ν] ν[fun ω => 1+θ*X ω+θ^2*(X ω)^2|m] at hmono
  have hadd := condExp_add ((integrable_const (1 : ℝ)).add (hi.const_mul θ)) (hi2.const_mul (θ^2)) m
  have hadd1 := condExp_add (integrable_const (1 : ℝ)) (hi.const_mul θ) m
  have hscale := condExp_smul θ X m (μ := ν)
  have hscale2 := condExp_smul (θ^2) (fun ω => (X ω)^2) m (μ := ν)
  change ν[fun ω => 1+θ*X ω+θ^2*(X ω)^2|m] =ᵐ[ν]
    fun ω => ν[fun ω => 1+θ*X ω|m] ω+ν[fun ω => θ^2*(X ω)^2|m] ω at hadd
  change ν[fun ω => 1+θ*X ω|m] =ᵐ[ν]
    fun ω => ν[fun _ => (1 : ℝ)|m] ω+ν[fun ω => θ*X ω|m] ω at hadd1
  change ν[fun ω => θ*X ω|m] =ᵐ[ν] fun ω => θ*ν[X|m] ω at hscale
  change ν[fun ω => θ^2*(X ω)^2|m] =ᵐ[ν] fun ω => θ^2*ν[fun ω => (X ω)^2|m] ω at hscale2
  rw [condExp_const hm (1 : ℝ)] at hadd1
  filter_upwards [hmono, hadd, hadd1, hscale, hscale2, hmean, hsecond] with ω hmo ha ha1 hs hs2 hm0 hv
  rw [ha, ha1, hs, hs2, hm0] at hmo
  simp only [Pi.zero_apply, mul_zero, add_zero] at hmo
  exact hmo.trans ((add_le_add_left (mul_le_mul_of_nonneg_left hv (sq_nonneg θ)) 1).trans
    (by simpa only [add_comm] using Real.add_one_le_exp (θ^2*v)))

def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑i∈Finset.range n, X (i+1) ω

def exponentialProcess (X : ℕ → Ω → ℝ) (θ v : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (θ*partialSum X n ω-θ^2*n*v)

lemma prefix_adapted (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X) :
    Adapted 𝓕 (partialSum X) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    change StronglyMeasurable[𝓕 (n+1)] (fun ω => partialSum X (n+1) ω)
    simp only [partialSum, Finset.sum_range_succ]
    exact (ih.mono (𝓕.mono (by omega))).add (hX (n+1))

lemma prefix_abs_bound (X : ℕ → Ω → ℝ) (b : ℝ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i+1) ω| ≤ b) (n : ℕ) :
    ∀ᵐ ω ∂ν, |partialSum X n ω| ≤ n*b := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    filter_upwards [ih, hb n] with ω hn hi
    simp only [partialSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    have hh := (abs_add_le (partialSum X n ω) (X (n+1) ω)).trans (add_le_add hn hi)
    dsimp [partialSum] at hh
    nlinarith only [hh]

lemma exponentialProcess_integrable (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v θ : ℝ) (hv : 0 ≤ v) (hθ : 0 ≤ θ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i+1) ω| ≤ b) (n : ℕ) :
    Integrable (exponentialProcess X θ v n) ν := by
  have hm : Measurable (exponentialProcess X θ v n) :=
    (((((prefix_adapted 𝓕 X hX n).mono (𝓕.le n)).measurable.const_mul θ).sub_const _).exp)
  apply Integrable.mono' (integrable_const (Real.exp (θ*(n*b)))) hm.aestronglyMeasurable
  filter_upwards [prefix_abs_bound ν X b hb n] with ω hω
  simp only [exponentialProcess, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) hθ
  have hs : 0 ≤ θ^2*n*v := by positivity
  linarith

/-- The exponential supermartingale of the increments. -/
theorem exponential_supermartingale_from_mgf (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v θ : ℝ) (hv : 0 ≤ v) (hθ : 0 ≤ θ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i+1) ω| ≤ b)
    (hmgf : ∀ i, ν[fun ω => Real.exp (θ*X (i+1) ω)|𝓕 i] ≤ᵐ[ν] fun _ => Real.exp (θ^2*v)) :
    Supermartingale (exponentialProcess X θ v) 𝓕 ν := by
  have had : Adapted 𝓕 (exponentialProcess X θ v) := by
    intro n
    exact Real.continuous_exp.comp_stronglyMeasurable
      (((prefix_adapted 𝓕 X hX n).const_mul θ).sub stronglyMeasurable_const)
  have hint := exponentialProcess_integrable ν 𝓕 X hX b v θ hv hθ hb
  apply supermartingale_nat had hint
  intro n
  let A : Ω → ℝ := fun ω => exponentialProcess X θ v n ω*Real.exp (-θ^2*v)
  let Y : Ω → ℝ := fun ω => Real.exp (θ*X (n+1) ω)
  have heq : exponentialProcess X θ v (n+1)=A*Y := by
    funext ω
    simp only [exponentialProcess, partialSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one,
      Pi.mul_apply, A, Y, ← Real.exp_add]
    congr 1
    ring
  have hA : StronglyMeasurable[𝓕 n] A := (had n).mul stronglyMeasurable_const
  have hXY : Integrable (A*Y) ν := heq ▸ hint (n+1)
  have hraw : Measurable (X (n+1)) := ((hX (n+1)).mono (𝓕.le (n+1))).measurable
  have hYi : Integrable Y ν := integrable_exp_of_abs_bound ν _ hraw b θ hθ (hb n)
  have hc := condExp_mul_of_stronglyMeasurable_left (μ := ν) hA hXY hYi
  rw [heq]
  have hm := hmgf n
  filter_upwards [hc, hm] with ω hcω hmω
  change ν[A*Y|𝓕 n] ω ≤ _
  rw [hcω]
  change A ω*ν[Y|𝓕 n] ω ≤ _
  have hA0 : 0 ≤ A ω := by dsimp [A, exponentialProcess]; positivity
  have hh := mul_le_mul_of_nonneg_left hmω hA0
  change A ω*ν[Y|𝓕 n] ω ≤ A ω*Real.exp (θ^2*v) at hh
  have he : A ω*Real.exp (θ^2*v)=exponentialProcess X θ v n ω := by
    dsimp [A]
    rw [mul_assoc, ← Real.exp_add]
    simp
  exact hh.trans_eq he

/-- A finite maximal exponential tail, before optimizing its deterministic θ. -/
theorem maximal_exponential_from_mgf (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v θ ℓ : ℝ) (hv : 0 ≤ v) (hθ : 0 < θ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i+1) ω| ≤ b)
    (hmgf : ∀ i, ν[fun ω => Real.exp (θ*X (i+1) ω)|𝓕 i] ≤ᵐ[ν] fun _ => Real.exp (θ^2*v)) (T : ℕ) :
    ν {ω | ∃ n ≤ T, θ*T*v+ℓ/θ < partialSum X n ω} ≤ ENNReal.ofReal (Real.exp (-ℓ)) := by
  have hsup := exponential_supermartingale_from_mgf ν 𝓕 X hX b v θ hv hθ.le hb hmgf
  have hville := ville_finite ν 𝓕 (exponentialProcess X θ v) hsup
    (fun n ω => (Real.exp_pos _).le) (by simp [exponentialProcess, partialSum])
    (Real.exp ℓ) (Real.exp_pos _) T
  have hsub : {ω | ∃ n ≤ T, θ*T*v+ℓ/θ < partialSum X n ω} ⊆
      {ω | ∃ n ≤ T, Real.exp ℓ ≤ exponentialProcess X θ v n ω} := by
    intro ω hω
    obtain ⟨n, hn, hh⟩ := hω
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have hnt : (n : ℝ) ≤ T := by exact_mod_cast hn
    have hnv := mul_le_mul_of_nonneg_right hnt (show 0 ≤ θ^2*v by positivity)
    have hm := mul_lt_mul_of_pos_left hh hθ
    have hid : θ*(ℓ/θ)=ℓ := by field_simp
    nlinarith only [hm, hnv, hid]
  apply (measure_mono hsub).trans
  simpa only [one_div, Real.exp_neg] using hville

theorem maximal_exponential (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v θ ℓ : ℝ) (hb0 : 0 ≤ b) (hv : 0 ≤ v) (hθ : 0 < θ)
    (hθb : θ*b ≤ 1) (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i+1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i+1)|𝓕 i] =ᵐ[ν] 0)
    (hsecond : ∀ i, ν[fun ω => (X (i+1) ω)^2|𝓕 i] ≤ᵐ[ν] fun _ => v) (T : ℕ) :
    ν {ω | ∃ n ≤ T, θ*T*v+ℓ/θ < partialSum X n ω} ≤ ENNReal.ofReal (Real.exp (-ℓ)) := by
  apply maximal_exponential_from_mgf ν 𝓕 X hX b v θ ℓ hv hθ hb
  intro n
  exact conditional_mgf ν (𝓕 n) (𝓕.le n) (X (n+1))
    (((hX (n+1)).mono (𝓕.le (n+1))).measurable) b v θ hb0 hθ.le hθb
    (hb n) (hmean n) (hsecond n)

/-- A maximal Bernstein-type bound for bounded martingale increments, with `θ = 1/b`. -/
theorem bounded_martingale_maximal (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i+1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i+1)|𝓕 i] =ᵐ[ν] 0)
    (hsecond : ∀ i, ν[fun ω => (X (i+1) ω)^2|𝓕 i] ≤ᵐ[ν] fun _ => v) (T : ℕ) :
    ν {ω | ∃ n ≤ T, (T : ℝ)*v/b+b*ℓ < partialSum X n ω} ≤ ENNReal.ofReal (Real.exp (-ℓ)) := by
  have hh := maximal_exponential ν 𝓕 X hX b v (1/b) ℓ hb0.le hv (by positivity)
    (by field_simp) hb hmean hsecond T
  have he : (1/b)*T*v+ℓ/(1/b)=(T : ℝ)*v/b+b*ℓ := by
    field_simp
    <;> ring_nf
    <;> simp
  rwa [he] at hh

end
end ClippedSGD.UpperConcentration
