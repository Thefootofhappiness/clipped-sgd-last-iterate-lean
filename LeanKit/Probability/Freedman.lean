import LeanKit.Probability.TimeUniform

/-!
# Freedman's Inequality with Predictable Quadratic Variation (`LeanKit.Probability.Freedman`)

Proves the predictable-quadratic-variation version of Freedman's inequality for bounded
martingale difference sequences on both finite horizons (`n ≤ T`) and infinite horizons (`n : ℕ`),
and derives the deterministic-variance maximal inequalities of `ClippedSGD.UpperConcentration`
as direct corollaries when the conditional step variances are bounded by a constant `v₀`.

Main declarations:
- `condStepVar`, `predictableQuadVar`: the predictable quadratic variation
  `V_n(ω) = ∑_{i < n} 𝔼[X_{i+1}^2 | 𝓕_i](ω)`.
- `conditional_mgf_predictable`: conditional exponential moment bound keeping the random
  conditional variance `𝔼[X^2 | m](ω)` inside the exponent.
- `freedmanProcess`, `freedmanProcess_supermartingale`: the exponential process
  `M_n(ω) = exp(θ S_n(ω) - θ^2 V_n(ω))` is a nonnegative supermartingale for `0 ≤ θ ≤ 1 / b`.
- `freedman_mgf_maximal_finite`, `freedman_mgf_maximal_infinite`: MGF maximal inequality
  jointly in `S_n ≥ ε` and `V_n ≤ v`.
- `freedman_finite`, `freedman_infinite`: Freedman tail bound
  `ℙ(∃ n, S_n ≥ ε ∧ V_n ≤ v) ≤ exp(-ε^2 / (4(v + b ε)))`.
- `freedman_quantile_finite`, `freedman_quantile_infinite`: sub-Gaussian + linear quantile bound
  `ℙ(∃ n, S_n ≥ 2√(vℓ) + 4bℓ ∧ V_n ≤ v) ≤ exp(-ℓ)`.
- `freedman_linear_quantile_finite`, `freedman_linear_quantile_infinite`: linear quantile bound
  `ℙ(∃ n, S_n ≥ v / b + 2bℓ ∧ V_n ≤ v) ≤ exp(-ℓ)`.
- `predictableQuadVar_le_of_step_bound`, `corollary_maximal_exponential`,
  `corollary_bounded_martingale_maximal`: self-check corollaries recovering `UpperConcentration.lean`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
open LeanKit.Probability.MartingaleConcentration
open LeanKit.Probability.TimeUniform

namespace LeanKit.Probability.Freedman
noncomputable section

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]

/-- Conditional step variance `𝔼[X_{i+1}^2 | 𝓕_i](ω)` at step `i`. -/
def condStepVar (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  ν[fun a => (X (i + 1) a) ^ 2 | 𝓕 i] ω

/-- Predictable quadratic variation `V_n(ω) = ∑_{i < n} 𝔼[X_{i+1}^2 | 𝓕_i](ω)`. -/
def predictableQuadVar (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, condStepVar ν 𝓕 X i ω

omit [IsProbabilityMeasure ν] in
lemma condStepVar_stronglyMeasurable (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (i : ℕ) :
    StronglyMeasurable[𝓕 i] (condStepVar ν 𝓕 X i) :=
  stronglyMeasurable_condExp (m := 𝓕 i)

omit [IsProbabilityMeasure ν] in
lemma condStepVar_nonneg_ae (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (i : ℕ) :
    ∀ᵐ ω ∂ν, 0 ≤ condStepVar ν 𝓕 X i ω :=
  condExp_nonneg (Eventually.of_forall fun a => sq_nonneg (X (i + 1) a))

omit [IsProbabilityMeasure ν] in
@[simp]
lemma predictableQuadVar_zero (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (ω : Ω) :
    predictableQuadVar ν 𝓕 X 0 ω = 0 := by
  simp [predictableQuadVar]

omit [IsProbabilityMeasure ν] in
lemma predictableQuadVar_succ (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    predictableQuadVar ν 𝓕 X (n + 1) ω =
      predictableQuadVar ν 𝓕 X n ω + condStepVar ν 𝓕 X n ω := by
  simp [predictableQuadVar, Finset.sum_range_succ]

omit [IsProbabilityMeasure ν] in
/-- `V_n` is adapted to `𝓕`. -/
lemma predictableQuadVar_adapted (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) :
    Adapted 𝓕 (predictableQuadVar ν 𝓕 X) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    change StronglyMeasurable[𝓕 (n + 1)] (fun ω => predictableQuadVar ν 𝓕 X (n + 1) ω)
    simp only [predictableQuadVar_succ]
    exact (ih.mono (𝓕.mono (by omega))).add
      ((condStepVar_stronglyMeasurable ν 𝓕 X n).mono (𝓕.mono (by omega)))

omit [IsProbabilityMeasure ν] in
/-- `V_{n+1}` is `𝓕_n`-measurable (predictable). -/
lemma predictableQuadVar_succ_stronglyMeasurable (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (n : ℕ) :
    StronglyMeasurable[𝓕 n] (predictableQuadVar ν 𝓕 X (n + 1)) := by
  have heq : predictableQuadVar ν 𝓕 X (n + 1) =
      fun ω => predictableQuadVar ν 𝓕 X n ω + condStepVar ν 𝓕 X n ω :=
    funext (predictableQuadVar_succ ν 𝓕 X n)
  rw [heq]
  exact (predictableQuadVar_adapted ν 𝓕 X n).add (condStepVar_stronglyMeasurable ν 𝓕 X n)

omit [IsProbabilityMeasure ν] in
lemma predictableQuadVar_nonneg_ae (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂ν, 0 ≤ predictableQuadVar ν 𝓕 X n ω := by
  induction n with
  | zero => exact Eventually.of_forall (fun _ => by simp)
  | succ n ih =>
    filter_upwards [ih, condStepVar_nonneg_ae ν 𝓕 X n] with ω h1 h2
    rw [predictableQuadVar_succ]
    exact add_nonneg h1 h2

/-- Conditional exponential moment bound keeping the random conditional second moment
`ν[fun a => (X a)^2 | m] ω` in the exponent. -/
theorem conditional_mgf_predictable (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (X : Ω → ℝ) (hX : @Measurable Ω ℝ m₀ _ X) (b θ : ℝ)
    (hb0 : 0 ≤ b) (hθ : 0 ≤ θ) (hθb : θ * b ≤ 1)
    (hb : ∀ᵐ ω ∂ν, |X ω| ≤ b)
    (hmean : ν[X | m] =ᵐ[ν] 0) :
    ν[fun ω => Real.exp (θ * X ω) | m] ≤ᵐ[ν]
      fun ω => Real.exp (θ ^ 2 * ν[fun a => (X a) ^ 2 | m] ω) := by
  letI : MeasurableSpace Ω := m₀
  have hi := integrable_of_abs_bound ν X hX b hb
  have hi2 : Integrable (fun ω => (X ω) ^ 2) ν := by
    apply integrable_of_abs_bound ν _ (hX.pow_const 2) (b ^ 2)
    filter_upwards [hb] with ω hω
    have hh := (sq_le_sq₀ (abs_nonneg _) hb0).mpr hω
    simpa only [sq_abs, abs_of_nonneg (sq_nonneg (X ω))] using hh
  have he := integrable_exp_of_abs_bound ν X hX b θ hθ hb
  have hip := ((integrable_const (1 : ℝ)).add (hi.const_mul θ)).add (hi2.const_mul (θ ^ 2))
  have hbound : (fun ω => Real.exp (θ * X ω)) ≤ᵐ[ν] fun ω => 1 + θ * X ω + θ ^ 2 * (X ω) ^ 2 := by
    filter_upwards [hb] with ω hω
    have habs : |θ * X ω| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hθ]
      exact (mul_le_mul_of_nonneg_left hω hθ).trans hθb
    simpa only [mul_pow] using exp_quadratic_bound (θ * X ω) habs
  have hmono := condExp_mono (m := m) he hip hbound
  change ν[fun ω => Real.exp (θ * X ω) | m] ≤ᵐ[ν]
    ν[fun ω => 1 + θ * X ω + θ ^ 2 * (X ω) ^ 2 | m] at hmono
  have hadd := condExp_add ((integrable_const (1 : ℝ)).add (hi.const_mul θ)) (hi2.const_mul (θ ^ 2)) m
  have hadd1 := condExp_add (integrable_const (1 : ℝ)) (hi.const_mul θ) m
  have hscale := condExp_smul θ X m (μ := ν)
  have hscale2 := condExp_smul (θ ^ 2) (fun ω => (X ω) ^ 2) m (μ := ν)
  change ν[fun ω => 1 + θ * X ω + θ ^ 2 * (X ω) ^ 2 | m] =ᵐ[ν]
    fun ω => ν[fun ω => 1 + θ * X ω | m] ω + ν[fun ω => θ ^ 2 * (X ω) ^ 2 | m] ω at hadd
  change ν[fun ω => 1 + θ * X ω | m] =ᵐ[ν]
    fun ω => ν[fun _ => (1 : ℝ) | m] ω + ν[fun ω => θ * X ω | m] ω at hadd1
  change ν[fun ω => θ * X ω | m] =ᵐ[ν] fun ω => θ * ν[X | m] ω at hscale
  change ν[fun ω => θ ^ 2 * (X ω) ^ 2 | m] =ᵐ[ν]
    fun ω => θ ^ 2 * ν[fun a => (X a) ^ 2 | m] ω at hscale2
  rw [condExp_const hm (1 : ℝ)] at hadd1
  filter_upwards [hmono, hadd, hadd1, hscale, hscale2, hmean] with ω hmo ha ha1 hs hs2 hm0
  rw [ha, ha1, hs, hs2, hm0] at hmo
  simp only [Pi.zero_apply, mul_zero, add_zero] at hmo
  exact hmo.trans (by simpa only [add_comm] using
    Real.add_one_le_exp (θ ^ 2 * ν[fun a => (X a) ^ 2 | m] ω))

/-- The Freedman exponential process `M_n(ω) = exp(θ S_n(ω) - θ^2 V_n(ω))`. -/
def freedmanProcess (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (θ * partialSum X n ω - θ ^ 2 * predictableQuadVar ν 𝓕 X n ω)

omit [IsProbabilityMeasure ν] in
lemma freedmanProcess_adapted (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X) (θ : ℝ) :
    Adapted 𝓕 (freedmanProcess ν 𝓕 X θ) := by
  intro n
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((prefix_adapted 𝓕 X hX n).const_mul θ).sub
      ((predictableQuadVar_adapted ν 𝓕 X n).const_mul (θ ^ 2)))

omit [IsProbabilityMeasure ν] in
lemma freedmanProcess_nonneg (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ freedmanProcess ν 𝓕 X θ n ω :=
  (Real.exp_pos _).le

omit [IsProbabilityMeasure ν] in
@[simp]
lemma freedmanProcess_zero (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (θ : ℝ) (ω : Ω) :
    freedmanProcess ν 𝓕 X θ 0 ω = 1 := by
  simp [freedmanProcess, partialSum]

lemma freedmanProcess_integrable (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b θ : ℝ) (hθ : 0 ≤ θ) (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b) (n : ℕ) :
    Integrable (freedmanProcess ν 𝓕 X θ n) ν := by
  letI : MeasurableSpace Ω := m₀
  have hm : StronglyMeasurable (freedmanProcess ν 𝓕 X θ n) :=
    (freedmanProcess_adapted ν 𝓕 X hX θ n).mono (𝓕.le n)
  apply Integrable.mono' (integrable_const (Real.exp (θ * (n * b)))) hm.aestronglyMeasurable
  filter_upwards [prefix_abs_bound ν X b hb n, predictableQuadVar_nonneg_ae ν 𝓕 X n] with ω hS hV
  dsimp [freedmanProcess]
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 : θ * partialSum X n ω ≤ θ * (n * b) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hS) hθ
  have h2 : 0 ≤ θ ^ 2 * predictableQuadVar ν 𝓕 X n ω := mul_nonneg (sq_nonneg θ) hV
  linarith

/-- The Freedman exponential process `exp(θ S_n - θ^2 V_n)` is a supermartingale for `0 ≤ θ ≤ 1 / b`. -/
theorem freedmanProcess_supermartingale (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b θ : ℝ) (hb0 : 0 ≤ b) (hθ : 0 ≤ θ) (hθb : θ * b ≤ 1)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) :
    Supermartingale (freedmanProcess ν 𝓕 X θ) 𝓕 ν := by
  letI : MeasurableSpace Ω := m₀
  have had : Adapted 𝓕 (freedmanProcess ν 𝓕 X θ) := freedmanProcess_adapted ν 𝓕 X hX θ
  have hint : ∀ n, Integrable (freedmanProcess ν 𝓕 X θ n) ν :=
    freedmanProcess_integrable ν 𝓕 X hX b θ hθ hb
  refine supermartingale_nat (f := freedmanProcess ν 𝓕 X θ) (𝒢 := 𝓕) (μ := ν) had hint ?_
  intro n
  let A : Ω → ℝ := fun ω =>
    Real.exp (θ * partialSum X n ω - θ ^ 2 * predictableQuadVar ν 𝓕 X (n + 1) ω)
  let Y : Ω → ℝ := fun ω => Real.exp (θ * X (n + 1) ω)
  have hAm : StronglyMeasurable[𝓕 n] A :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((prefix_adapted 𝓕 X hX n).const_mul θ).sub
        ((predictableQuadVar_succ_stronglyMeasurable ν 𝓕 X n).const_mul (θ ^ 2)))
  have hXn : @Measurable Ω ℝ m₀ _ (X (n + 1)) :=
    ((hX (n + 1)).mono (𝓕.le (n + 1))).measurable
  have hYi : Integrable Y ν := integrable_exp_of_abs_bound ν (X (n + 1)) hXn b θ hθ (hb n)
  have hsplit : freedmanProcess ν 𝓕 X θ (n + 1) = fun ω => A ω * Y ω := by
    funext ω
    dsimp [freedmanProcess, A, Y]
    rw [← Real.exp_add]
    congr 1
    simp [partialSum, Finset.sum_range_succ]
    ring
  have hAYi : Integrable (fun ω => A ω * Y ω) ν := by
    rw [← hsplit]
    exact hint (n + 1)
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 n) (μ := ν) hAm hAYi hYi
  have hmgf := conditional_mgf_predictable ν (𝓕 n) (𝓕.le n) (X (n + 1)) hXn
    b θ hb0 hθ hθb (hb n) (hmean n)
  rw [hsplit]
  filter_upwards [hpull, hmgf] with ω hp hm
  change ν[A * Y | 𝓕 n] ω ≤ _
  rw [hp]
  dsimp [Pi.mul_apply]
  have hApos : 0 ≤ A ω := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hm hApos
  have hcollapse : A ω * Real.exp (θ ^ 2 * condStepVar ν 𝓕 X n ω) =
      freedmanProcess ν 𝓕 X θ n ω := by
    dsimp [A, freedmanProcess]
    rw [← Real.exp_add, predictableQuadVar_succ]
    congr 1
    ring
  exact hmul.trans_eq hcollapse

/-- Finite-horizon Freedman MGF maximal inequality: for `0 ≤ θ ≤ 1 / b`,
`ℙ(∃ n ≤ T, S_n ≥ ε ∧ V_n ≤ v) ≤ exp(θ^2 v - θ ε)`. -/
theorem freedman_mgf_maximal_finite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b θ ε v : ℝ) (hb0 : 0 ≤ b) (hθ : 0 ≤ θ) (hθb : θ * b ≤ 1)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) (T : ℕ) :
    ν {ω | ∃ n ≤ T, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (θ ^ 2 * v - θ * ε)) := by
  have hsm := freedmanProcess_supermartingale ν 𝓕 X hX b θ hb0 hθ hθb hb hmean
  have hinit : ∫ ω, freedmanProcess ν 𝓕 X θ 0 ω ∂ν ≤ 1 := by simp [freedmanProcess_zero]
  have hville := ville_finite ν 𝓕 (freedmanProcess ν 𝓕 X θ) hsm
    (freedmanProcess_nonneg ν 𝓕 X θ) hinit
    (Real.exp (θ * ε - θ ^ 2 * v)) (Real.exp_pos _) T
  have hsub : {ω | ∃ n ≤ T, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v} ⊆
      {ω | ∃ n ≤ T, Real.exp (θ * ε - θ ^ 2 * v) ≤ freedmanProcess ν 𝓕 X θ n ω} := by
    rintro ω ⟨n, hn, hS, hV⟩
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have h1 : θ * ε ≤ θ * partialSum X n ω := mul_le_mul_of_nonneg_left hS hθ
    have h2 : θ ^ 2 * predictableQuadVar ν 𝓕 X n ω ≤ θ ^ 2 * v :=
      mul_le_mul_of_nonneg_left hV (sq_nonneg θ)
    linarith
  refine (measure_mono hsub).trans (hville.trans_eq ?_)
  congr 1
  rw [one_div, ← Real.exp_neg]
  congr 1
  ring

/-- Infinite-horizon Freedman MGF maximal inequality: for `0 ≤ θ ≤ 1 / b`,
`ℙ(∃ n : ℕ, S_n ≥ ε ∧ V_n ≤ v) ≤ exp(θ^2 v - θ ε)`. -/
theorem freedman_mgf_maximal_infinite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b θ ε v : ℝ) (hb0 : 0 ≤ b) (hθ : 0 ≤ θ) (hθb : θ * b ≤ 1)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) :
    ν {ω | ∃ n : ℕ, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (θ ^ 2 * v - θ * ε)) := by
  let E : ℕ → Set Ω := fun T =>
    {ω | ∃ n ≤ T, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v}
  have hmono : Monotone E := by
    intro T₁ T₂ hT ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hT, h⟩
  have hunion : {ω | ∃ n : ℕ, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v} =
      ⋃ T : ℕ, E T := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, E]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  rw [hunion]
  exact measure_iUnion_le_of_monotone ν hmono
    (fun T => freedman_mgf_maximal_finite ν 𝓕 X hX b θ ε v hb0 hθ hθb hb hmean T)

/-- Algebraic exponent bound at `θ = ε / (2(v + b ε))`. -/
lemma freedman_exponent_bound (b ε v : ℝ) (hb : 0 < b) (hε : 0 ≤ ε) (hv : 0 ≤ v) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ * b ≤ 1 ∧
      θ ^ 2 * v - θ * ε ≤ -ε ^ 2 / (4 * (v + b * ε)) := by
  by_cases hε0 : ε = 0
  · refine ⟨0, le_rfl, by simp, ?_⟩
    simp [hε0]
  · have hε_pos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
    have hden : 0 < v + b * ε := by positivity
    let θ := ε / (2 * (v + b * ε))
    refine ⟨θ, by positivity, ?_, ?_⟩
    · dsimp [θ]
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      linarith
    · dsimp [θ]
      have hdiff : (ε / (2 * (v + b * ε))) ^ 2 * v - ε / (2 * (v + b * ε)) * ε -
          (-ε ^ 2 / (4 * (v + b * ε))) =
          -(b * ε ^ 3) / (4 * (v + b * ε) ^ 2) := by
        field_simp
        ring
      have hnonpos : -(b * ε ^ 3) / (4 * (v + b * ε) ^ 2) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
      linarith

/-- Finite-horizon Freedman inequality with predictable quadratic variation:
`ℙ(∃ n ≤ T, S_n ≥ ε ∧ V_n ≤ v) ≤ exp(-ε^2 / (4(v + b ε)))`. -/
theorem freedman_finite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b ε v : ℝ) (hb0 : 0 < b) (hε : 0 ≤ ε) (hv : 0 ≤ v)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) (T : ℕ) :
    ν {ω | ∃ n ≤ T, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (4 * (v + b * ε)))) := by
  obtain ⟨θ, hθ0, hθb, hexp⟩ := freedman_exponent_bound b ε v hb0 hε hv
  refine (freedman_mgf_maximal_finite ν 𝓕 X hX b θ ε v hb0.le hθ0 hθb hb hmean T).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)

/-- Infinite-horizon Freedman inequality with predictable quadratic variation:
`ℙ(∃ n : ℕ, S_n ≥ ε ∧ V_n ≤ v) ≤ exp(-ε^2 / (4(v + b ε)))`. -/
theorem freedman_infinite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b ε v : ℝ) (hb0 : 0 < b) (hε : 0 ≤ ε) (hv : 0 ≤ v)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) :
    ν {ω | ∃ n : ℕ, ε ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (-ε ^ 2 / (4 * (v + b * ε)))) := by
  obtain ⟨θ, hθ0, hθb, hexp⟩ := freedman_exponent_bound b ε v hb0 hε hv
  refine (freedman_mgf_maximal_infinite ν 𝓕 X hX b θ ε v hb0.le hθ0 hθb hb hmean).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)

/-- Sharp sub-Gaussian + linear quantile exponent choice:
for `b > 0`, `v ≥ 0`, `ℓ > 0`, setting `θ = min(1 / b, √(ℓ / v))` satisfies `0 ≤ θ ≤ 1 / b` and
`θ^2 v - θ (2√(vℓ) + 2bℓ) ≤ -ℓ`. -/
lemma freedman_quantile_exponent (b v ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v) (hℓ : 0 < ℓ) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ * b ≤ 1 ∧
      θ ^ 2 * v - θ * (2 * Real.sqrt (v * ℓ) + 2 * b * ℓ) ≤ -ℓ := by
  by_cases hcase : b ^ 2 * ℓ ≤ v
  · have hvpos : 0 < v := lt_of_lt_of_le (by positivity) hcase
    have hsqrtv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
    let θ := Real.sqrt ℓ / Real.sqrt v
    refine ⟨θ, by positivity, ?_, ?_⟩
    · dsimp [θ]
      rw [div_mul_eq_mul_div, div_le_one hsqrtv]
      have hsq : (Real.sqrt ℓ * b) ^ 2 ≤ v := by
        rw [mul_pow, Real.sq_sqrt hℓ.le]
        linarith
      exact (Real.le_sqrt (by positivity) hv).mpr hsq
    · dsimp [θ]
      have hsqℓ : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
      have hsqv : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
      have h1 : (Real.sqrt ℓ / Real.sqrt v) ^ 2 * v = ℓ := by
        rw [div_pow, hsqℓ, hsqv, div_mul_cancel₀ _ hvpos.ne']
      have h2 : Real.sqrt ℓ / Real.sqrt v * (2 * Real.sqrt (v * ℓ)) = 2 * ℓ := by
        rw [Real.sqrt_mul hv]
        calc
          Real.sqrt ℓ / Real.sqrt v * (2 * (Real.sqrt v * Real.sqrt ℓ)) =
              2 * (Real.sqrt ℓ / Real.sqrt v * Real.sqrt v) * Real.sqrt ℓ := by ring
          _ = 2 * Real.sqrt ℓ * Real.sqrt ℓ := by rw [div_mul_cancel₀ _ hsqrtv.ne']
          _ = 2 * (Real.sqrt ℓ ^ 2) := by ring
          _ = 2 * ℓ := by rw [hsqℓ]
      have h3 : 0 ≤ Real.sqrt ℓ / Real.sqrt v * (2 * b * ℓ) := by positivity
      linarith
  · push_neg at hcase
    let θ := 1 / b
    refine ⟨θ, by positivity, ?_, ?_⟩
    · dsimp [θ]
      exact div_mul_cancel₀ 1 hb0.ne' |>.le
    · dsimp [θ]
      have h1 : (1 / b) ^ 2 * v ≤ ℓ := by
        rw [div_pow, one_pow, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith
      have h2 : 1 / b * (2 * b * ℓ) = 2 * ℓ := by field_simp; ring
      have h3 : 0 ≤ 1 / b * (2 * Real.sqrt (v * ℓ)) := by positivity
      linarith

/-- Sub-Gaussian + linear quantile bound on a finite horizon:
`ℙ(∃ n ≤ T, S_n ≥ 2√(vℓ) + 2bℓ ∧ V_n ≤ v) ≤ exp(-ℓ)`. -/
theorem freedman_quantile_finite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b v ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) (T : ℕ) :
    ν {ω | ∃ n ≤ T, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ ≤ partialSum X n ω ∧
        predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  obtain ⟨θ, hθ0, hθb, hexp⟩ := freedman_quantile_exponent b v ℓ hb0 hv hℓ
  refine (freedman_mgf_maximal_finite ν 𝓕 X hX b θ (2 * Real.sqrt (v * ℓ) + 2 * b * ℓ) v
    hb0.le hθ0 hθb hb hmean T).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)

/-- Sub-Gaussian + linear quantile bound on an infinite horizon:
`ℙ(∃ n : ℕ, S_n ≥ 2√(vℓ) + 2bℓ ∧ V_n ≤ v) ≤ exp(-ℓ)`. -/
theorem freedman_quantile_infinite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b v ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) :
    ν {ω | ∃ n : ℕ, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ ≤ partialSum X n ω ∧
        predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  obtain ⟨θ, hθ0, hθb, hexp⟩ := freedman_quantile_exponent b v ℓ hb0 hv hℓ
  refine (freedman_mgf_maximal_infinite ν 𝓕 X hX b θ (2 * Real.sqrt (v * ℓ) + 2 * b * ℓ) v
    hb0.le hθ0 hθb hb hmean).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)

/-- Linear quantile bound on a finite horizon with predictable quadratic variation:
`ℙ(∃ n ≤ T, S_n ≥ v / b + bℓ ∧ V_n ≤ v) ≤ exp(-ℓ)`. -/
theorem freedman_linear_quantile_finite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b v ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) (T : ℕ) :
    ν {ω | ∃ n ≤ T, v / b + b * ℓ ≤ partialSum X n ω ∧
        predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  let _ := hv
  let _ := hℓ
  have hθ0 : 0 ≤ 1 / b := (one_div_pos.mpr hb0).le
  have hθb : (1 / b) * b ≤ 1 := (one_div_mul_cancel hb0.ne').le
  refine (freedman_mgf_maximal_finite ν 𝓕 X hX b (1 / b) (v / b + b * ℓ) v
    hb0.le hθ0 hθb hb hmean T).trans_eq ?_
  congr 1
  congr 1
  field_simp
  ring

/-- Linear quantile bound on an infinite horizon with predictable quadratic variation:
`ℙ(∃ n : ℕ, S_n ≥ v / b + bℓ ∧ V_n ≤ v) ≤ exp(-ℓ)`. -/
theorem freedman_linear_quantile_infinite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b v ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0) :
    ν {ω | ∃ n : ℕ, v / b + b * ℓ ≤ partialSum X n ω ∧
        predictableQuadVar ν 𝓕 X n ω ≤ v} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  let E : ℕ → Set Ω := fun T =>
    {ω | ∃ n ≤ T, v / b + b * ℓ ≤ partialSum X n ω ∧ predictableQuadVar ν 𝓕 X n ω ≤ v}
  have hmono : Monotone E := by
    intro T₁ T₂ hT ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hT, h⟩
  have hunion : {ω | ∃ n : ℕ, v / b + b * ℓ ≤ partialSum X n ω ∧
      predictableQuadVar ν 𝓕 X n ω ≤ v} = ⋃ T : ℕ, E T := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, E]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  rw [hunion]
  exact measure_iUnion_le_of_monotone ν hmono
    (fun T => freedman_linear_quantile_finite ν 𝓕 X hX b v ℓ hb0 hv hℓ hb hmean T)

section SelfCheckCorollaries

omit [IsProbabilityMeasure ν] in
/-- When every step conditional second moment is a.e. bounded by `v₀`,
the predictable quadratic variation satisfies `V_n ≤ n * v₀` almost everywhere. -/
lemma predictableQuadVar_le_of_step_bound (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (v₀ : ℝ)
    (hsecond : ∀ i, ν[fun ω => (X (i + 1) ω) ^ 2 | 𝓕 i] ≤ᵐ[ν] fun _ => v₀) (n : ℕ) :
    ∀ᵐ ω ∂ν, predictableQuadVar ν 𝓕 X n ω ≤ n * v₀ := by
  induction n with
  | zero => exact Eventually.of_forall (fun _ => by simp)
  | succ n ih =>
    filter_upwards [ih, hsecond n] with ω hn hv
    rw [predictableQuadVar_succ, Nat.cast_add, Nat.cast_one]
    change predictableQuadVar ν 𝓕 X n ω + ν[fun a => (X (n + 1) a) ^ 2 | 𝓕 n] ω ≤ (n + 1) * v₀
    linarith

/-- Self-check corollary 1: recovering `UpperConcentration.maximal_exponential` from
`freedmanProcess_supermartingale` when `𝔼[X_{i+1}^2 | 𝓕_i] ≤ v₀` a.e. -/
theorem corollary_maximal_exponential (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ) (hX : Adapted 𝓕 X)
    (b v₀ θ a : ℝ) (hb0 : 0 ≤ b) (hθ : 0 < θ) (hθb : θ * b ≤ 1)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0)
    (hsecond : ∀ i, ν[fun ω => (X (i + 1) ω) ^ 2 | 𝓕 i] ≤ᵐ[ν] fun _ => v₀) (T : ℕ) :
    ν {ω | ∃ n ≤ T, a + θ * n * v₀ ≤ partialSum X n ω} ≤
      ENNReal.ofReal (Real.exp (-θ * a)) := by
  have hsm := freedmanProcess_supermartingale ν 𝓕 X hX b θ hb0 hθ.le hθb hb hmean
  have hinit : ∫ ω, freedmanProcess ν 𝓕 X θ 0 ω ∂ν ≤ 1 := by simp [freedmanProcess_zero]
  have hville := ville_finite ν 𝓕 (freedmanProcess ν 𝓕 X θ) hsm
    (freedmanProcess_nonneg ν 𝓕 X θ) hinit (Real.exp (θ * a)) (Real.exp_pos _) T
  have hall : ∀ᵐ ω ∂ν, ∀ n ≤ T, predictableQuadVar ν 𝓕 X n ω ≤ n * v₀ := by
    rw [ae_all_iff]
    intro n
    filter_upwards [predictableQuadVar_le_of_step_bound ν 𝓕 X v₀ hsecond n] with ω hω _
    exact hω
  refine (measure_mono_ae ?_).trans (hville.trans_eq ?_)
  · filter_upwards [hall] with ω hV ⟨n, hn, hS⟩
    refine ⟨n, hn, Real.exp_le_exp.mpr ?_⟩
    have hVn := hV n hn
    have h1 := mul_le_mul_of_nonneg_left hS hθ.le
    have h2 := mul_le_mul_of_nonneg_left hVn (sq_nonneg θ)
    linarith
  · rw [one_div, ← Real.exp_neg, neg_mul]

/-- Self-check corollary 2: recovering `UpperConcentration.bounded_martingale_maximal`
directly from `freedman_linear_quantile_finite` when `𝔼[X_{i+1}^2 | 𝓕_i] ≤ v₀` a.e. -/
theorem corollary_bounded_martingale_maximal (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v₀ ℓ : ℝ) (hb0 : 0 < b) (hv : 0 ≤ v₀) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0)
    (hsecond : ∀ i, ν[fun ω => (X (i + 1) ω) ^ 2 | 𝓕 i] ≤ᵐ[ν] fun _ => v₀) (T : ℕ) :
    ν {ω | ∃ n ≤ T, (T : ℝ) * v₀ / b + b * ℓ < partialSum X n ω} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  have hall : ∀ᵐ ω ∂ν, ∀ n ≤ T, predictableQuadVar ν 𝓕 X n ω ≤ (T : ℝ) * v₀ := by
    rw [ae_all_iff]
    intro n
    filter_upwards [predictableQuadVar_le_of_step_bound ν 𝓕 X v₀ hsecond n] with ω hω hn
    have hle : (n : ℝ) ≤ T := Nat.cast_le.mpr hn
    exact hω.trans (mul_le_mul_of_nonneg_right hle hv)
  refine (measure_mono_ae ?_).trans
    (freedman_linear_quantile_finite ν 𝓕 X hX b ((T : ℝ) * v₀) ℓ hb0 (by positivity) hℓ hb hmean T)
  filter_upwards [hall] with ω hV ⟨n, hn, hS⟩
  exact ⟨n, hn, hS.le, hV n hn⟩

/-- `lem:martingale` (finite horizon `T`, including `b = 0` and `v = 0`):
if `|X_{i+1}| ≤ b` a.e., `𝔼[X_{i+1} | 𝓕_i] = 0` a.e., and `V_n ≤ v` a.e. for all `n ≤ T`,
then `ℙ(∃ n ≤ T, S_n > 2√(vℓ) + 2bℓ) ≤ exp(-ℓ)`. -/
theorem freedman_lemma14_finite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v ℓ : ℝ) (hb0 : 0 ≤ b) (hv : 0 ≤ v) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0)
    (T : ℕ) (hV : ∀ n ≤ T, ∀ᵐ ω ∂ν, predictableQuadVar ν 𝓕 X n ω ≤ v) :
    ν {ω | ∃ n ≤ T, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ < partialSum X n ω} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  by_cases hbpos : 0 < b
  · have hallV : ∀ᵐ ω ∂ν, ∀ n ≤ T, predictableQuadVar ν 𝓕 X n ω ≤ v := by
      rw [ae_all_iff]
      intro n
      by_cases hn : n ≤ T
      · filter_upwards [hV n hn] with ω hω _
        exact hω
      · exact Eventually.of_forall (fun _ h => (hn h).elim)
    refine (measure_mono_ae ?_).trans
      (freedman_quantile_finite ν 𝓕 X hX b v ℓ hbpos hv hℓ hb hmean T)
    filter_upwards [hallV] with ω hVω ⟨n, hn, hS⟩
    exact ⟨n, hn, hS.le, hVω n hn⟩
  · have hb_zero : b = 0 := le_antisymm (not_lt.mp hbpos) hb0
    have hallS : ∀ᵐ ω ∂ν, ∀ n : ℕ, |partialSum X n ω| ≤ 0 := by
      rw [ae_all_iff]
      intro n
      filter_upwards [prefix_abs_bound ν X b hb n] with ω hω
      simpa [hb_zero] using hω
    have hempty : ∀ᵐ ω ∂ν,
        ω ∉ {ω | ∃ n ≤ T, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ < partialSum X n ω} := by
      filter_upwards [hallS] with ω hS ⟨n, _, hlt⟩
      have hSn : partialSum X n ω ≤ 0 := (le_abs_self _).trans (hS n)
      have hpos : 0 ≤ 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ := by positivity
      linarith
    have hmeas0 : ν {ω | ∃ n ≤ T, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ < partialSum X n ω} = 0 :=
      measure_mono_null (fun ω hω => not_not.mpr hω) (ae_iff.mp hempty)
    rw [hmeas0]
    exact zero_le _

/-- Infinite-horizon version of `lem:martingale` (`T = ∞`, including `b = 0`):
if `|X_{i+1}| ≤ b` a.e., `𝔼[X_{i+1} | 𝓕_i] = 0` a.e., and `V_n ≤ v` a.e. for all `n : ℕ`,
then `ℙ(∃ n : ℕ, S_n > 2√(vℓ) + 2bℓ) ≤ exp(-ℓ)`. -/
theorem freedman_lemma14_infinite (𝓕 : Filtration ℕ m₀) (X : ℕ → Ω → ℝ)
    (hX : Adapted 𝓕 X) (b v ℓ : ℝ) (hb0 : 0 ≤ b) (hv : 0 ≤ v) (hℓ : 0 < ℓ)
    (hb : ∀ i, ∀ᵐ ω ∂ν, |X (i + 1) ω| ≤ b)
    (hmean : ∀ i, ν[X (i + 1) | 𝓕 i] =ᵐ[ν] 0)
    (hV : ∀ n : ℕ, ∀ᵐ ω ∂ν, predictableQuadVar ν 𝓕 X n ω ≤ v) :
    ν {ω | ∃ n : ℕ, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ < partialSum X n ω} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  let E : ℕ → Set Ω := fun T =>
    {ω | ∃ n ≤ T, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ < partialSum X n ω}
  have hmono : Monotone E := by
    intro T₁ T₂ hT ω ⟨n, hn, h⟩
    exact ⟨n, hn.trans hT, h⟩
  have hunion : {ω | ∃ n : ℕ, 2 * Real.sqrt (v * ℓ) + 2 * b * ℓ < partialSum X n ω} =
      ⋃ T : ℕ, E T := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, E]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  rw [hunion]
  exact measure_iUnion_le_of_monotone ν hmono (fun T =>
    freedman_lemma14_finite ν 𝓕 X hX b v ℓ hb0 hv hℓ hb hmean T (fun n _ => hV n))

end SelfCheckCorollaries

end
end LeanKit.Probability.Freedman
