import ClippedSGD.MixedNoise
import LeanKit.Probability.Freedman
import LeanKit.Probability.TimeUniform

/-! `lem:energy-budget`: common stopped energy concentration bound
on a finite or infinite horizon, built on `LeanKit.Probability.Freedman` and
`LeanKit.Probability.TimeUniform`. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators InnerProductSpace ENNReal
namespace ClippedSGD.EnergyBudget
open UpperConcentration ClippingConditional PredictableInner MixedNoise
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m₀ : MeasurableSpace Ω}

/-- Constant `C = p₀ + A + 2 √(K₀ A q) + 2 K₀ q` in `lem:energy-budget`. -/
def energyC (p₀ A_bud K₀ q : ℝ) : ℝ :=
  p₀ + A_bud + 2 * Real.sqrt (K₀ * A_bud * q) + 2 * K₀ * q

/-- Constant `D = B₀ + 2 √(V₀ q) + 2 J₀ q` in `lem:energy-budget`. -/
def energyD (B₀ V₀ J₀ q : ℝ) : ℝ :=
  B₀ + 2 * Real.sqrt (V₀ * q) + 2 * J₀ * q

/-- Energy threshold `H = (√C + D)^2` in `lem:energy-budget`. -/
def energyThreshold (p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ) : ℝ :=
  (Real.sqrt (energyC p₀ A_bud K₀ q) + energyD B₀ V₀ J₀ q) ^ 2

lemma energyC_nonneg {p₀ A_bud K₀ q : ℝ}
    (hp₀ : 0 ≤ p₀) (hA : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀) (hq : 0 ≤ q) :
    0 ≤ energyC p₀ A_bud K₀ q := by
  unfold energyC
  positivity

lemma energyD_nonneg {B₀ V₀ J₀ q : ℝ}
    (hB₀ : 0 ≤ B₀) (hV₀ : 0 ≤ V₀) (hJ₀ : 0 ≤ J₀) (hq : 0 ≤ q) :
    0 ≤ energyD B₀ V₀ J₀ q := by
  unfold energyD
  positivity

lemma energyThreshold_nonneg (p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ) :
    0 ≤ energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q :=
  sq_nonneg _

lemma sqrt_energyThreshold {p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ}
    (hp₀ : 0 ≤ p₀) (hA : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀)
    (hB₀ : 0 ≤ B₀) (hV₀ : 0 ≤ V₀) (hJ₀ : 0 ≤ J₀) (hq : 0 ≤ q) :
    Real.sqrt (energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q) =
      Real.sqrt (energyC p₀ A_bud K₀ q) + energyD B₀ V₀ J₀ q := by
  unfold energyThreshold
  have hD := energyD_nonneg hB₀ hV₀ hJ₀ hq
  exact Real.sqrt_sq (by positivity)

lemma p0_le_energyThreshold {p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ}
    (hp₀ : 0 ≤ p₀) (hA : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀)
    (hB₀ : 0 ≤ B₀) (hV₀ : 0 ≤ V₀) (hJ₀ : 0 ≤ J₀) (hq : 0 ≤ q) :
    p₀ ≤ energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q := by
  have hC := energyC_nonneg hp₀ hA hK₀ hq
  have hD := energyD_nonneg hB₀ hV₀ hJ₀ hq
  have hpC : p₀ ≤ energyC p₀ A_bud K₀ q := by
    unfold energyC
    linarith [Real.sqrt_nonneg (K₀ * A_bud * q), mul_nonneg hK₀ hq]
  calc
    p₀ ≤ energyC p₀ A_bud K₀ q := hpC
    _ = (Real.sqrt (energyC p₀ A_bud K₀ q)) ^ 2 := (Real.sq_sqrt hC).symm
    _ ≤ energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q := by
      unfold energyThreshold
      nlinarith [Real.sqrt_nonneg (energyC p₀ A_bud K₀ q)]

/-- Key algebraic closure inequality `C + √H D ≤ H` in `lem:energy-budget`. -/
lemma energy_closure_ineq {p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ}
    (hp₀ : 0 ≤ p₀) (hA : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀)
    (hB₀ : 0 ≤ B₀) (hV₀ : 0 ≤ V₀) (hJ₀ : 0 ≤ J₀) (hq : 0 ≤ q) :
    energyC p₀ A_bud K₀ q +
      Real.sqrt (energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q) * energyD B₀ V₀ J₀ q ≤
      energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q := by
  rw [sqrt_energyThreshold hp₀ hA hK₀ hB₀ hV₀ hJ₀ hq]
  have hC := energyC_nonneg hp₀ hA hK₀ hq
  have hD := energyD_nonneg hB₀ hV₀ hJ₀ hq
  unfold energyThreshold
  have hsq : (Real.sqrt (energyC p₀ A_bud K₀ q)) ^ 2 = energyC p₀ A_bud K₀ q :=
    Real.sq_sqrt hC
  nlinarith [Real.sqrt_nonneg (energyC p₀ A_bud K₀ q)]

/-- Deterministic variance budget triangle inequality in `lem:energy-budget`:
`∑_{t < N} (a_t M_t + s_t √H)^2 V_t ≤ (√(K₀ A_bud) + √(H V₀))^2`. -/
lemma deterministic_variance_sum_le (a s M V : ℕ → ℝ) (N : ℕ)
    (A_bud K₀ V₀ H : ℝ)
    (ha : ∀ t < N, 0 ≤ a t) (hs : ∀ t < N, 0 ≤ s t)
    (hM : ∀ t < N, 0 ≤ M t) (hV : ∀ t < N, 0 ≤ V t)
    (hA_bud : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀) (hV₀ : 0 ≤ V₀) (hH : 0 ≤ H)
    (hA : ∑ t ∈ Finset.range N, a t * V t ≤ A_bud)
    (hK : ∀ t < N, a t * (M t) ^ 2 ≤ K₀)
    (hV0 : ∑ t ∈ Finset.range N, (s t) ^ 2 * V t ≤ V₀) :
    ∑ t ∈ Finset.range N, (a t * M t + s t * Real.sqrt H) ^ 2 * V t ≤
      (Real.sqrt (K₀ * A_bud) + Real.sqrt (H * V₀)) ^ 2 := by
  have h1 : ∑ t ∈ Finset.range N, (a t * M t) ^ 2 * V t ≤ K₀ * A_bud := by
    calc
      ∑ t ∈ Finset.range N, (a t * M t) ^ 2 * V t
        = ∑ t ∈ Finset.range N, (a t * (M t) ^ 2) * (a t * V t) := by
          apply Finset.sum_congr rfl; intro t _; ring
      _ ≤ ∑ t ∈ Finset.range N, K₀ * (a t * V t) := by
          apply Finset.sum_le_sum
          intro t ht
          have htN := Finset.mem_range.mp ht
          exact mul_le_mul_of_nonneg_right (hK t htN) (mul_nonneg (ha t htN) (hV t htN))
      _ = K₀ * ∑ t ∈ Finset.range N, a t * V t := (Finset.mul_sum _ _ _).symm
      _ ≤ K₀ * A_bud := mul_le_mul_of_nonneg_left hA hK₀
  have h2 : ∑ t ∈ Finset.range N, (s t * Real.sqrt H) ^ 2 * V t ≤ H * V₀ := by
    calc
      ∑ t ∈ Finset.range N, (s t * Real.sqrt H) ^ 2 * V t
        = H * ∑ t ∈ Finset.range N, (s t) ^ 2 * V t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _
          rw [mul_pow, Real.sq_sqrt hH]
          ring
      _ ≤ H * V₀ := mul_le_mul_of_nonneg_left hV0 hH
  have hcs : (∑ t ∈ Finset.range N, (a t * M t * Real.sqrt (V t)) *
      (s t * Real.sqrt H * Real.sqrt (V t))) ^ 2 ≤
      (∑ t ∈ Finset.range N, (a t * M t * Real.sqrt (V t)) ^ 2) *
      (∑ t ∈ Finset.range N, (s t * Real.sqrt H * Real.sqrt (V t)) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun t => a t * M t * Real.sqrt (V t))
      (fun t => s t * Real.sqrt H * Real.sqrt (V t))
  have hsum_L : (∑ t ∈ Finset.range N, (a t * M t * Real.sqrt (V t)) ^ 2) =
      ∑ t ∈ Finset.range N, (a t * M t) ^ 2 * V t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [mul_pow, Real.sq_sqrt (hV t (Finset.mem_range.mp ht))]
  have hsum_R : (∑ t ∈ Finset.range N, (s t * Real.sqrt H * Real.sqrt (V t)) ^ 2) =
      ∑ t ∈ Finset.range N, (s t * Real.sqrt H) ^ 2 * V t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [mul_pow, Real.sq_sqrt (hV t (Finset.mem_range.mp ht))]
  have hsum_M : (∑ t ∈ Finset.range N, (a t * M t * Real.sqrt (V t)) *
      (s t * Real.sqrt H * Real.sqrt (V t))) =
      ∑ t ∈ Finset.range N, (a t * M t) * (s t * Real.sqrt H) * V t := by
    apply Finset.sum_congr rfl
    intro t ht
    have hVt := Real.mul_self_sqrt (hV t (Finset.mem_range.mp ht))
    calc
      (a t * M t * Real.sqrt (V t)) * (s t * Real.sqrt H * Real.sqrt (V t))
        = (a t * M t) * (s t * Real.sqrt H) * (Real.sqrt (V t) * Real.sqrt (V t)) := by ring
      _ = (a t * M t) * (s t * Real.sqrt H) * V t := by rw [hVt]
  rw [hsum_L, hsum_R, hsum_M] at hcs
  have hsum_L_nn : 0 ≤ ∑ t ∈ Finset.range N, (a t * M t) ^ 2 * V t :=
    Finset.sum_nonneg (fun t ht => mul_nonneg (sq_nonneg _) (hV t (Finset.mem_range.mp ht)))
  have hsum_R_nn : 0 ≤ ∑ t ∈ Finset.range N, (s t * Real.sqrt H) ^ 2 * V t :=
    Finset.sum_nonneg (fun t ht => mul_nonneg (sq_nonneg _) (hV t (Finset.mem_range.mp ht)))
  have hsum_M_nn : 0 ≤ ∑ t ∈ Finset.range N, (a t * M t) * (s t * Real.sqrt H) * V t := by
    apply Finset.sum_nonneg
    intro t ht
    have htN := Finset.mem_range.mp ht
    exact mul_nonneg (mul_nonneg (mul_nonneg (ha t htN) (hM t htN))
      (mul_nonneg (hs t htN) (Real.sqrt_nonneg H))) (hV t htN)
  have h3 : ∑ t ∈ Finset.range N, (a t * M t) * (s t * Real.sqrt H) * V t ≤
      Real.sqrt (K₀ * A_bud) * Real.sqrt (H * V₀) := by
    have hprod : (∑ t ∈ Finset.range N, (a t * M t) * (s t * Real.sqrt H) * V t) ^ 2 ≤
        (K₀ * A_bud) * (H * V₀) :=
      hcs.trans (mul_le_mul h1 h2 hsum_R_nn (mul_nonneg hK₀ hA_bud))
    rw [← Real.sqrt_mul (mul_nonneg hK₀ hA_bud), ← Real.sqrt_sq hsum_M_nn]
    exact Real.sqrt_le_sqrt hprod
  have hexp : ∑ t ∈ Finset.range N, (a t * M t + s t * Real.sqrt H) ^ 2 * V t =
      (∑ t ∈ Finset.range N, (a t * M t) ^ 2 * V t) +
      2 * (∑ t ∈ Finset.range N, (a t * M t) * (s t * Real.sqrt H) * V t) +
      (∑ t ∈ Finset.range N, (s t * Real.sqrt H) ^ 2 * V t) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hexp, add_sq, Real.sq_sqrt (mul_nonneg hK₀ hA_bud), Real.sq_sqrt (mul_nonneg hH hV₀)]
  linarith

/-- Nonnegative version of `centered_nonnegative` allowing `K ≥ 0`. -/
lemma centered_nonnegative_nonneg (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (Y : Ω → ℝ) (hY : @Measurable Ω ℝ m₀ _ Y)
    (K V : ℝ) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hb : ∀ᵐ ω ∂ν, 0 ≤ Y ω ∧ Y ω ≤ K)
    (hmean : ν[Y | m] ≤ᵐ[ν] fun _ => V) :
    Integrable Y ν ∧
    (ν[fun ω => Y ω - ν[Y | m] ω | m] =ᵐ[ν] 0) ∧
    (∀ᵐ ω ∂ν, |Y ω - ν[Y | m] ω| ≤ K) ∧
    (ν[fun ω => (Y ω - ν[Y | m] ω) ^ 2 | m] ≤ᵐ[ν] fun _ => K * V) := by
  letI : MeasurableSpace Ω := m₀
  rcases eq_or_lt_of_le hK with rfl | hKpos
  · have hY0 : Y =ᵐ[ν] 0 := hb.mono (fun ω hω => le_antisymm hω.2 hω.1)
    have hi : Integrable Y ν := (integrable_zero Ω ℝ ν).congr hY0.symm
    have hce0 : ν[Y | m] =ᵐ[ν] 0 := by
      simpa only [condExp_zero] using condExp_congr_ae (m := m) hY0
    have hdiff0 : (fun ω => Y ω - ν[Y | m] ω) =ᵐ[ν] 0 := by
      filter_upwards [hY0, hce0] with ω h1 h2
      simp [h1, h2]
    have hsq0 : (fun ω => (Y ω - ν[Y | m] ω) ^ 2) =ᵐ[ν] 0 := by
      filter_upwards [hdiff0] with ω h1
      simp [h1]
    have hce_diff0 : ν[fun ω => Y ω - ν[Y | m] ω | m] =ᵐ[ν] 0 := by
      simpa only [condExp_zero] using condExp_congr_ae (m := m) hdiff0
    have hce_sq0 : ν[fun ω => (Y ω - ν[Y | m] ω) ^ 2 | m] =ᵐ[ν] 0 := by
      simpa only [condExp_zero] using condExp_congr_ae (m := m) hsq0
    refine ⟨ hi, hce_diff0, ?_, ?_ ⟩
    · filter_upwards [hdiff0] with ω h1
      simp [h1]
    · filter_upwards [hce_sq0] with ω h1
      simp [h1]
  · exact centered_nonnegative ν m hm Y hY K V hKpos hV hb hmean

/-- Nonnegative version of `conditional_mixed_second` allowing `0 ≤ d` and `0 ≤ h` when
`|D| ≤ 0` on `d = 0` and `|H| ≤ 0` on `h = 0`. -/
lemma conditional_mixed_second_nonneg (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : MeasurableSpace Ω) (D H : Ω → ℝ)
    (hD : @Measurable Ω ℝ m₀ _ D) (hH : @Measurable Ω ℝ m₀ _ H)
    (d h V bD bH : ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h) (hV : 0 ≤ V)
    (hbD0 : d = 0 → bD = 0) (hbH0 : h = 0 → bH = 0)
    (hDb : ∀ᵐ ω ∂ν, |D ω| ≤ bD) (hHb : ∀ᵐ ω ∂ν, |H ω| ≤ bH)
    (hD2 : ν[fun ω => (D ω) ^ 2 | m] ≤ᵐ[ν] fun _ => d ^ 2 * V)
    (hH2 : ν[fun ω => (H ω) ^ 2 | m] ≤ᵐ[ν] fun _ => h ^ 2 * V) :
    ν[fun ω => (D ω + H ω) ^ 2 | m] ≤ᵐ[ν] fun _ => (d + h) ^ 2 * V := by
  letI : MeasurableSpace Ω := m₀
  rcases eq_or_lt_of_le hd with rfl | hdpos
  · have hbD : bD = 0 := hbD0 rfl
    have hD0 : D =ᵐ[ν] 0 := by
      filter_upwards [hDb] with ω hω
      rw [hbD] at hω
      exact abs_nonpos_iff.mp hω
    have hsum : (fun ω => (D ω + H ω) ^ 2) =ᵐ[ν] (fun ω => (H ω) ^ 2) := by
      filter_upwards [hD0] with ω hω
      simp [hω]
    filter_upwards [condExp_congr_ae (m := m) hsum, hH2] with ω hsω hHω
    rw [hsω, zero_add]
    exact hHω
  · rcases eq_or_lt_of_le hh with rfl | hhpos
    · have hbH : bH = 0 := hbH0 rfl
      have hH0 : H =ᵐ[ν] 0 := by
        filter_upwards [hHb] with ω hω
        rw [hbH] at hω
        exact abs_nonpos_iff.mp hω
      have hsum : (fun ω => (D ω + H ω) ^ 2) =ᵐ[ν] (fun ω => (D ω) ^ 2) := by
        filter_upwards [hH0] with ω hω
        simp [hω]
      filter_upwards [condExp_congr_ae (m := m) hsum, hD2] with ω hsω hDω
      rw [hsω, add_zero]
      exact hDω
    · exact conditional_mixed_second ν m D H hD hH d h V bD bH hdpos hhpos hV hDb hHb hD2 hH2

/-- Predictable pre-stopping set `{P 0 ≤ p₀ ∧ ∀ j ≤ t, P j ≤ H}` in `lem:energy-budget`. -/
def preStopSet (P : ℕ → Ω → ℝ) (p₀ H : ℝ) (t : ℕ) : Set Ω :=
  {ω | P 0 ω ≤ p₀ ∧ ∀ j ≤ t, P j ω ≤ H}

lemma preStopSet_measurable (𝓕 : Filtration ℕ m₀) (P : ℕ → Ω → ℝ)
    (hP : Adapted 𝓕 P) (p₀ H : ℝ) (t : ℕ) :
    MeasurableSet[𝓕 t] (preStopSet P p₀ H t) := by
  unfold preStopSet
  simp only [Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter
  · exact measurableSet_le ((hP 0).mono (𝓕.mono (Nat.zero_le t))).measurable measurable_const
  · apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact measurableSet_le ((hP j).mono (𝓕.mono hj)).measurable measurable_const

/-- Shifted scalar sequence: `0` at index `0`, `q t` at index `t + 1`. -/
def shiftSeq (q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => q t

lemma shiftSeq_adapted (𝓕 : Filtration ℕ m₀) (q : ℕ → Ω → ℝ)
    (hq : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (q t)) : Adapted 𝓕 (shiftSeq q) := by
  intro t
  cases t with
  | zero => exact stronglyMeasurable_zero
  | succ t => exact hq t

/-- `lem:energy-budget` (finite horizon `N`): stopped energy bound.
Here `e t` is already stopped on `J t` (so `e t ω = 0` for `ω ∉ J t`), and satisfies
the conditional bias, variance, range, and centered-range bounds `(B t, V t, M t, U t)`. -/
theorem energy_budget_finite (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    (N : ℕ) (P : ℕ → Ω → ℝ) (hP : Adapted 𝓕 P) (hP_nn : ∀ t ω, 0 ≤ P t ω)
    (J : ℕ → Set Ω) (hJ_meas : ∀ t, MeasurableSet[𝓕 t] (J t))
    (hJ_mono : ∀ t, J (t + 1) ⊆ J t) (ℰ : Set Ω)
    (e w : ℕ → Ω → E)
    (he_meas : ∀ t < N, StronglyMeasurable[𝓕 (t + 1)] (e t))
    (he_int : ∀ t < N, Integrable (e t) ν)
    (he_sq_int : ∀ t < N, Integrable (fun ω => ‖e t ω‖ ^ 2) ν)
    (he_supp : ∀ t < N, ∀ ω, ω ∉ J t → e t ω = 0)
    (hw_meas : ∀ t < N, StronglyMeasurable[𝓕 t] (w t))
    (a s B V M U : ℕ → ℝ)
    (ha : ∀ t < N, 0 ≤ a t) (hs : ∀ t < N, 0 ≤ s t)
    (hB : ∀ t < N, 0 ≤ B t) (hV : ∀ t < N, 0 ≤ V t)
    (hM : ∀ t < N, 0 ≤ M t) (hU : ∀ t < N, 0 ≤ U t)
    (hw_bound : ∀ t < N, ∀ ω ∈ J t, ‖w t ω‖ ≤ s t * Real.sqrt (P t ω))
    (hrec : ∀ m < N, ∀ ω ∈ ℰ ∩ J m,
      P (m + 1) ω ≤ P 0 ω +
        ∑ t ∈ Finset.range (m + 1), (a t * ‖e t ω‖ ^ 2 + ⟪e t ω, w t ω⟫_ℝ))
    (hBias : ∀ t < N, ∀ᵐ ω ∂ν, ‖ν[e t | 𝓕 t] ω‖ ≤ B t)
    (hVar : ∀ t < N, ν[fun ω => ‖e t ω‖ ^ 2 | 𝓕 t] ≤ᵐ[ν] fun _ => V t)
    (hRange : ∀ t < N, ∀ᵐ ω ∂ν, ‖e t ω‖ ≤ M t)
    (hCentRange : ∀ t < N, ∀ᵐ ω ∂ν, ‖e t ω - ν[e t | 𝓕 t] ω‖ ≤ U t)
    (p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ)
    (hp₀ : 0 ≤ p₀) (hA_bud : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀)
    (hB₀ : 0 ≤ B₀) (hV₀ : 0 ≤ V₀) (hJ₀ : 0 ≤ J₀) (hq : 0 < q)
    (hA_sum : ∑ t ∈ Finset.range N, a t * V t ≤ A_bud)
    (hK_sup : ∀ t < N, a t * (M t) ^ 2 ≤ K₀)
    (hB_sum : ∑ t ∈ Finset.range N, s t * B t ≤ B₀)
    (hV_sum : ∑ t ∈ Finset.range N, (s t) ^ 2 * V t ≤ V₀)
    (hJ_sup : ∀ t < N, s t * U t ≤ J₀) :
    ν {ω ∈ ℰ | P 0 ω ≤ p₀ ∧ ∃ m < N, ω ∈ J m ∧
        energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q < P (m + 1) ω} ≤
      ENNReal.ofReal (Real.exp (-q)) := by
  letI : MeasurableSpace Ω := m₀
  let H := energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q
  have hH_nn : 0 ≤ H := energyThreshold_nonneg p₀ A_bud K₀ B₀ V₀ J₀ q
  let I₀ : ℕ → Set Ω := fun t => preStopSet P p₀ H t
  have hI₀_meas : ∀ t, MeasurableSet[𝓕 t] (I₀ t) :=
    fun t => preStopSet_measurable 𝓕 P hP p₀ H t
  have hI₀_meas0 : ∀ t, MeasurableSet (I₀ t) :=
    fun t => 𝓕.le t _ (hI₀_meas t)
  let I : ℕ → Set Ω := fun t => J t ∩ I₀ t
  have hI_meas : ∀ t, MeasurableSet[𝓕 t] (I t) :=
    fun t => (hJ_meas t).inter (hI₀_meas t)
  let eI : ℕ → Ω → E := fun t => if t < N then (I₀ t).indicator (e t) else 0
  let wI : ℕ → Ω → E := fun t => if t < N then (I t).indicator (w t) else 0
  let Y : ℕ → Ω → ℝ := fun t ω => ‖eI t ω‖ ^ 2
  let mY : ℕ → Ω → ℝ := fun t => ν[Y t | 𝓕 t]
  let bI : ℕ → Ω → E := fun t => ν[eI t | 𝓕 t]
  let uI : ℕ → Ω → E := fun t ω => eI t ω - bI t ω
  let aN : ℕ → ℝ := fun t => if t < N then a t else 0
  let sN : ℕ → ℝ := fun t => if t < N then s t else 0
  let BN : ℕ → ℝ := fun t => if t < N then B t else 0
  let VN : ℕ → ℝ := fun t => if t < N then V t else 0
  let MN : ℕ → ℝ := fun t => if t < N then M t else 0
  let UN : ℕ → ℝ := fun t => if t < N then U t else 0
  let D_inc : ℕ → Ω → ℝ := fun t ω => aN t * (Y t ω - mY t ω)
  let H_inc : ℕ → Ω → ℝ := fun t ω => ⟪wI t ω, uI t ω⟫_ℝ
  let X_inc : ℕ → Ω → ℝ := fun t ω => D_inc t ω + H_inc t ω
  have heI_meas : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (eI t) := by
    intro t
    dsimp [eI]
    split_ifs with ht
    · exact (he_meas t ht).indicator (𝓕.mono (Nat.le_succ t) _ (hI₀_meas t))
    · exact stronglyMeasurable_zero
  have hwI_meas : ∀ t, StronglyMeasurable[𝓕 t] (wI t) := by
    intro t
    dsimp [wI]
    split_ifs with ht
    · exact (hw_meas t ht).indicator (hI_meas t)
    · exact stronglyMeasurable_zero
  have hwI_bound : ∀ t ω, ‖wI t ω‖ ≤ sN t * Real.sqrt H := by
    intro t ω
    dsimp [wI, sN]
    split_ifs with ht
    · by_cases hω : ω ∈ I t
      · simp only [Set.indicator_of_mem hω]
        have h1 := hw_bound t ht ω hω.1
        have h2 : P t ω ≤ H := hω.2.2 t le_rfl
        exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (hs t ht))
      · simp only [Set.indicator_of_not_mem hω, norm_zero]
        exact mul_nonneg (hs t ht) (Real.sqrt_nonneg H)
    · simp
  have heI_int : ∀ t, Integrable (eI t) ν := by
    intro t
    dsimp [eI]
    split_ifs with ht
    · exact (he_int t ht).indicator (hI₀_meas0 t)
    · exact integrable_zero Ω E ν
  have hY_int : ∀ t, Integrable (Y t) ν := by
    intro t
    dsimp [Y, eI]
    split_ifs with ht
    · have heq : (fun ω => ‖(I₀ t).indicator (e t) ω‖ ^ 2) =
          (I₀ t).indicator (fun ω => ‖e t ω‖ ^ 2) := by
        funext ω
        by_cases hω : ω ∈ I₀ t <;> simp [hω]
      rw [heq]
      exact (he_sq_int t ht).indicator (hI₀_meas0 t)
    · convert integrable_zero Ω ℝ ν
      simp
  have hbI_eq : ∀ t < N, bI t =ᵐ[ν] (I₀ t).indicator (ν[e t | 𝓕 t]) := by
    intro t ht
    dsimp [bI, eI]
    rw [if_pos ht]
    exact condExp_indicator (he_int t ht) (hI₀_meas t)
  have hmY_eq : ∀ t < N, mY t =ᵐ[ν] (I₀ t).indicator (ν[fun ω => ‖e t ω‖ ^ 2 | 𝓕 t]) := by
    intro t ht
    dsimp [mY, Y, eI]
    rw [if_pos ht]
    have heq : (fun ω => ‖(I₀ t).indicator (e t) ω‖ ^ 2) =
        (I₀ t).indicator (fun ω => ‖e t ω‖ ^ 2) := by
      funext ω
      by_cases hω : ω ∈ I₀ t <;> simp [hω]
    rw [heq]
    exact condExp_indicator (he_sq_int t ht) (hI₀_meas t)
  have hbI_bound : ∀ t < N, ∀ᵐ ω ∂ν, ‖bI t ω‖ ≤ B t ∧ (ω ∉ I₀ t → bI t ω = 0) := by
    intro t ht
    filter_upwards [hbI_eq t ht, hBias t ht] with ω heq hb
    rw [heq]
    refine ⟨ ?_, fun hnot => by simp [hnot] ⟩
    by_cases hω : ω ∈ I₀ t
    · simpa [hω] using hb
    · simp [hω, hB t ht]
  have hmY_bound : ∀ t < N, ∀ᵐ ω ∂ν, mY t ω ≤ V t ∧ (ω ∉ I₀ t → mY t ω = 0) := by
    intro t ht
    filter_upwards [hmY_eq t ht, hVar t ht] with ω heq hv
    rw [heq]
    refine ⟨ ?_, fun hnot => by simp [hnot] ⟩
    by_cases hω : ω ∈ I₀ t
    · simpa [hω] using hv
    · simp [hω, hV t ht]
  have hY_props : ∀ t < N,
      (ν[D_inc t | 𝓕 t] =ᵐ[ν] 0) ∧
      (∀ᵐ ω ∂ν, |D_inc t ω| ≤ aN t * (MN t) ^ 2) ∧
      (ν[fun ω => (D_inc t ω) ^ 2 | 𝓕 t] ≤ᵐ[ν] fun _ => (aN t * MN t) ^ 2 * VN t) := by
    intro t ht
    have hYb : ∀ᵐ ω ∂ν, 0 ≤ Y t ω ∧ Y t ω ≤ (M t) ^ 2 := by
      filter_upwards [hRange t ht] with ω hr
      refine ⟨ sq_nonneg _, ?_ ⟩
      dsimp [Y, eI]
      rw [if_pos ht]
      by_cases hω : ω ∈ I₀ t
      · simp only [Set.indicator_of_mem hω]
        exact pow_le_pow_left₀ (norm_nonneg _) hr 2
      · simp [hω, sq_nonneg]
    have hYm : ν[Y t | 𝓕 t] ≤ᵐ[ν] fun _ => V t :=
      (hmY_bound t ht).mono (fun ω hω => hω.1)
    have hY_meas : @Measurable Ω ℝ m₀ _ (Y t) :=
      (((heI_meas t).mono (𝓕.le (t + 1))).norm.pow 2).measurable
    obtain ⟨ hiY, hm0, hbD, hvD ⟩ := centered_nonnegative_nonneg ν (𝓕 t) (𝓕.le t)
      (Y t) hY_meas ((M t) ^ 2) (V t) (sq_nonneg _) (hV t ht) hYb hYm
    have ha_pos : 0 ≤ a t := ha t ht
    refine ⟨ ?_, ?_, ?_ ⟩
    · have hs_ce := condExp_smul (a t) (fun ω => Y t ω - mY t ω) (𝓕 t) (μ := ν)
      filter_upwards [hs_ce, hm0] with ω hsω hm0ω
      dsimp [D_inc, aN]
      rw [if_pos ht]
      change ν[fun a_1 => a t * (Y t a_1 - mY t a_1) | 𝓕 t] ω =
        a t * ν[fun a_1 => Y t a_1 - mY t a_1 | 𝓕 t] ω at hsω
      rw [hsω, hm0ω, Pi.zero_apply, mul_zero]
    · filter_upwards [hbD] with ω hbω
      dsimp [D_inc, aN, MN]
      rw [if_pos ht, if_pos ht, abs_mul, abs_of_nonneg ha_pos]
      exact mul_le_mul_of_nonneg_left hbω ha_pos
    · have heq : (fun ω => (D_inc t ω) ^ 2) =
          (fun ω => (a t) ^ 2 * (Y t ω - mY t ω) ^ 2) := by
        funext ω; dsimp [D_inc, aN]; rw [if_pos ht]; ring
      rw [heq]
      have hs_ce := condExp_smul ((a t) ^ 2) (fun ω => (Y t ω - mY t ω) ^ 2) (𝓕 t) (μ := ν)
      filter_upwards [hs_ce, hvD] with ω hsω hvω
      change ν[fun a_1 => (a t) ^ 2 * (Y t a_1 - mY t a_1) ^ 2 | 𝓕 t] ω =
        (a t) ^ 2 * ν[fun a_1 => (Y t a_1 - mY t a_1) ^ 2 | 𝓕 t] ω at hsω
      rw [hsω]
      dsimp [aN, MN, VN]
      rw [if_pos ht, if_pos ht, if_pos ht]
      calc
        (a t) ^ 2 * ν[fun a_1 => (Y t a_1 - mY t a_1) ^ 2 | 𝓕 t] ω
          ≤ (a t) ^ 2 * ((M t) ^ 2 * V t) := mul_le_mul_of_nonneg_left hvω (sq_nonneg _)
        _ = (a t * M t) ^ 2 * V t := by ring
  have hH_props : ∀ t < N,
      (ν[H_inc t | 𝓕 t] =ᵐ[ν] 0) ∧
      (∀ᵐ ω ∂ν, |H_inc t ω| ≤ sN t * Real.sqrt H * UN t) ∧
      (ν[fun ω => (H_inc t ω) ^ 2 | 𝓕 t] ≤ᵐ[ν] fun _ => (sN t * Real.sqrt H) ^ 2 * VN t) := by
    intro t ht
    have huI_int : Integrable (uI t) ν := (heI_int t).sub integrable_condExp
    have huI_sq_int : Integrable (fun ω => ‖uI t ω‖ ^ 2) ν := by
      have hL2 := (memLp_two_iff_integrable_sq_norm (heI_int t).1).mpr (hY_int t)
      exact (hL2.sub (hL2.condExp (m := 𝓕 t))).integrable_norm_pow (by norm_num)
    have huI_mean : ν[uI t | 𝓕 t] =ᵐ[ν] 0 :=
      centered_condExp_zero ν (𝓕 t) (𝓕.le t) (eI t) (heI_int t)
    have huI_var : ν[fun ω => ‖uI t ω‖ ^ 2 | 𝓕 t] ≤ᵐ[ν] fun _ => V t := by
      have hred := conditional_centered_second_le ν (𝓕 t) (𝓕.le t) (eI t) (heI_int t) (hY_int t)
      exact hred.trans ((hmY_bound t ht).mono (fun ω hω => hω.1))
    have huI_range : ∀ᵐ ω ∂ν, ‖uI t ω‖ ≤ U t := by
      filter_upwards [hbI_eq t ht, hCentRange t ht] with ω heq hc
      dsimp [uI, eI]
      rw [if_pos ht, heq]
      by_cases hω : ω ∈ I₀ t
      · simpa [hω] using hc
      · simp [hω, hU t ht]
    have hw_b : ∀ᵐ ω ∂ν, ‖wI t ω‖ ≤ s t * Real.sqrt H := by
      apply Eventually.of_forall
      intro ω
      simpa [sN, ht] using hwI_bound t ω
    have hm0 := inner_condExp_zero ν (𝓕 t) (𝓕.le t) (uI t) (wI t) huI_int (hwI_meas t)
      (s t * Real.sqrt H) hw_b huI_mean
    have hvar := (conditional_inner_variance ν (𝓕 t) (𝓕.le t) (uI t) (wI t) huI_int huI_sq_int
      (hwI_meas t) (s t * Real.sqrt H) (V t) (mul_nonneg (hs t ht) (Real.sqrt_nonneg H))
      hw_b huI_var).2
    refine ⟨ hm0, ?_, ?_ ⟩
    · filter_upwards [huI_range, hw_b] with ω huω hwω
      dsimp [H_inc, sN, UN]
      rw [if_pos ht, if_pos ht, ← Real.norm_eq_abs]
      exact (norm_inner_le_norm (wI t ω) (uI t ω)).trans
        (mul_le_mul hwω huω (norm_nonneg _) (mul_nonneg (hs t ht) (Real.sqrt_nonneg H)))
    · filter_upwards [hvar] with ω hvω
      simpa [H_inc, sN, VN, ht] using hvω
  have hX_meas : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (X_inc t) := by
    intro t
    have hYm : StronglyMeasurable[𝓕 (t + 1)] (Y t) := ((heI_meas t).norm.pow 2)
    have hmYm : StronglyMeasurable[𝓕 (t + 1)] (mY t) :=
      (stronglyMeasurable_condExp (m := 𝓕 t)).mono (𝓕.mono (Nat.le_succ t))
    have hDm : StronglyMeasurable[𝓕 (t + 1)] (D_inc t) := (hYm.sub hmYm).const_mul (aN t)
    have huIm : StronglyMeasurable[𝓕 (t + 1)] (uI t) :=
      (heI_meas t).sub ((stronglyMeasurable_condExp (m := 𝓕 t)).mono (𝓕.mono (Nat.le_succ t)))
    have hHm : StronglyMeasurable[𝓕 (t + 1)] (H_inc t) :=
      ((hwI_meas t).mono (𝓕.mono (Nat.le_succ t))).inner huIm
    exact hDm.add hHm
  let b_tot := K₀ + Real.sqrt H * J₀
  let v_tot := (Real.sqrt (K₀ * A_bud) + Real.sqrt (H * V₀)) ^ 2
  have hb_tot_nn : 0 ≤ b_tot := by positivity
  have hv_tot_nn : 0 ≤ v_tot := sq_nonneg _
  have hX_props : ∀ t < N,
      Integrable (X_inc t) ν ∧ Integrable (fun ω => (X_inc t ω) ^ 2) ν ∧
      (ν[X_inc t | 𝓕 t] =ᵐ[ν] 0) ∧
      (∀ᵐ ω ∂ν, |X_inc t ω| ≤ b_tot) ∧
      (ν[fun ω => (X_inc t ω) ^ 2 | 𝓕 t] ≤ᵐ[ν]
        fun _ => (a t * M t + s t * Real.sqrt H) ^ 2 * V t) := by
    intro t ht
    have hD_meas0 : @Measurable Ω ℝ m₀ _ (D_inc t) := by
      have hYm : StronglyMeasurable[𝓕 (t + 1)] (Y t) := ((heI_meas t).norm.pow 2)
      have hmYm : StronglyMeasurable[𝓕 (t + 1)] (mY t) :=
        (stronglyMeasurable_condExp (m := 𝓕 t)).mono (𝓕.mono (Nat.le_succ t))
      exact (((hYm.sub hmYm).const_mul (aN t)).mono (𝓕.le (t + 1))).measurable
    have hH_meas0 : @Measurable Ω ℝ m₀ _ (H_inc t) := by
      have huIm : StronglyMeasurable[𝓕 (t + 1)] (uI t) :=
        (heI_meas t).sub ((stronglyMeasurable_condExp (m := 𝓕 t)).mono (𝓕.mono (Nat.le_succ t)))
      exact ((((hwI_meas t).mono (𝓕.mono (Nat.le_succ t))).inner huIm).mono (𝓕.le (t + 1))).measurable
    have hDb := (hY_props t ht).2.1
    have hHb := (hH_props t ht).2.1
    have hX_b : ∀ᵐ ω ∂ν, |X_inc t ω| ≤ b_tot := by
      filter_upwards [hDb, hHb] with ω hdω hhω
      dsimp [aN, MN, sN, UN] at hdω hhω
      rw [if_pos ht, if_pos ht] at hdω hhω
      have h1 : a t * (M t) ^ 2 ≤ K₀ := hK_sup t ht
      have h2 : s t * Real.sqrt H * U t ≤ Real.sqrt H * J₀ := by
        calc
          s t * Real.sqrt H * U t = Real.sqrt H * (s t * U t) := by ring
          _ ≤ Real.sqrt H * J₀ := mul_le_mul_of_nonneg_left (hJ_sup t ht) (Real.sqrt_nonneg H)
      exact (abs_add (D_inc t ω) (H_inc t ω)).trans ((add_le_add hdω hhω).trans (add_le_add h1 h2))
    have hX_int : Integrable (X_inc t) ν :=
      integrable_of_abs_bound ν (X_inc t)
        (((hX_meas t).mono (𝓕.le (t + 1))).measurable) b_tot hX_b
    have hX2_int : Integrable (fun ω => (X_inc t ω) ^ 2) ν := by
      apply integrable_of_abs_bound ν _
        ((((hX_meas t).mono (𝓕.le (t + 1))).measurable).pow_const 2) (b_tot ^ 2)
      filter_upwards [hX_b] with ω hω
      rw [abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb_tot_nn).mpr hω
    have hD_int : Integrable (D_inc t) ν :=
      integrable_of_abs_bound ν (D_inc t) hD_meas0 (aN t * (MN t) ^ 2) hDb
    have hH_int : Integrable (H_inc t) ν :=
      integrable_of_abs_bound ν (H_inc t) hH_meas0 (sN t * Real.sqrt H * UN t) hHb
    have hX_mean : ν[X_inc t | 𝓕 t] =ᵐ[ν] 0 := by
      have ha_ce := condExp_add hD_int hH_int (𝓕 t)
      filter_upwards [ha_ce, (hY_props t ht).1, (hH_props t ht).1] with ω haω hd0 hh0
      change ν[fun a_1 => D_inc t a_1 + H_inc t a_1 | 𝓕 t] ω =
        ν[D_inc t | 𝓕 t] ω + ν[H_inc t | 𝓕 t] ω at haω
      change ν[X_inc t | 𝓕 t] ω = 0
      rw [haω, hd0, hh0]
      simp
    have hX_second : ν[fun ω => (X_inc t ω) ^ 2 | 𝓕 t] ≤ᵐ[ν]
        fun _ => (a t * M t + s t * Real.sqrt H) ^ 2 * V t := by
      have hm2 := conditional_mixed_second_nonneg ν (𝓕 t) (D_inc t) (H_inc t) hD_meas0 hH_meas0
        (aN t * MN t) (sN t * Real.sqrt H) (VN t)
        (aN t * (MN t) ^ 2) (sN t * Real.sqrt H * UN t)
        (by dsimp [aN, MN]; rw [if_pos ht, if_pos ht]; exact mul_nonneg (ha t ht) (hM t ht))
        (by dsimp [sN]; rw [if_pos ht]; exact mul_nonneg (hs t ht) (Real.sqrt_nonneg H))
        (by dsimp [VN]; rw [if_pos ht]; exact hV t ht)
        (fun hd0 => by
          dsimp [aN, MN] at hd0 ⊢
          rw [if_pos ht, if_pos ht] at hd0 ⊢
          rcases mul_eq_zero.mp hd0 with ha0 | hM0
          · simp [ha0]
          · simp [hM0])
        (fun hh0 => by simp [hh0])
        hDb hHb (hY_props t ht).2.2 (hH_props t ht).2.2
      filter_upwards [hm2] with ω hm2ω
      simpa [X_inc, aN, MN, sN, VN, ht] using hm2ω
    exact ⟨ hX_int, hX2_int, hX_mean, hX_b, hX_second ⟩
  have hX_zero_ge : ∀ t, ¬ t < N → X_inc t = 0 := by
    intro t ht
    funext ω
    dsimp [X_inc, D_inc, H_inc, aN, wI]
    rw [if_neg ht, if_neg ht]
    simp
  let X_shift := shiftSeq X_inc
  have hX_shift_ad : Adapted 𝓕 X_shift := shiftSeq_adapted 𝓕 X_inc hX_meas
  have hX_shift_b : ∀ i, ∀ᵐ ω ∂ν, |X_shift (i + 1) ω| ≤ b_tot := by
    intro i
    by_cases hi : i < N
    · exact (hX_props i hi).2.2.2.1
    · apply Eventually.of_forall
      intro ω
      change |X_inc i ω| ≤ b_tot
      rw [hX_zero_ge i hi]
      simpa using hb_tot_nn
  have hX_shift_mean : ∀ i, ν[X_shift (i + 1) | 𝓕 i] =ᵐ[ν] 0 := by
    intro i
    by_cases hi : i < N
    · exact (hX_props i hi).2.2.1
    · change ν[X_inc i | 𝓕 i] =ᵐ[ν] 0
      rw [hX_zero_ge i hi]
      exact EventuallyEq.of_eq condExp_zero
  have h_sum_var : ∀ n ≤ N, ∀ᵐ ω ∂ν,
      LeanKit.Probability.Freedman.predictableQuadVar ν 𝓕 X_shift n ω ≤ v_tot := by
    intro n hn
    have hall : ∀ᵐ ω ∂ν, ∀ i < N,
        ν[fun a_1 => (X_shift (i + 1) a_1) ^ 2 | 𝓕 i] ω ≤
          (a i * M i + s i * Real.sqrt H) ^ 2 * V i := by
      rw [ae_all_iff]
      intro i
      by_cases hi : i < N
      · filter_upwards [(hX_props i hi).2.2.2.2] with ω hω _
        exact hω
      · exact Eventually.of_forall (fun _ hlt => (hi hlt).elim)
    filter_upwards [hall] with ω hω
    unfold LeanKit.Probability.Freedman.predictableQuadVar
    have hsub : Finset.range n ⊆ Finset.range N := Finset.range_mono hn
    have hle1 : (∑ i ∈ Finset.range n, ν[fun a_1 => (X_shift (i + 1) a_1) ^ 2 | 𝓕 i] ω) ≤
        ∑ i ∈ Finset.range n, (a i * M i + s i * Real.sqrt H) ^ 2 * V i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hω i (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)
    have hle2 : (∑ i ∈ Finset.range n, (a i * M i + s i * Real.sqrt H) ^ 2 * V i) ≤
        ∑ i ∈ Finset.range N, (a i * M i + s i * Real.sqrt H) ^ 2 * V i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro i hi _
      exact mul_nonneg (sq_nonneg _) (hV i (Finset.mem_range.mp hi))
    exact (hle1.trans hle2).trans (deterministic_variance_sum_le a s M V N A_bud K₀ V₀ H
      ha hs hM hV hA_bud hK₀ hV₀ hH_nn hA_sum hK_sup hV_sum)
  have hfreedman := LeanKit.Probability.Freedman.freedman_lemma14_finite ν 𝓕 X_shift hX_shift_ad
    b_tot v_tot q hb_tot_nn hv_tot_nn hq hX_shift_b hX_shift_mean N h_sum_var
  have hbI_all : ∀ᵐ ω ∂ν, ∀ t < N, ‖bI t ω‖ ≤ B t ∧ (ω ∉ I₀ t → bI t ω = 0) := by
    rw [ae_all_iff]
    intro t
    by_cases ht : t < N
    · filter_upwards [hbI_bound t ht] with ω hω _
      exact hω
    · exact Eventually.of_forall (fun _ hlt => (ht hlt).elim)
  have hmY_all : ∀ᵐ ω ∂ν, ∀ t < N, mY t ω ≤ V t ∧ (ω ∉ I₀ t → mY t ω = 0) := by
    rw [ae_all_iff]
    intro t
    by_cases ht : t < N
    · filter_upwards [hmY_bound t ht] with ω hω _
      exact hω
    · exact Eventually.of_forall (fun _ hlt => (ht hlt).elim)
  refine (measure_mono_ae ?_).trans hfreedman
  filter_upwards [hbI_all, hmY_all] with ω hbω hmω
  rintro ⟨ hωℰ, hP0, m, hmN, hωJm, hPm_gt ⟩
  -- Take the smallest `m < N` such that `ω ∈ J m` and `H < P (m + 1) ω`
  classical
  have hex : ∃ m, m < N ∧ ω ∈ J m ∧ H < P (m + 1) ω := ⟨ m, hmN, hωJm, hPm_gt ⟩
  let m₀_idx := Nat.find hex
  have hm₀_spec : m₀_idx < N ∧ ω ∈ J m₀_idx ∧ H < P (m₀_idx + 1) ω := Nat.find_spec hex
  have hm₀_lt : m₀_idx < N := hm₀_spec.1
  have hω_Jm₀ : ω ∈ J m₀_idx := hm₀_spec.2.1
  have hPm₀_gt : H < P (m₀_idx + 1) ω := hm₀_spec.2.2
  have hJ_down : ∀ t ≤ m₀_idx, ω ∈ J t := by
    intro t ht
    obtain ⟨ d, hd ⟩ := Nat.exists_eq_add_of_le ht
    have hω_td : ω ∈ J (t + d) := by simpa only [← hd] using hω_Jm₀
    clear ht hd hm₀_lt hPm₀_gt
    induction d with
    | zero => simpa using hω_td
    | succ d ih =>
      exact ih (hJ_mono (t + d) hω_td)
  have hI₀_up : ∀ t ≤ m₀_idx, ω ∈ I₀ t := by
    intro t ht
    refine ⟨ hP0, ?_ ⟩
    intro j hj
    rcases j with _ | j
    · exact hP0.trans (p0_le_energyThreshold hp₀ hA_bud hK₀ hB₀ hV₀ hJ₀ hq.le)
    · have hj_lt : j < Nat.find hex := by omega
      have hnot := Nat.find_min hex hj_lt
      by_contra hgt
      push_neg at hgt
      exact hnot ⟨ by omega, hJ_down j (by omega), hgt ⟩
  have hI_up : ∀ t ≤ m₀_idx, ω ∈ I t := fun t ht => ⟨ hJ_down t ht, hI₀_up t ht ⟩
  -- Show that at step `m₀_idx + 1 ≤ N`, `partialSum X_shift (m₀_idx + 1) ω > 2 √(v_tot q) + 2 b_tot q`
  refine ⟨ m₀_idx + 1, by omega, ?_ ⟩
  have hrec_m₀ := hrec m₀_idx hm₀_lt ω ⟨ hωℰ, hω_Jm₀ ⟩
  have hsum_decomp :
      (∑ t ∈ Finset.range (m₀_idx + 1), (a t * ‖e t ω‖ ^ 2 + ⟪e t ω, w t ω⟫_ℝ)) =
        (∑ t ∈ Finset.range (m₀_idx + 1), a t * mY t ω) +
        (∑ t ∈ Finset.range (m₀_idx + 1), ⟪bI t ω, wI t ω⟫_ℝ) +
        LeanKit.Probability.MartingaleConcentration.partialSum X_shift (m₀_idx + 1) ω := by
    unfold LeanKit.Probability.MartingaleConcentration.partialSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have ht_le : t ≤ m₀_idx := by have := Finset.mem_range.mp ht; omega
    have ht_lt : t < N := by omega
    have hωIt : ω ∈ I t := hI_up t ht_le
    have hωI₀t : ω ∈ I₀ t := hI₀_up t ht_le
    have heI_eq : eI t ω = e t ω := by
      dsimp [eI]; rw [if_pos ht_lt, Set.indicator_of_mem hωI₀t]
    have hwI_eq : wI t ω = w t ω := by
      dsimp [wI]; rw [if_pos ht_lt, Set.indicator_of_mem hωIt]
    dsimp [X_shift, shiftSeq, X_inc, D_inc, H_inc, uI, Y, aN]
    rw [if_pos ht_lt, heI_eq, hwI_eq, inner_sub_right, real_inner_comm (w t ω) (e t ω),
      real_inner_comm (w t ω) (bI t ω)]
    ring
  have hmean_sq_le : (∑ t ∈ Finset.range (m₀_idx + 1), a t * mY t ω) ≤ A_bud := by
    have hsub : Finset.range (m₀_idx + 1) ⊆ Finset.range N :=
      Finset.range_mono (by omega)
    calc
      (∑ t ∈ Finset.range (m₀_idx + 1), a t * mY t ω)
        ≤ ∑ t ∈ Finset.range (m₀_idx + 1), a t * V t := by
          apply Finset.sum_le_sum
          intro t ht
          have ht_lt : t < N := by have := Finset.mem_range.mp ht; omega
          exact mul_le_mul_of_nonneg_left (hmω t ht_lt).1 (ha t ht_lt)
      _ ≤ ∑ t ∈ Finset.range N, a t * V t := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro t ht _
          have ht_lt := Finset.mem_range.mp ht
          exact mul_nonneg (ha t ht_lt) (hV t ht_lt)
      _ ≤ A_bud := hA_sum
  have hbias_lin_le : (∑ t ∈ Finset.range (m₀_idx + 1), ⟪bI t ω, wI t ω⟫_ℝ) ≤
      Real.sqrt H * B₀ := by
    have hsub : Finset.range (m₀_idx + 1) ⊆ Finset.range N :=
      Finset.range_mono (by omega)
    calc
      (∑ t ∈ Finset.range (m₀_idx + 1), ⟪bI t ω, wI t ω⟫_ℝ)
        ≤ ∑ t ∈ Finset.range (m₀_idx + 1), Real.sqrt H * (s t * B t) := by
          apply Finset.sum_le_sum
          intro t ht
          have ht_lt : t < N := by have := Finset.mem_range.mp ht; omega
          have h1 := real_inner_le_norm (bI t ω) (wI t ω)
          have h2 : ‖bI t ω‖ ≤ B t := (hbω t ht_lt).1
          have h3 : ‖wI t ω‖ ≤ s t * Real.sqrt H := by simpa [sN, ht_lt] using hwI_bound t ω
          have h4 := mul_le_mul h2 h3 (norm_nonneg _) (hB t ht_lt)
          linarith
      _ = Real.sqrt H * ∑ t ∈ Finset.range (m₀_idx + 1), s t * B t :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Real.sqrt H * ∑ t ∈ Finset.range N, s t * B t := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg H)
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro t ht _
          have ht_lt := Finset.mem_range.mp ht
          exact mul_nonneg (hs t ht_lt) (hB t ht_lt)
      _ ≤ Real.sqrt H * B₀ := mul_le_mul_of_nonneg_left hB_sum (Real.sqrt_nonneg H)
  have h_closure :
      (p₀ + A_bud + 2 * Real.sqrt (K₀ * A_bud * q) + 2 * K₀ * q) +
      Real.sqrt H * B₀ + Real.sqrt H * (2 * Real.sqrt (V₀ * q) + 2 * J₀ * q) ≤ H := by
    have hc := energy_closure_ineq hp₀ hA_bud hK₀ hB₀ hV₀ hJ₀ hq.le
    unfold energyC energyD at hc
    change (p₀ + A_bud + 2 * Real.sqrt (K₀ * A_bud * q) + 2 * K₀ * q) +
      Real.sqrt H * (B₀ + 2 * Real.sqrt (V₀ * q) + 2 * J₀ * q) ≤ H at hc
    linarith [show Real.sqrt H * (B₀ + 2 * Real.sqrt (V₀ * q) + 2 * J₀ * q) =
      Real.sqrt H * B₀ + Real.sqrt H * (2 * Real.sqrt (V₀ * q) + 2 * J₀ * q) by ring]
  have h_thresh_id : 2 * Real.sqrt (v_tot * q) + 2 * b_tot * q =
      (2 * Real.sqrt (K₀ * A_bud * q) + 2 * K₀ * q) +
      Real.sqrt H * (2 * Real.sqrt (V₀ * q) + 2 * J₀ * q) := by
    dsimp [v_tot, b_tot]
    have hsqrt_v : Real.sqrt ((Real.sqrt (K₀ * A_bud) + Real.sqrt (H * V₀)) ^ 2 * q) =
        (Real.sqrt (K₀ * A_bud) + Real.sqrt (H * V₀)) * Real.sqrt q := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have hsqrt_KA : Real.sqrt (K₀ * A_bud * q) = Real.sqrt (K₀ * A_bud) * Real.sqrt q :=
      Real.sqrt_mul (mul_nonneg hK₀ hA_bud) q
    have hsqrt_HV : Real.sqrt (H * V₀) * Real.sqrt q = Real.sqrt H * Real.sqrt (V₀ * q) := by
      rw [Real.sqrt_mul hH_nn V₀, Real.sqrt_mul hV₀ q]
      ring
    rw [hsqrt_v, hsqrt_KA]
    linarith [hsqrt_HV]
  linarith

/-- Infinite-horizon version of `lem:energy-budget` (`N = ∞`), obtained by
monotone union continuity (`LeanKit.Probability.TimeUniform.measure_iUnion_le_of_monotone`). -/
theorem energy_budget_infinite (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    (P : ℕ → Ω → ℝ) (hP : Adapted 𝓕 P) (hP_nn : ∀ t ω, 0 ≤ P t ω)
    (J : ℕ → Set Ω) (hJ_meas : ∀ t, MeasurableSet[𝓕 t] (J t))
    (hJ_mono : ∀ t, J (t + 1) ⊆ J t) (ℰ : Set Ω)
    (e w : ℕ → Ω → E)
    (he_meas : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (e t))
    (he_int : ∀ t, Integrable (e t) ν)
    (he_sq_int : ∀ t, Integrable (fun ω => ‖e t ω‖ ^ 2) ν)
    (he_supp : ∀ t ω, ω ∉ J t → e t ω = 0)
    (hw_meas : ∀ t, StronglyMeasurable[𝓕 t] (w t))
    (a s B V M U : ℕ → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hs : ∀ t, 0 ≤ s t)
    (hB : ∀ t, 0 ≤ B t) (hV : ∀ t, 0 ≤ V t)
    (hM : ∀ t, 0 ≤ M t) (hU : ∀ t, 0 ≤ U t)
    (hw_bound : ∀ t, ∀ ω ∈ J t, ‖w t ω‖ ≤ s t * Real.sqrt (P t ω))
    (hrec : ∀ m, ∀ ω ∈ ℰ ∩ J m,
      P (m + 1) ω ≤ P 0 ω +
        ∑ t ∈ Finset.range (m + 1), (a t * ‖e t ω‖ ^ 2 + ⟪e t ω, w t ω⟫_ℝ))
    (hBias : ∀ t, ∀ᵐ ω ∂ν, ‖ν[e t | 𝓕 t] ω‖ ≤ B t)
    (hVar : ∀ t, ν[fun ω => ‖e t ω‖ ^ 2 | 𝓕 t] ≤ᵐ[ν] fun _ => V t)
    (hRange : ∀ t, ∀ᵐ ω ∂ν, ‖e t ω‖ ≤ M t)
    (hCentRange : ∀ t, ∀ᵐ ω ∂ν, ‖e t ω - ν[e t | 𝓕 t] ω‖ ≤ U t)
    (p₀ A_bud K₀ B₀ V₀ J₀ q : ℝ)
    (hp₀ : 0 ≤ p₀) (hA_bud : 0 ≤ A_bud) (hK₀ : 0 ≤ K₀)
    (hB₀ : 0 ≤ B₀) (hV₀ : 0 ≤ V₀) (hJ₀ : 0 ≤ J₀) (hq : 0 < q)
    (hA_sum : ∀ N, ∑ t ∈ Finset.range N, a t * V t ≤ A_bud)
    (hK_sup : ∀ t, a t * (M t) ^ 2 ≤ K₀)
    (hB_sum : ∀ N, ∑ t ∈ Finset.range N, s t * B t ≤ B₀)
    (hV_sum : ∀ N, ∑ t ∈ Finset.range N, (s t) ^ 2 * V t ≤ V₀)
    (hJ_sup : ∀ t, s t * U t ≤ J₀) :
    ν {ω ∈ ℰ | P 0 ω ≤ p₀ ∧ ∃ m : ℕ, ω ∈ J m ∧
        energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q < P (m + 1) ω} ≤
      ENNReal.ofReal (Real.exp (-q)) := by
  let E_fin : ℕ → Set Ω := fun N =>
    {ω ∈ ℰ | P 0 ω ≤ p₀ ∧ ∃ m < N, ω ∈ J m ∧
      energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q < P (m + 1) ω}
  have hmono : Monotone E_fin := by
    intro N₁ N₂ hle ω hω
    rcases hω with ⟨ hℰ, hp0, m, hm, hJm, hgt ⟩
    exact ⟨ hℰ, hp0, m, lt_of_lt_of_le hm hle, hJm, hgt ⟩
  have hunion : {ω ∈ ℰ | P 0 ω ≤ p₀ ∧ ∃ m : ℕ, ω ∈ J m ∧
      energyThreshold p₀ A_bud K₀ B₀ V₀ J₀ q < P (m + 1) ω} = ⋃ N : ℕ, E_fin N := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, E_fin]
    constructor
    · rintro ⟨ hℰ, hp0, m, hJm, hgt ⟩
      exact ⟨ m + 1, hℰ, hp0, m, Nat.lt_succ_self m, hJm, hgt ⟩
    · rintro ⟨ N, hℰ, hp0, m, _, hJm, hgt ⟩
      exact ⟨ hℰ, hp0, m, hJm, hgt ⟩
  rw [hunion]
  apply LeanKit.Probability.TimeUniform.measure_iUnion_le_of_monotone ν hmono
  intro N
  exact energy_budget_finite ν 𝓕 N P hP hP_nn J hJ_meas hJ_mono ℰ e w
    (fun t _ => he_meas t) (fun t _ => he_int t) (fun t _ => he_sq_int t)
    (fun t _ => he_supp t) (fun t _ => hw_meas t)
    a s B V M U (fun t _ => ha t) (fun t _ => hs t) (fun t _ => hB t)
    (fun t _ => hV t) (fun t _ => hM t) (fun t _ => hU t)
    (fun t _ => hw_bound t) (fun m _ => hrec m)
    (fun t _ => hBias t) (fun t _ => hVar t) (fun t _ => hRange t) (fun t _ => hCentRange t)
    p₀ A_bud K₀ B₀ V₀ J₀ q hp₀ hA_bud hK₀ hB₀ hV₀ hJ₀ hq
    (hA_sum N) (fun t _ => hK_sup t) (hB_sum N) (hV_sum N) (fun t _ => hJ_sup t)

end
end ClippedSGD.EnergyBudget
