import LeanKit.Probability.MartingaleConcentration
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Log

/-!
# Time-Uniform Martingale Inequalities and Dyadic Peeling (`LeanKit.Probability.TimeUniform`)

Contains:
- `ville_finite_expectation`: finite-horizon Ville's inequality for nonnegative supermartingales
  with general initial expectation `∫ ω, Z 0 ω ∂ν / a`.
- `ville_infinite`: infinite-horizon Ville's inequality
  `ν {ω | ∃ t : ℕ, a ≤ Z t ω} ≤ ENNReal.ofReal ((∫ ω, Z 0 ω ∂ν) / a)`.
- `ville_infinite_one`: infinite-horizon Ville's inequality when `∫ ω, Z 0 ω ∂ν ≤ 1`.
- Dyadic block partitioning `[2^k, 2^(k+1))` and general time-uniform peeling union bounds:
  `dyadicBlock`, `mem_dyadicBlock_log`, `exists_mem_dyadicBlock`, `iUnion_dyadicBlock`,
  `peeling_dyadic_measure_le`, `peeling_dyadic_ofReal_le`, `peeling_dyadic_envelope`,
  `countable_horizon_union_ofReal`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

namespace LeanKit.Probability.TimeUniform
noncomputable section

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]

/-- Finite-horizon Ville's inequality for a nonnegative supermartingale with general initial expectation. -/
theorem ville_finite_expectation (𝓕 : Filtration ℕ m₀) (Z : ℕ → Ω → ℝ)
    (hZ : Supermartingale Z 𝓕 ν) (hpos : ∀ n ω, 0 ≤ Z n ω)
    (a : ℝ) (ha : 0 < a) (T : ℕ) :
    ν {ω | ∃ n ≤ T, a ≤ Z n ω} ≤ ENNReal.ofReal ((∫ ω, Z 0 ω ∂ν) / a) := by
  let τ := hitting Z (Ici a) 0 T
  have hτ : IsStoppingTime 𝓕 τ := hitting_isStoppingTime hZ.adapted measurableSet_Ici
  have hτT : ∀ ω, τ ω ≤ T := hitting_le
  have hi : Integrable (stoppedValue Z τ) ν :=
    integrable_stoppedValue ℕ hτ hZ.integrable hτT
  have he := hZ.neg.expected_stoppedValue_mono (isStoppingTime_const 𝓕 0) hτ
    (fun _ => Nat.zero_le _) hτT
  have he' : ∫ ω, stoppedValue Z τ ω ∂ν ≤ ∫ ω, Z 0 ω ∂ν := by
    simpa only [stoppedValue_const, stoppedValue, Pi.neg_apply, integral_neg, neg_le_neg_iff] using he
  have hp : 0 ≤ᵐ[ν] (fun ω => (1 / a) * stoppedValue Z τ ω) :=
    Eventually.of_forall (fun ω => mul_nonneg (one_div_pos.mpr ha).le (hpos _ _))
  have hm := (hi.const_mul (1 / a)).measure_le_integral hp (s := {ω | ∃ n ≤ T, a ≤ Z n ω}) (by
    intro ω hω
    have hh : stoppedValue Z τ ω ∈ Ici a := stoppedValue_hitting_mem (by
      obtain ⟨n, hn, hzn⟩ := hω
      exact ⟨n, ⟨Nat.zero_le _, hn⟩, hzn⟩)
    change a ≤ stoppedValue Z τ ω at hh
    have hh' : 1 ≤ stoppedValue Z τ ω / a := (one_le_div ha).mpr hh
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul, mul_one] using hh')
  apply hm.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left he' (one_div_pos.mpr ha).le
  linarith [hh, show (1 / a) * ∫ ω, Z 0 ω ∂ν = (∫ ω, Z 0 ω ∂ν) / a by ring]

omit [IsProbabilityMeasure ν] in
/-- Monotone continuity from below for upper bounds on a countable increasing union of events. -/
theorem measure_iUnion_le_of_monotone {E : ℕ → Set Ω} (hmono : Monotone E) {c : ℝ≥0∞}
    (hbound : ∀ T, ν (E T) ≤ c) : ν (⋃ T : ℕ, E T) ≤ c :=
  le_of_tendsto' (MeasureTheory.tendsto_measure_iUnion_atTop hmono) hbound

/-- Infinite-horizon Ville's inequality for a nonnegative supermartingale:
`ℙ(∃ t : ℕ, Z_t ≥ a) ≤ 𝔼[Z_0] / a`. -/
theorem ville_infinite (𝓕 : Filtration ℕ m₀) (Z : ℕ → Ω → ℝ)
    (hZ : Supermartingale Z 𝓕 ν) (hpos : ∀ n ω, 0 ≤ Z n ω)
    (a : ℝ) (ha : 0 < a) :
    ν {ω | ∃ t : ℕ, a ≤ Z t ω} ≤ ENNReal.ofReal ((∫ ω, Z 0 ω ∂ν) / a) := by
  let E : ℕ → Set Ω := fun T => {ω | ∃ n ≤ T, a ≤ Z n ω}
  have hmono : Monotone E := by
    intro T₁ T₂ hT ω ⟨n, hn, hzn⟩
    exact ⟨n, hn.trans hT, hzn⟩
  have hunion : {ω | ∃ t : ℕ, a ≤ Z t ω} = ⋃ T : ℕ, E T := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, E]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, t, le_rfl, ht⟩, fun ⟨_, n, _, hn⟩ => ⟨n, hn⟩⟩
  rw [hunion]
  exact measure_iUnion_le_of_monotone ν hmono
    (fun T => ville_finite_expectation ν 𝓕 Z hZ hpos a ha T)

/-- Infinite-horizon Ville's inequality for a nonnegative supermartingale with `𝔼[Z_0] ≤ 1`. -/
theorem ville_infinite_one (𝓕 : Filtration ℕ m₀) (Z : ℕ → Ω → ℝ)
    (hZ : Supermartingale Z 𝓕 ν) (hpos : ∀ n ω, 0 ≤ Z n ω)
    (hinit : ∫ ω, Z 0 ω ∂ν ≤ 1) (a : ℝ) (ha : 0 < a) :
    ν {ω | ∃ t : ℕ, a ≤ Z t ω} ≤ ENNReal.ofReal (1 / a) := by
  refine (ville_infinite ν 𝓕 Z hZ hpos a ha).trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right hinit ha.le

section Peeling

/-- The `k`-th dyadic time block `[2^k, 2^(k+1))`. -/
def dyadicBlock (k : ℕ) : Set ℕ := {t : ℕ | 2 ^ k ≤ t ∧ t < 2 ^ (k + 1)}

/-- Every positive integer `t ≥ 1` belongs to the dyadic block `k = Nat.log 2 t`. -/
lemma mem_dyadicBlock_log {t : ℕ} (ht : 1 ≤ t) : t ∈ dyadicBlock (Nat.log 2 t) := by
  exact ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by decide) t⟩

/-- Every positive integer `t ≥ 1` belongs to some dyadic block `[2^k, 2^(k+1))`. -/
lemma exists_mem_dyadicBlock {t : ℕ} (ht : 1 ≤ t) : ∃ k : ℕ, t ∈ dyadicBlock k :=
  ⟨Nat.log 2 t, mem_dyadicBlock_log ht⟩

/-- The union of all dyadic blocks `[2^k, 2^(k+1))` is `[1, ∞)`. -/
theorem iUnion_dyadicBlock : (⋃ k : ℕ, dyadicBlock k) = {t : ℕ | 1 ≤ t} := by
  ext t
  simp only [mem_iUnion, dyadicBlock, mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, _⟩
    exact (Nat.one_le_two_pow).trans hk
  · intro ht
    exact exists_mem_dyadicBlock ht

/-- General dyadic peeling union bound: the measure of an all-time failure event over `t ≥ 1`
is bounded by the sum of measures over dyadic blocks `[2^k, 2^(k+1))`. -/
theorem peeling_dyadic_measure_le (Bad : ℕ → Ω → Prop) :
    ν {ω | ∃ t ≥ 1, Bad t ω} ≤
      ∑' k : ℕ, ν {ω | ∃ t, 2 ^ k ≤ t ∧ t < 2 ^ (k + 1) ∧ Bad t ω} := by
  have hsub : {ω | ∃ t ≥ 1, Bad t ω} ⊆
      ⋃ k : ℕ, {ω | ∃ t, 2 ^ k ≤ t ∧ t < 2 ^ (k + 1) ∧ Bad t ω} := by
    rintro ω ⟨t, ht, hbad⟩
    obtain ⟨k, hk1, hk2⟩ := exists_mem_dyadicBlock ht
    exact mem_iUnion.mpr ⟨k, t, hk1, hk2, hbad⟩
  exact (measure_mono hsub).trans (measure_iUnion_le _)

/-- Dyadic peeling with real summable block failure budgets `δ k`:
if each dyadic block `[2^k, 2^(k+1))` fails with probability at most `δ k`,
then the time-uniform failure probability over all `t ≥ 1` is at most `∑' k, δ k`. -/
theorem peeling_dyadic_ofReal_le (Bad : ℕ → Ω → Prop) (δ : ℕ → ℝ)
    (hδ_nonneg : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (hblock : ∀ k, ν {ω | ∃ t, 2 ^ k ≤ t ∧ t < 2 ^ (k + 1) ∧ Bad t ω} ≤ ENNReal.ofReal (δ k)) :
    ν {ω | ∃ t ≥ 1, Bad t ω} ≤ ENNReal.ofReal (∑' k : ℕ, δ k) := by
  calc
    ν {ω | ∃ t ≥ 1, Bad t ω} ≤
        ∑' k : ℕ, ν {ω | ∃ t, 2 ^ k ≤ t ∧ t < 2 ^ (k + 1) ∧ Bad t ω} :=
      peeling_dyadic_measure_le ν Bad
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (δ k) := ENNReal.tsum_le_tsum hblock
    _ = ENNReal.ofReal (∑' k : ℕ, δ k) := (ENNReal.ofReal_tsum_of_nonneg hδ_nonneg hδ_sum).symm

/-- Dyadic peeling for a real process `X` against a time-varying boundary `B : ℕ → ℝ`
lower-bounded on each dyadic block `[2^k, 2^(k+1))` by a block threshold `B_block k`. -/
theorem peeling_dyadic_envelope (X : ℕ → Ω → ℝ) (B B_block δ : ℕ → ℝ)
    (hB : ∀ k t, 2 ^ k ≤ t → t < 2 ^ (k + 1) → B_block k ≤ B t)
    (hδ_nonneg : ∀ k, 0 ≤ δ k) (hδ_sum : Summable δ)
    (hblock : ∀ k, ν {ω | ∃ t, 2 ^ k ≤ t ∧ t < 2 ^ (k + 1) ∧ B_block k < X t ω} ≤
      ENNReal.ofReal (δ k)) :
    ν {ω | ∃ t ≥ 1, B t < X t ω} ≤ ENNReal.ofReal (∑' k : ℕ, δ k) := by
  apply peeling_dyadic_ofReal_le ν (fun t ω => B t < X t ω) δ hδ_nonneg hδ_sum
  intro k
  refine (measure_mono ?_).trans (hblock k)
  rintro ω ⟨t, hk1, hk2, hX⟩
  exact ⟨t, hk1, hk2, (hB k t hk1 hk2).trans_lt hX⟩

/-- Countable-horizon union bound with summable real failure budgets `δ T`. -/
theorem countable_horizon_union_ofReal (Bad : ℕ → Set Ω) (δ : ℕ → ℝ)
    (hδ_nonneg : ∀ T, 0 ≤ δ T) (hδ_sum : Summable δ)
    (hbound : ∀ T, ν (Bad T) ≤ ENNReal.ofReal (δ T)) :
    ν (⋃ T : ℕ, Bad T) ≤ ENNReal.ofReal (∑' T : ℕ, δ T) := by
  calc
    ν (⋃ T : ℕ, Bad T) ≤ ∑' T : ℕ, ν (Bad T) := measure_iUnion_le Bad
    _ ≤ ∑' T : ℕ, ENNReal.ofReal (δ T) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (∑' T : ℕ, δ T) := (ENNReal.ofReal_tsum_of_nonneg hδ_nonneg hδ_sum).symm

end Peeling

end
end LeanKit.Probability.TimeUniform
