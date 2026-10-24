import ClippedSGD.Bernoulli
import Mathlib.Tactic.FunProp

/-! Sample laws of the momentum instance and probability estimates on a finite prefix. -/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace ClippedSGD.MomentumProbability

noncomputable section

/-- The law of `N` independent samples. -/
def iid {α : Type*} [MeasurableSpace α] (N : ℕ) (ν : Measure α) :
    Measure (Fin N → α) := Measure.pi (fun _ => ν)

instance {α : Type*} [MeasurableSpace α] (N : ℕ) (ν : Measure α)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (iid N ν) := by
  unfold iid
  infer_instance

lemma cylinder {α : Type*} [MeasurableSpace α] {N : ℕ} (ν : Measure α)
    [IsProbabilityMeasure ν] (i : Fin N) (s : Set α) :
    iid N ν {ω | ω i ∈ s} = ν s := by
  classical
  have he : {ω : Fin N → α | ω i ∈ s} =
      univ.pi (fun j => if j = i then s else univ) := by
    ext ω
    simp only [mem_setOf_eq, mem_pi, mem_univ, true_implies]
    constructor
    · intro h j
      by_cases hj : j = i <;> simp [hj, h]
    · intro h
      simpa using h i
  rw [he, iid, Measure.pi_pi]
  simp only [apply_ite, measure_univ]
  simp

lemma two_cylinders {α : Type*} [MeasurableSpace α] {N : ℕ} (ν : Measure α)
    [IsProbabilityMeasure ν] (i j : Fin N) (hij : i ≠ j) (s t : Set α) :
    iid N ν {ω | ω i ∈ s ∧ ω j ∈ t} = ν s * ν t := by
  classical
  have he : {ω : Fin N → α | ω i ∈ s ∧ ω j ∈ t} =
      univ.pi (fun k => if k = i then s else if k = j then t else univ) := by
    ext ω
    simp only [mem_setOf_eq, mem_pi, mem_univ, true_implies]
    constructor
    · rintro ⟨hs, ht⟩ k
      by_cases hi : k = i
      · simp [hi, hs]
      · by_cases hj : k = j <;> simp [hi, hj, ht, Ne.symm hij]
    · intro h
      exact ⟨by simpa using h i, by simpa [Ne.symm hij] using h j⟩
  rw [he, iid, Measure.pi_pi]
  have hf : (fun k : Fin N => ν (if k = i then s else if k = j then t else univ)) =
      (fun k => (if k = i then ν s else 1) * (if k = j then ν t else 1)) := by
    funext k
    by_cases hi : k = i
    · subst k; simp [hij]
    · by_cases hj : k = j <;> simp [hi, hj, Ne.symm hij]
  rw [hf, Finset.prod_mul_distrib]
  simp

/-- A sample has a rare bit, a uniform auxiliary coordinate and a symmetric sign. -/
abbrev Sample (d : ℕ) := Bool × (Fin (d + 1) × Bool)

def coordinateLaw (d : ℕ) : Measure (Fin (d + 1)) :=
  (d + 1 : ℝ≥0∞)⁻¹ • Measure.count

instance (d : ℕ) : IsProbabilityMeasure (coordinateLaw d) := by
  constructor
  simp [coordinateLaw, Measure.smul_apply, Measure.count_univ, ENNReal.inv_mul_cancel]

def sampleLaw (d : ℕ) (π : ℝ) (hπ : π ≤ 1) : Measure (Sample d) :=
  (ClippedSGD.Lower.bernoulliLaw π hπ).prod
    ((coordinateLaw d).prod (ClippedSGD.Lower.bernoulliLaw (1 / 2) (by norm_num)))

instance (d : ℕ) (π : ℝ) (hπ : π ≤ 1) : IsProbabilityMeasure (sampleLaw d π hπ) := by
  unfold sampleLaw
  infer_instance

lemma coordinateLaw_singleton (d : ℕ) (j : Fin (d + 1)) :
    (coordinateLaw d).real {j} = 1 / (d + 1 : ℝ) := by
  simp [coordinateLaw, measureReal_def, Measure.smul_apply, ENNReal.toReal_inv, ENNReal.toReal_add]

lemma sample_rare_mass (d : ℕ) {π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    (sampleLaw d π hπ1).real {a | a.1 = true} = π := by
  have he : {a : Sample d | a.1 = true} = {true} ×ˢ univ := by ext a; simp
  rw [he, sampleLaw, measureReal_prod_prod]
  simp [ClippedSGD.Lower.bernoulliLaw, measureReal_def,
    PMF.toMeasure_apply_singleton, PMF.bernoulli_apply, ENNReal.toReal_ofReal hπ0]

lemma sample_coordinate_mass (d : ℕ) (π : ℝ) (hπ : π ≤ 1) (j : Fin (d + 1)) :
    (sampleLaw d π hπ).real {a | a.2.1 = j} = 1 / (d + 1 : ℝ) := by
  have he : {a : Sample d | a.2.1 = j} = univ ×ˢ ({j} ×ˢ univ) := by ext a; simp
  rw [he, sampleLaw, measureReal_prod_prod, measureReal_prod_prod]
  rw [measureReal_univ_eq_one, measureReal_univ_eq_one, one_mul, mul_one]
  exact coordinateLaw_singleton d j

lemma iid_rare_mass {N : ℕ} (d : ℕ) {π : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (i : Fin N) :
    (iid N (sampleLaw d π hπ1)).real {ω | (ω i).1 = true} = π := by
  change ((iid N (sampleLaw d π hπ1)) {ω | ω i ∈ {a | a.1 = true}}).toReal = _
  rw [cylinder]
  exact sample_rare_mass d hπ0 hπ1

lemma iid_coordinate_pair_mass {N : ℕ} (d : ℕ) (π : ℝ) (hπ : π ≤ 1)
    (i j : Fin N) (hij : i ≠ j) (k : Fin (d + 1)) :
    (iid N (sampleLaw d π hπ)).real {ω | (ω i).2.1 = k ∧ (ω j).2.1 = k} =
      (1 / (d + 1 : ℝ)) ^ 2 := by
  change ((iid N (sampleLaw d π hπ)) {ω | ω i ∈ {a | a.2.1 = k} ∧ ω j ∈ {a | a.2.1 = k}}).toReal = _
  rw [two_cylinders _ i j hij, ENNReal.toReal_mul]
  change (sampleLaw d π hπ).real {a | a.2.1 = k} *
    (sampleLaw d π hπ).real {a | a.2.1 = k} = _
  rw [sample_coordinate_mass]
  ring

/-- A collision between two different fresh coordinate draws has probability at
most the reciprocal dimension. -/
lemma collision_pair_le {N : ℕ} (d : ℕ) (π : ℝ) (hπ : π ≤ 1)
    (i j : Fin N) (hij : i ≠ j) :
    (iid N (sampleLaw d π hπ)).real {ω | (ω i).2.1 = (ω j).2.1} ≤
      1 / (d + 1 : ℝ) := by
  have hsub : {ω : Fin N → Sample d | (ω i).2.1 = (ω j).2.1} ⊆
      ⋃ k : Fin (d + 1), {ω | (ω i).2.1 = k ∧ (ω j).2.1 = k} := by
    intro ω hω
    exact mem_iUnion.mpr ⟨(ω i).2.1, rfl, hω.symm⟩
  calc
    _ ≤ (iid N (sampleLaw d π hπ)).real
        (⋃ k : Fin (d + 1), {ω | (ω i).2.1 = k ∧ (ω j).2.1 = k}) :=
      measureReal_mono hsub
    _ ≤ ∑ k : Fin (d + 1), (iid N (sampleLaw d π hπ)).real
        {ω | (ω i).2.1 = k ∧ (ω j).2.1 = k} := measureReal_iUnion_fintype_le _
    _ = 1 / (d + 1 : ℝ) := by
      simp only [iid_coordinate_pair_mass d π hπ i j hij, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- The probability that two of `N` samples draw the same coordinate is at most
`N²/(d+1)`. -/
lemma collision_probability_le {N : ℕ} (d : ℕ) (π : ℝ) (hπ : π ≤ 1) :
    (iid N (sampleLaw d π hπ)).real
      {ω | ∃ i j : Fin N, i ≠ j ∧ (ω i).2.1 = (ω j).2.1} ≤
        (N : ℝ) ^ 2 / (d + 1 : ℝ) := by
  classical
  have he : {ω : Fin N → Sample d | ∃ i j : Fin N, i ≠ j ∧ (ω i).2.1 = (ω j).2.1} =
      ⋃ i : Fin N, ⋃ j : Fin N, {ω | i ≠ j ∧ (ω i).2.1 = (ω j).2.1} := by
    ext ω; simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin N, (iid N (sampleLaw d π hπ)).real
        (⋃ j : Fin N, {ω | i ≠ j ∧ (ω i).2.1 = (ω j).2.1}) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (1 / (d + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      refine (measureReal_iUnion_fintype_le _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j; simp; positivity
      · simpa [hij] using collision_pair_le d π hπ i j hij
    _ = (N : ℝ) ^ 2 / (d + 1 : ℝ) := by simp; ring

/-- The expected weighted number of rare arrivals is `π ∑ w i`. -/
lemma weighted_rare_expectation {N : ℕ} (d : ℕ) {π : ℝ}
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (w : Fin N → ℝ) :
    (∫ ω, ∑ i : Fin N, (if (ω i).1 = true then w i else 0)
      ∂iid N (sampleLaw d π hπ1)) = π * ∑ i : Fin N, w i := by
  classical
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  have he (i : Fin N) :
      (fun ω : Fin N → Sample d => if (ω i).1 = true then w i else 0) =
        {ω | (ω i).1 = true}.indicator (fun _ => w i) := by
    funext ω
    simp [Set.indicator_apply]
  simp_rw [he, integral_indicator_const _ (MeasurableSet.of_discrete),
    smul_eq_mul, iid_rare_mass d hπ0 hπ1]
  rw [Finset.mul_sum]

/-- If a nonnegative integrable `Z` is at least `c` on `E`, then `c P(E) ≤ E[Z]`. -/
lemma event_progress_budget {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (E : Set Ω) (hE : MeasurableSet E)
    (Z : Ω → ℝ) (hZ : Integrable Z ν) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (c : ℝ) (hprogress : ∀ ω ∈ E, c ≤ Z ω) :
    c * ν.real E ≤ ∫ ω, Z ω ∂ν := by
  have hle : E.indicator (fun _ => c) ≤ Z := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [hω] using hprogress ω hω
    · simpa [hω] using hZ0 ω
  have hi : Integrable (E.indicator (fun _ : Ω => c)) ν :=
    (integrable_const c).indicator hE
  have hh := integral_mono hi hZ hle
  rw [integral_indicator_const c hE, smul_eq_mul] at hh
  simpa only [mul_comm] using hh

section Seed
variable {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

lemma seed_event_mass {N : ℕ} (d : ℕ) (π : ℝ) (hπ : π ≤ 1)
    (E : Set (Fin N → Sample d)) :
    ((iid N (sampleLaw d π hπ)).prod ν).real {q | q.1 ∈ E} =
      (iid N (sampleLaw d π hπ)).real E := by
  have he : {q : (Fin N → Sample d) × S | q.1 ∈ E} = E ×ˢ univ := by ext q; simp
  rw [he, measureReal_prod_prod, measureReal_univ_eq_one, mul_one]

lemma weighted_rare_integrable {N : ℕ} (d : ℕ) (π : ℝ) (hπ : π ≤ 1)
    (w : Fin N → ℝ) :
    Integrable (fun q : (Fin N → Sample d) × S =>
      ∑ i : Fin N, if (q.1 i).1 = true then w i else 0)
      ((iid N (sampleLaw d π hπ)).prod ν) := by
  have hi : Integrable (fun ω : Fin N → Sample d =>
      ∑ i : Fin N, if (ω i).1 = true then w i else 0) (iid N (sampleLaw d π hπ)) :=
    Integrable.of_finite
  simpa using hi.mul_prod (integrable_const (1 : ℝ) (μ := ν))

lemma weighted_rare_seed_expectation {N : ℕ} (d : ℕ) {π : ℝ}
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (w : Fin N → ℝ) :
    (∫ q : (Fin N → Sample d) × S,
      ∑ i : Fin N, if (q.1 i).1 = true then w i else 0
      ∂(iid N (sampleLaw d π hπ1)).prod ν) = π * ∑ i : Fin N, w i := by
  rw [integral_prod _ (weighted_rare_integrable ν d π hπ1 w)]
  dsimp only
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  exact weighted_rare_expectation d hπ0 hπ1 w

end Seed
end
end ClippedSGD.MomentumProbability
