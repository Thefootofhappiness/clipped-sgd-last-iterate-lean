import ClippedSGD.Resolvent

/-! The orthogonal pulse lemma, proved by projecting the heavy-ball recursion onto a test
direction chosen after the whole finite path is fixed. -/

open Finset
open scoped BigOperators InnerProductSpace

namespace ClippedSGD.ProjectionPulse

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pythagoras for a finite family of pairwise orthogonal vectors. -/
theorem response_energy {ι : Type*} (s : Finset ι) (z : ι → E) (k : ι → ℝ)
    (orth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪z i, z j⟫_ℝ = 0) :
    ‖∑ i ∈ s, k i • z i‖ ^ 2 = ∑ i ∈ s, k i ^ 2 * ‖z i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]
    ring
  · intro j hj hji
    rw [orth j hj i hi hji]
    ring
  · exact fun h => False.elim (h hi)

/-- The test direction of the projection argument. -/
def direction (z : ℕ → E) (h : ℕ → ℝ) (τ t : ℕ) (A : ℝ) : E :=
  (1 / A) • z τ + ∑ j ∈ Ioo τ t, (h j / ‖z j‖ ^ 2) • z j

theorem noise_projection (z : ℕ → E) (h : ℕ → ℝ) (τ t : ℕ) (A : ℝ)
    (hτ : τ < t) (hA : A = ‖z τ‖) (hA0 : 0 < A)
    (orth : ∀ i < t, ∀ j < t, i ≠ j → ⟪z i, z j⟫_ℝ = 0)
    (nonzero : ∀ j < t, ‖z j‖ ≠ 0)
    (hbefore : ∀ j ≤ τ, h j = 0) (j : ℕ) (hjt : j < t) :
    ⟪z j, direction z h τ t A⟫_ℝ = h j + if j = τ then A else 0 := by
  classical
  have hs : (∑ i ∈ Ioo τ t, (h i / ‖z i‖ ^ 2) * ⟪z j, z i⟫_ℝ) =
      if j ∈ Ioo τ t then h j else 0 := by
    rw [sum_eq_single j]
    · by_cases hw : j ∈ Ioo τ t
      · simp only [if_pos hw, real_inner_self_eq_norm_sq]
        exact div_mul_cancel₀ _ (pow_ne_zero 2 (nonzero j hjt))
      · simp only [if_neg hw]
        have hb : j ≤ τ := by
          have : ¬ (τ < j ∧ j < t) := by simpa only [mem_Ioo] using hw
          omega
        rw [hbefore j hb, zero_div, zero_mul]
    · intro i hi hji
      rw [orth j hjt i (mem_Ioo.mp hi).2 (Ne.symm hji), mul_zero]
    · intro hw
      have hb : j ≤ τ := by
        have : ¬ (τ < j ∧ j < t) := by simpa only [mem_Ioo] using hw
        omega
      rw [hbefore j hb, zero_div, zero_mul]
  simp only [direction, inner_add_right, inner_smul_right, inner_sum]
  rw [hs]
  by_cases he : j = τ
  · subst j
    rw [real_inner_self_eq_norm_sq, ← hA]
    simp only [mem_Ioo, lt_self_iff_false, false_and, if_false, if_true,
      hbefore τ le_rfl, zero_add, add_zero]
    field_simp
    ring
  · rw [orth j hjt τ hτ he]
    simp only [mul_zero, zero_add, if_neg he, add_zero]
    by_cases hw : j ∈ Ioo τ t
    · simp [hw]
    · have hb : j ≤ τ := by
        have : ¬ (τ < j ∧ j < t) := by simpa only [mem_Ioo] using hw
        omega
      simp [hw, hbefore j hb]

theorem direction_energy (z : ℕ → E) (h : ℕ → ℝ) (τ t : ℕ) (A : ℝ)
    (hτ : τ < t) (hA : A = ‖z τ‖) (hA0 : 0 < A)
    (orth : ∀ i < t, ∀ j < t, i ≠ j → ⟪z i, z j⟫_ℝ = 0)
    (nonzero : ∀ j < t, ‖z j‖ ≠ 0) :
    ‖direction z h τ t A‖ ^ 2 =
      1 + ∑ j ∈ Ioo τ t, h j ^ 2 / ‖z j‖ ^ 2 := by
  have hcross : ⟪(1 / A) • z τ,
      ∑ j ∈ Ioo τ t, (h j / ‖z j‖ ^ 2) • z j⟫_ℝ = 0 := by
    simp only [inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
    apply sum_eq_zero
    intro j hj
    rw [orth τ hτ j (mem_Ioo.mp hj).2 (ne_of_lt (mem_Ioo.mp hj).1), mul_zero,
      mul_zero]
  rw [direction, norm_add_sq_real, hcross, mul_zero, add_zero]
  have hunit : ‖(1 / A) • z τ‖ ^ 2 = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hA0), ← hA]
    field_simp
  rw [hunit, response_energy]
  · congr 1
    apply sum_congr rfl
    intro j hj
    have hn := nonzero j (mem_Ioo.mp hj).2
    field_simp
    ring
  · intro i hi j hj hij
    exact orth i (mem_Ioo.mp hi).2 j (mem_Ioo.mp hj).2 hij

/-- The projection of the recursion onto the test direction. -/
theorem trajectory_projection (β c η h k : ℕ → ℝ) (v y z : ℕ → E)
    (w : E) (t τ : ℕ) (A : ℝ)
    (vzero : v 0 = 0) (yzero : y 0 = 0) (hzero : h 0 = 0) (kzero : k 0 = 0)
    (vstep : ∀ j < t, v (j + 1) = β j • v j + c j • (y j + z j))
    (ystep : ∀ j < t, y (j + 1) = y j - η j • v (j + 1))
    (kstep : ∀ j < t, k (j + 1) = β j * k j + c j * (if j = τ then A else 0))
    (hstep : ∀ j < t, h (j + 1) = h j + η j * k (j + 1))
    (zproj : ∀ j < t, ⟪z j, w⟫_ℝ = h j + if j = τ then A else 0) :
    ∀ j ≤ t, ⟪v j, w⟫_ℝ = k j ∧ ⟪y j, w⟫_ℝ = -h j := by
  intro j
  induction j with
  | zero => intro _; simp [vzero, yzero, hzero, kzero]
  | succ j ih =>
    intro hj
    have hjt : j < t := by omega
    obtain ⟨hv, hy⟩ := ih (by omega)
    have hv' : ⟪v (j + 1), w⟫_ℝ = k (j + 1) := by
      rw [vstep j hjt, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        inner_add_left, hv, hy, zproj j hjt, kstep j hjt]
      ring
    refine ⟨hv', ?_⟩
    rw [ystep j hjt, inner_sub_left, real_inner_smul_left, hy, hv', hstep j hjt]
    ring

/-- The Cauchy--Schwarz and absorption step of the projection argument. -/
theorem projection_budget (z : ℕ → E) (h : ℕ → ℝ) (y : E) (τ t : ℕ)
    (A B R : ℝ) (hτ : τ < t) (hA : A = ‖z τ‖) (hB : 0 < B)
    (orth : ∀ i < t, ∀ j < t, i ≠ j → ⟪z i, z j⟫_ℝ = 0)
    (floor : ∀ j < t, B ≤ ‖z j‖)
    (radius : ‖y‖ ≤ R) (ht0 : 0 ≤ h t)
    (height : ∀ j ∈ Ioo τ t, 0 ≤ h j ∧ h j ≤ h t)
    (projection : ⟪y, direction z h τ t A⟫_ℝ = -h t)
    (small : R * Real.sqrt (t - τ - 1 : ℕ) ≤ B / 2) :
    h t ≤ 2 * R := by
  have hR : 0 ≤ R := (norm_nonneg y).trans radius
  have hn : ∀ j < t, ‖z j‖ ≠ 0 := fun j hj => ne_of_gt (hB.trans_le (floor j hj))
  have hA0 : 0 < A := by rw [hA]; exact hB.trans_le (floor τ hτ)
  have energy : ‖direction z h τ t A‖ ^ 2 ≤
      1 + (t - τ - 1 : ℕ) * (h t ^ 2 / B ^ 2) := by
    rw [direction_energy z h τ t A hτ hA hA0 orth hn]
    calc
      _ ≤ 1 + ∑ _j ∈ Ioo τ t, h t ^ 2 / B ^ 2 := by
        apply add_le_add_left
        apply sum_le_sum
        intro j hj
        obtain ⟨hj0, hjh⟩ := height j hj
        have hnorm : 0 < ‖z j‖ := hB.trans_le (floor j (mem_Ioo.mp hj).2)
        have hs : B ^ 2 ≤ ‖z j‖ ^ 2 := by nlinarith [floor j (mem_Ioo.mp hj).2]
        have hh : h j ^ 2 ≤ h t ^ 2 := by nlinarith
        exact (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans
          (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hB) hs)
      _ = _ := by simp [Nat.card_Ioo]
  have cs : h t ≤ R * ‖direction z h τ t A‖ := by
    calc
      _ = |⟪y, direction z h τ t A⟫_ℝ| := by rw [projection, abs_neg, abs_of_nonneg ht0]
      _ ≤ ‖y‖ * ‖direction z h τ t A‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right radius (norm_nonneg _)
  have cs2 : h t ^ 2 ≤ R ^ 2 * ‖direction z h τ t A‖ ^ 2 := by
    have := mul_self_le_mul_self ht0 cs
    nlinarith
  have energyR := mul_le_mul_of_nonneg_left energy (sq_nonneg R)
  have short : R ^ 2 * (t - τ - 1 : ℕ) ≤ B ^ 2 / 4 := by
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (t - τ - 1) : (0 : ℝ) ≤ _)
    have hprod : 0 ≤ R * Real.sqrt (t - τ - 1 : ℕ) := by positivity
    have := mul_self_le_mul_self hprod small
    nlinarith
  have hratio : R ^ 2 * (t - τ - 1 : ℕ) / B ^ 2 ≤ 1 / 4 :=
    (div_le_iff₀ (sq_pos_of_pos hB)).mpr (by nlinarith)
  have hlast := mul_le_mul_of_nonneg_right hratio (sq_nonneg (h t))
  have heq : R ^ 2 * (1 + (t - τ - 1 : ℕ) * (h t ^ 2 / B ^ 2)) =
      R ^ 2 + (R ^ 2 * (t - τ - 1 : ℕ) / B ^ 2) * h t ^ 2 := by ring
  rw [heq] at energyR
  nlinarith

/-- The orthogonal pulse lemma for the heavy-ball trajectory. -/
theorem orthogonal_pulse_budget_full
    (β c η : ℕ → ℝ) (v y z : ℕ → E) (t τ : ℕ) (hτ : τ < t)
    (vzero : v 0 = 0) (yzero : y 0 = 0)
    (vstep : ∀ j < t, v (j + 1) = β j • v j + c j • (y j + z j))
    (ystep : ∀ j < t, y (j + 1) = y j - η j • v (j + 1))
    (hβ : ∀ j < t, 0 ≤ β j) (hc : ∀ j < t, 0 ≤ c j)
    (hη : ∀ j < t, 0 ≤ η j)
    (A B R : ℝ) (hA : A = ‖z τ‖) (hB : 0 < B)
    (orth : ∀ i < t, ∀ j < t, i ≠ j → ⟪z i, z j⟫_ℝ = 0)
    (floor : ∀ j < t, B ≤ ‖z j‖)
    (radius : ‖y t‖ ≤ R)
    (small : R * Real.sqrt (t - τ - 1 : ℕ) ≤ B / 2) :
    A * Resolvent.kernel β c η t τ ≤ 2 * R := by
  let h : ℕ → ℝ := fun j => A * Resolvent.kernel β c η j τ
  let k : ℕ → ℝ := fun j => A * Resolvent.velocityWeight β c j τ
  let w := direction z h τ t A
  have hA0 : 0 < A := by rw [hA]; exact hB.trans_le (floor τ hτ)
  have hbefore : ∀ j ≤ τ, h j = 0 := by
    intro j hj
    simp only [h, Resolvent.kernel_zero β c η hj, mul_zero]
  have kzero : k 0 = 0 := by
    simp only [k, Resolvent.velocityWeight_zero β c (Nat.zero_le τ), mul_zero]
  have kstep : ∀ j < t, k (j + 1) = β j * k j + c j * (if j = τ then A else 0) := by
    intro j _
    rcases lt_trichotomy j τ with hj | rfl | hj
    · simp only [k, Resolvent.velocityWeight_zero β c (by omega : j + 1 ≤ τ),
        Resolvent.velocityWeight_zero β c (by omega : j ≤ τ), if_neg (ne_of_lt hj),
        mul_zero, add_zero]
    · simp only [k, Resolvent.velocityWeight_diag,
        Resolvent.velocityWeight_zero β c (le_refl j), if_true, mul_zero, zero_add]
      ring
    · simp only [k, Resolvent.velocityWeight_succ β c hj, if_neg (ne_of_gt hj),
        mul_zero, add_zero]
      ring
  have hstep : ∀ j < t, h (j + 1) = h j + η j * k (j + 1) := by
    intro j _
    simp only [h, k, Resolvent.kernel_succ]
    ring
  have zproj : ∀ j < t, ⟪z j, w⟫_ℝ = h j + if j = τ then A else 0 :=
    noise_projection z h τ t A hτ hA hA0 orth
      (fun j hj => ne_of_gt (hB.trans_le (floor j hj))) hbefore
  have proj := (trajectory_projection β c η h k v y z w t τ A
    vzero yzero (hbefore 0 (Nat.zero_le τ)) kzero vstep ystep kstep hstep zproj
    t le_rfl).2
  apply projection_budget z h (y t) τ t A B R hτ hA hB orth floor radius
  · exact mul_nonneg hA0.le
      (Resolvent.kernel_nonneg_prefix β c η t t τ hβ (hc τ hτ) hη le_rfl)
  · intro j hj
    refine ⟨mul_nonneg hA0.le
      (Resolvent.kernel_nonneg_prefix β c η t j τ hβ (hc τ hτ) hη
        (mem_Ioo.mp hj).2.le), ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Resolvent.kernel_mono_prefix β c η t τ hβ (hc τ hτ) hη
        (mem_Ioo.mp hj).2.le le_rfl) hA0.le
  · exact proj
  · exact small

end
end ClippedSGD.ProjectionPulse
