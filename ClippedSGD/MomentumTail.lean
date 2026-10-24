import ClippedSGD.ProjectionPulse
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Forgetting bounds for the response to a single pulse. -/

open Finset
open scoped BigOperators InnerProductSpace

namespace ClippedSGD.MomentumTail

noncomputable section

lemma damping_window (β : ℕ → ℝ) (j w : ℕ) (g : ℝ)
    (hβ : ∀ i ∈ Ico (j + 1) (j + w + 1), 0 ≤ β i)
    (hgap : ∀ i ∈ Ico (j + 1) (j + w + 1), β i ≤ 1 - g) :
    (∏ i ∈ Ico (j + 1) (j + w + 1), β i) ≤ Real.exp (-(w : ℝ) * g) := by
  calc
    _ ≤ ∏ _i ∈ Ico (j + 1) (j + w + 1), Real.exp (-g) := by
      apply prod_le_prod hβ
      intro i hi
      exact (hgap i hi).trans (Real.one_sub_le_exp_neg g)
    _ = Real.exp (-(w : ℝ) * g) := by
      rw [prod_const, Nat.card_Ico]
      have hn : j + w + 1 - (j + 1) = w := by omega
      rw [hn, ← Real.exp_nat_mul]
      congr 1
      ring

lemma damping_after_window (β : ℕ → ℝ) (j w s : ℕ) (hjs : j + w ≤ s)
    (g : ℝ)
    (hβ0 : ∀ i ∈ Ico (j + 1) (s + 1), 0 ≤ β i)
    (hβ1 : ∀ i ∈ Ico (j + 1) (s + 1), β i ≤ 1)
    (hgap : ∀ i ∈ Ico (j + 1) (j + w + 1), β i ≤ 1 - g) :
    (∏ i ∈ Ico (j + 1) (s + 1), β i) ≤ Real.exp (-(w : ℝ) * g) := by
  have hfirst : ∀ i ∈ Ico (j + 1) (j + w + 1), 0 ≤ β i := by
    intro i hi
    apply hβ0 i
    have := mem_Ico.mp hi
    exact mem_Ico.mpr ⟨this.1, by omega⟩
  rw [← prod_Ico_consecutive β (by omega : j + 1 ≤ j + w + 1)
    (by omega : j + w + 1 ≤ s + 1)]
  have htail : (∏ i ∈ Ico (j + w + 1) (s + 1), β i) ≤ 1 := by
    apply prod_le_one
    · intro i hi; apply hβ0 i
      have := mem_Ico.mp hi
      exact mem_Ico.mpr ⟨by omega, this.2⟩
    · intro i hi; apply hβ1 i
      have := mem_Ico.mp hi
      exact mem_Ico.mpr ⟨by omega, this.2⟩
  calc
    _ ≤ (∏ i ∈ Ico (j + 1) (j + w + 1), β i) * 1 :=
      mul_le_mul_of_nonneg_left htail (prod_nonneg hfirst)
    _ ≤ _ := by simpa using damping_window β j w g hfirst hgap

/-- A bound on the position-response kernel after the useful window of a pulse. -/
theorem kernel_tail_bound (β c η : ℕ → ℝ) (N t j w : ℕ)
    (htN : t ≤ N) (hwindow : j + w + 1 ≤ t)
    (g H A : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hc0 : 0 ≤ c j) (hc1 : c j ≤ 1)
    (hβ0 : ∀ i < t, 0 ≤ β i) (hβ1 : ∀ i < t, β i ≤ 1)
    (hη0 : ∀ i < t, 0 ≤ η i) (hηH : ∀ i < t, η i ≤ H)
    (hgap : ∀ i ∈ Ico (j + 1) (j + w + 1), β i ≤ 1 - g) :
    0 ≤ A * (ClippedSGD.Resolvent.kernel β c η t j -
      ClippedSGD.Resolvent.kernel β c η (j + w + 1) j) ∧
    A * (ClippedSGD.Resolvent.kernel β c η t j -
      ClippedSGD.Resolvent.kernel β c η (j + w + 1) j) ≤
      A * H * N * Real.exp (-(w : ℝ) * g) := by
  let e := j + w + 1
  have hsplit : ClippedSGD.Resolvent.kernel β c η t j -
      ClippedSGD.Resolvent.kernel β c η e j =
      ∑ s ∈ Ico e t, η s * ClippedSGD.Resolvent.velocityWeight β c (s + 1) j := by
    unfold ClippedSGD.Resolvent.kernel
    exact sub_eq_iff_eq_add.mpr
      ((sum_range_add_sum_Ico
        (fun s => η s * ClippedSGD.Resolvent.velocityWeight β c (s + 1) j)
        hwindow).symm.trans (add_comm _ _))
  have hterm (s : ℕ) (hs : s ∈ Ico e t) :
      0 ≤ η s * ClippedSGD.Resolvent.velocityWeight β c (s + 1) j ∧
      η s * ClippedSGD.Resolvent.velocityWeight β c (s + 1) j ≤
        H * Real.exp (-(w : ℝ) * g) := by
    have hst : s < t := (mem_Ico.mp hs).2
    have hjs : j < s + 1 := by have := (mem_Ico.mp hs).1; dsimp [e] at this; omega
    rw [ClippedSGD.Resolvent.velocityWeight, if_pos hjs]
    have hp0 : 0 ≤ ∏ i ∈ Ico (j + 1) (s + 1), β i := by
      apply prod_nonneg
      intro i hi
      apply hβ0 i
      have := (mem_Ico.mp hi).2; omega
    have hp1 : (∏ i ∈ Ico (j + 1) (s + 1), β i) ≤ Real.exp (-(w : ℝ) * g) := by
      apply damping_after_window β j w s
        (by have := (mem_Ico.mp hs).1; dsimp [e] at this; omega) g
      · intro i hi; apply hβ0 i; have := (mem_Ico.mp hi).2; omega
      · intro i hi; apply hβ1 i; have := (mem_Ico.mp hi).2; omega
      · exact hgap
    constructor
    · exact mul_nonneg (hη0 s hst) (mul_nonneg hc0 hp0)
    · calc
        _ ≤ H * (c j * ∏ i ∈ Ico (j + 1) (s + 1), β i) :=
          mul_le_mul_of_nonneg_right (hηH s hst) (mul_nonneg hc0 hp0)
        _ ≤ H * (1 * Real.exp (-(w : ℝ) * g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hc1 hp1 hp0 (by norm_num)) hH
        _ = _ := by ring
  rw [hsplit]
  constructor
  · exact mul_nonneg hA (sum_nonneg fun s hs => (hterm s hs).1)
  · calc
      _ ≤ A * ∑ _s ∈ Ico e t, H * Real.exp (-(w : ℝ) * g) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun s hs => (hterm s hs).2) hA
      _ = A * (t - e : ℕ) * H * Real.exp (-(w : ℝ) * g) := by
        simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
        ring
      _ ≤ A * N * H * Real.exp (-(w : ℝ) * g) := by
        gcongr
        exact_mod_cast (show t - e ≤ N by omega)
      _ = _ := by ring

/-- The short-window and forgetting estimate for a single pulse. -/
theorem pulse_response_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (β c η : ℕ → ℝ) (v y z : ℕ → E) (N T j w : ℕ)
    (hjT : j < T) (hTN : T ≤ N)
    (vzero : v 0 = 0) (yzero : y 0 = 0)
    (vstep : ∀ i < T, v (i + 1) = β i • v i + c i • (y i + z i))
    (ystep : ∀ i < T, y (i + 1) = y i - η i • v (i + 1))
    (hβ0 : ∀ i < T, 0 ≤ β i) (hβ1 : ∀ i < T, β i ≤ 1)
    (hc0 : ∀ i < T, 0 ≤ c i) (hc1 : c j ≤ 1)
    (hη0 : ∀ i < T, 0 ≤ η i)
    (A B R H g : ℝ) (hA : A = ‖z j‖) (hB : 0 < B) (hH : 0 ≤ H)
    (hηH : ∀ i < T, η i ≤ H)
    (hgap : ∀ i ∈ Ico (j + 1) (j + w + 1), β i ≤ 1 - g)
    (orth : ∀ i < T, ∀ k < T, i ≠ k → ⟪z i, z k⟫_ℝ = 0)
    (floor : ∀ i < T, B ≤ ‖z i‖)
    (radius : ‖y (min T (j + w + 1))‖ ≤ R)
    (small : R * Real.sqrt (w : ℝ) ≤ B / 2) :
    A * ClippedSGD.Resolvent.kernel β c η T j ≤
      2 * R + A * H * N * Real.exp (-(w : ℝ) * g) := by
  let e := min T (j + w + 1)
  have heT : e ≤ T := min_le_left _ _
  have hje : j < e := lt_min hjT (by omega)
  have hR : 0 ≤ R := (norm_nonneg _).trans radius
  have hA0 : 0 ≤ A := by rw [hA]; exact norm_nonneg _
  have hew : e - j - 1 ≤ w := by
    have := min_le_right T (j + w + 1)
    dsimp [e]
    omega
  have hsmall : R * Real.sqrt (e - j - 1 : ℕ) ≤ B / 2 := by
    calc
      _ ≤ R * Real.sqrt (w : ℝ) := by
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hew)) hR
      _ ≤ _ := small
  have hshort : A * ClippedSGD.Resolvent.kernel β c η e j ≤ 2 * R := by
    exact ClippedSGD.ProjectionPulse.orthogonal_pulse_budget_full β c η v y z e j hje
      vzero yzero
      (fun i hi => vstep i (hi.trans_le heT))
      (fun i hi => ystep i (hi.trans_le heT))
      (fun i hi => hβ0 i (hi.trans_le heT))
      (fun i hi => hc0 i (hi.trans_le heT))
      (fun i hi => hη0 i (hi.trans_le heT))
      A B R hA hB
      (fun i hi k hk hik => orth i (hi.trans_le heT) k (hk.trans_le heT) hik)
      (fun i hi => floor i (hi.trans_le heT)) radius hsmall
  by_cases hTe : T ≤ j + w + 1
  · have he : e = T := min_eq_left hTe
    rw [he] at hshort
    exact hshort.trans (le_add_of_nonneg_right (by positivity))
  · have he : e = j + w + 1 := min_eq_right (le_of_not_ge hTe)
    rw [he] at hshort
    have htail := kernel_tail_bound β c η N T j w hTN (le_of_not_ge hTe)
      g H A hH hA0 (hc0 j hjT) hc1 hβ0 hβ1 hη0 hηH hgap
    nlinarith [htail.2]

/-- The displacement along the useful coordinate, from the zero initialization and the
flat-coordinate gradient `-A Y`. -/
theorem flat_displacement (β c η : ℕ → ℝ) (v x : ℕ → ℝ)
    (Y : ℕ → Bool) (A : ℝ) (T : ℕ) (vzero : v 0 = 0) (xzero : x 0 = 0)
    (vstep : ∀ i < T, v (i + 1) = β i * v i - c i * A * (if Y i then 1 else 0))
    (xstep : ∀ i < T, x (i + 1) = x i - η i * v (i + 1)) :
    x T = ∑ j ∈ range T, if Y j then A * ClippedSGD.Resolvent.kernel β c η T j else 0 := by
  have hv : ∀ i < T, v (i + 1) = β i • v i + c i • (-(A * (if Y i then 1 else 0))) := by
    intro i hi
    rw [vstep i hi]
    simp only [smul_eq_mul]
    ring
  have hx := ClippedSGD.Resolvent.position_expansion β c η v x
    (fun i => -(A * (if Y i then 1 else 0))) T vzero xzero hv xstep T le_rfl
  rw [hx, ← sum_neg_distrib]
  apply sum_congr rfl
  intro j _
  cases hy : Y j <;> simp [smul_eq_mul, hy, mul_comm]

end
end ClippedSGD.MomentumTail
