import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.GeomSum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Interval.Finset.Fin

/-! Response kernels of the heavy-ball recursion. Time is zero-based: Lean time `j` is
the paper's time `j + 1`. -/

open scoped BigOperators InnerProductSpace
open Finset

namespace ClippedSGD.Resolvent

/-- Weight of input j in the velocity at time t. -/
noncomputable def velocityWeight (β c : ℕ → ℝ) (t j : ℕ) : ℝ :=
  if j < t then c j * ∏ i ∈ Ico (j + 1) t, β i else 0

/-- The position response kernel, a sum of velocity weights. -/
noncomputable def kernel (β c η : ℕ → ℝ) (t j : ℕ) : ℝ :=
  ∑ s ∈ range t, η s * velocityWeight β c (s + 1) j

lemma velocityWeight_zero (β c : ℕ → ℝ) {t j : ℕ} (h : t ≤ j) :
    velocityWeight β c t j = 0 := by
  simp [velocityWeight, Nat.not_lt.mpr h]

lemma velocityWeight_diag (β c : ℕ → ℝ) (t : ℕ) :
    velocityWeight β c (t + 1) t = c t := by
  simp [velocityWeight]

lemma velocityWeight_succ (β c : ℕ → ℝ) {t j : ℕ} (h : j < t) :
    velocityWeight β c (t + 1) j = β t * velocityWeight β c t j := by
  simp only [velocityWeight, if_pos h, if_pos (Nat.lt_succ_of_lt h)]
  rw [prod_Ico_succ_top (by omega : j + 1 ≤ t)]
  ring

lemma kernel_zero (β c η : ℕ → ℝ) {t j : ℕ} (h : t ≤ j) :
    kernel β c η t j = 0 := by
  apply sum_eq_zero
  intro s hs
  have hsj : s + 1 ≤ j := by have := mem_range.mp hs; omega
  rw [velocityWeight_zero β c hsj, mul_zero]

lemma kernel_succ (β c η : ℕ → ℝ) (t j : ℕ) :
    kernel β c η (t + 1) j =
      kernel β c η t j + η t * velocityWeight β c (t + 1) j := by
  exact sum_range_succ _ t

/-- The kernel is nonnegative when the controls before time `T` are nonnegative. -/
theorem kernel_nonneg_prefix (β c η : ℕ → ℝ) (T t j : ℕ)
    (hβ : ∀ i < T, 0 ≤ β i) (hc : 0 ≤ c j) (hη : ∀ i < T, 0 ≤ η i)
    (ht : t ≤ T) : 0 ≤ kernel β c η t j := by
  apply sum_nonneg
  intro s hs
  have hsT : s < T := lt_of_lt_of_le (mem_range.mp hs) ht
  apply mul_nonneg (hη s hsT)
  unfold velocityWeight
  split_ifs
  · apply mul_nonneg hc
    apply prod_nonneg
    intro i hi
    exact hβ i (by have := (mem_Ico.mp hi).2; omega)
  · exact le_rfl

/-- Under the same conditions, the kernel is nondecreasing in time up to `T`. -/
theorem kernel_mono_prefix (β c η : ℕ → ℝ) (T j : ℕ)
    (hβ : ∀ i < T, 0 ≤ β i) (hc : 0 ≤ c j) (hη : ∀ i < T, 0 ≤ η i)
    {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    kernel β c η s j ≤ kernel β c η t j := by
  unfold kernel
  apply sum_le_sum_of_subset_of_nonneg (range_mono hst)
  intro k hk _
  have hkT : k < T := lt_of_lt_of_le (mem_range.mp hk) ht
  apply mul_nonneg (hη k hkT)
  unfold velocityWeight
  split_ifs
  · apply mul_nonneg hc
    apply prod_nonneg
    intro i hi
    exact hβ i (by have := (mem_Ico.mp hi).2; omega)
  · exact le_rfl

section Matrices

variable {n : ℕ}

end Matrices

section Dynamics
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Unrolls the velocity recursion. -/
theorem velocity_expansion (β c : ℕ → ℝ) (v u : ℕ → E)
    (T : ℕ) (vzero : v 0 = 0)
    (step : ∀ t < T, v (t + 1) = β t • v t + c t • u t) (t : ℕ) (ht : t ≤ T) :
    v t = ∑ j ∈ range t, velocityWeight β c t j • u j := by
  induction t with
  | zero => simpa using vzero
  | succ t ih =>
    rw [step t (by omega), ih (by omega), sum_range_succ, velocityWeight_diag, smul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [velocityWeight_succ β c (mem_range.mp hj), mul_smul]

/-- Unrolls the position recursion from zero into the response kernel. -/
theorem position_expansion (β c η : ℕ → ℝ) (v y u : ℕ → E)
    (T : ℕ) (vzero : v 0 = 0) (yzero : y 0 = 0)
    (vstep : ∀ t < T, v (t + 1) = β t • v t + c t • u t)
    (ystep : ∀ t < T, y (t + 1) = y t - η t • v (t + 1)) (t : ℕ) (ht : t ≤ T) :
    y t = -(∑ j ∈ range t, kernel β c η t j • u j) := by
  induction t with
  | zero => simpa using yzero
  | succ t ih =>
    rw [ystep t (by omega), ih (by omega),
      velocity_expansion β c v u T vzero vstep (t + 1) ht, smul_sum]
    rw [sum_range_succ, sum_range_succ]
    simp only [kernel_succ, add_smul, velocityWeight_diag,
      kernel_zero β c η (le_refl t), zero_add]
    rw [sum_add_distrib]
    simp only [mul_smul]
    abel

end Dynamics

end ClippedSGD.Resolvent
