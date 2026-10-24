import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The one-step inequality for an inexact gradient step on a smooth convex function on a
real Hilbert space. -/

open Set
open scoped InnerProductSpace

set_option autoImplicit false

namespace ClippedSGD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Derivative of the objective restricted to the straight line from x to y. -/
lemma along_line_hasDerivAt {f : E → ℝ} {g : E → E}
    (hgrad : ∀ u, HasGradientAt f (g u) u) (x y : E) (t : ℝ) :
    HasDerivAt (f ∘ AffineMap.lineMap x y)
      ⟪g (AffineMap.lineMap x y t), y - x⟫_ℝ t := by
  simpa only [InnerProductSpace.toDual_apply] using
    (hasGradientAt_iff_hasFDerivAt.mp (hgrad (AffineMap.lineMap x y t))).comp_hasDerivAt
      t AffineMap.hasDerivAt_lineMap

/-- The first-order inequality of convexity. -/
lemma convex_support {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ u, HasGradientAt f (g u) u) (x z : E) :
    f x + ⟪g x, z - x⟫_ℝ ≤ f z := by
  have hc := hconv.comp_affineMap (AffineMap.lineMap x z)
  have hd := along_line_hasDerivAt hgrad x z 0
  have hh := hc.le_slope_of_hasDerivAt (by simp) (by simp)
    (show (0 : ℝ) < 1 by norm_num) hd
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at hh
  linarith

/-- The quadratic upper bound for a function with Lipschitz gradient. -/
lemma smooth_upper {f : E → ℝ} {g : E → E} {L : ℝ}
    (hgrad : ∀ u, HasGradientAt f (g u) u)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  let φ : ℝ → ℝ := f ∘ AffineMap.lineMap x y
  let A : ℝ := ⟪g x, y - x⟫_ℝ
  let N : ℝ := ‖y - x‖
  let B : ℝ → ℝ := fun t => f x + t * A + L / 2 * t ^ 2 * N ^ 2
  have hφ (t : ℝ) : HasDerivAt φ ⟪g (AffineMap.lineMap x y t), y - x⟫_ℝ t :=
    along_line_hasDerivAt hgrad x y t
  have hB (t : ℝ) : HasDerivAt B (A + L * t * N ^ 2) t := by
    convert ((hasDerivAt_const t (f x)).add ((hasDerivAt_id t).mul_const A)).add
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (N ^ 2)) using 1
    dsimp [B]
    ring
  have bound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ⟪g (AffineMap.lineMap x y t), y - x⟫_ℝ ≤ A + L * t * N ^ 2 := by
    have hn : ‖g (AffineMap.lineMap x y t) - g x‖ ≤ L * (t * N) := by
      simpa [AffineMap.lineMap_apply_module', norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1, N] using hlip (AffineMap.lineMap x y t) x
    have hi := (real_inner_le_norm (g (AffineMap.lineMap x y t) - g x) (y - x)).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg (y - x)))
    rw [inner_sub_left] at hi
    dsimp [A, N] at *
    nlinarith only [hi]
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hφ t).continuousAt.continuousWithinAt)
    (fun t _ => (hφ t).hasDerivWithinAt)
    (show φ 0 ≤ B 0 by simp [φ, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    bound (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa [φ, B, A, N] using h

/-- The one-step inequality for an inexact gradient step, with any error `e` and
comparator `z`. -/
theorem inexact_smooth_convex_step {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ u, HasGradientAt f (g u) u)
    {L γ : ℝ} (hL : 0 < L)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hγ : 0 < γ) (hstep : γ ≤ 1 / (2 * L))
    (x z e y : E) (hy : y = x - γ • (g x + e)) :
    γ * (f y - f z) + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖x - z‖ ^ 2 + γ * ⟪e, z - x⟫_ℝ + γ ^ 2 * ‖e‖ ^ 2 := by
  have hγL : γ * L ≤ (1 / 2 : ℝ) := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 2 * L by linarith)).mp hstep
    nlinarith only [hh]
  have hs := smooth_upper hgrad hlip x y
  have hc := convex_support hconv hgrad x z
  have hdiff : f y - f z ≤ ⟪g x, y - z⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
    simp only [inner_sub_right] at hs hc ⊢
    linarith
  have hm := mul_le_mul_of_nonneg_left hdiff hγ.le
  have hthree : ‖x - z‖ ^ 2 = ‖x - y‖ ^ 2 +
      2 * ⟪x - y, y - z⟫_ℝ + ‖y - z‖ ^ 2 := by
    simpa only [sub_add_sub_cancel] using norm_add_sq_real (x - y) (y - z)
  have hu : γ • g x = (x - y) - γ • e := by
    rw [hy, smul_add]
    abel
  have hi : γ * ⟪g x, y - z⟫_ℝ =
      ⟪x - y, y - z⟫_ℝ - γ * ⟪e, y - z⟫_ℝ := by
    rw [← real_inner_smul_left, hu, inner_sub_left, real_inner_smul_left]
  have he : ⟪e, y - z⟫_ℝ = -⟪e, z - x⟫_ℝ - ⟪e, x - y⟫_ℝ := by
    simp only [inner_sub_right]
    ring
  have hyoung : γ * ⟪e, x - y⟫_ℝ ≤
      γ ^ 2 * ‖e‖ ^ 2 + ‖x - y‖ ^ 2 / 4 := by
    have hcs := mul_le_mul_of_nonneg_left (real_inner_le_norm e (x - y)) hγ.le
    nlinarith only [hcs, sq_nonneg (γ * ‖e‖ - ‖x - y‖ / 2)]
  have hcoef := mul_nonpos_of_nonpos_of_nonneg
    (show 2 * γ * L - 1 ≤ 0 by nlinarith only [hγL]) (sq_nonneg ‖x - y‖)
  rw [mul_add, hi, he, norm_sub_rev y x] at hm
  nlinarith only [hm, hthree, hyoung, hcoef]

/-- The one-step inequality stated with `gradient f`. -/
theorem paper_one_step {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    {L γ : ℝ} (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (hγ : 0 < γ) (hstep : γ ≤ 1 / (2 * L)) (x z e : E) :
    let y := x - γ • (gradient f x + e)
    γ * (f y - f z) + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖x - z‖ ^ 2 + γ * ⟪e, z - x⟫_ℝ + γ ^ 2 * ‖e‖ ^ 2 := by
  exact inexact_smooth_convex_step hconv (fun u => (hdiff u).hasGradientAt)
    hL hlip hγ hstep x z e _ rfl

end ClippedSGD
