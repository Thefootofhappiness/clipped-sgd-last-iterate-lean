import ClippedSGD
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.Radius
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_zero_at_minimizer {f : E → ℝ} {g : E → E} (hgrad : ∀ x, HasGradientAt f (g x) x)
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) : g xstar=0 := by
  have hm : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  have hd := (hgrad xstar).hasFDerivAt.fderiv
  have hz := hm.fderiv_eq_zero
  rw [hd] at hz
  exact (InnerProductSpace.toDual ℝ E).injective (by simpa using hz)

/-- `‖∇f(x)‖² ≤ 2L (f(x) - f(xstar))` for an `L`-smooth `f` minimized at `xstar`. -/
lemma gradient_sq_le_gap {f : E → ℝ} {g : E → E} (hgrad : ∀ x, HasGradientAt f (g x) x)
    (L : ℝ) (hL : 0 < L) (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (x : E) :
    ‖g x‖^2 ≤ 2*L*(f x-f xstar) := by
  have hs := smooth_upper hgrad hlip x (x-(1/L) • g x)
  have he : x-(1/L) • g x-x=-(1/L) • g x := by module
  rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.mpr hL)] at hs
  have hm := hmin (x-(1/L) • g x)
  have hid : -(1/L)*‖g x‖^2+L/2*((1/L)*‖g x‖)^2= -‖g x‖^2/(2*L) := by
    field_simp
    <;> ring
  have hs' : f (x-(1/L) • g x) ≤ f x-‖g x‖^2/(2*L) := by
    rw [add_assoc, hid] at hs
    simpa only [neg_div, sub_eq_add_neg] using hs
  have hdiv : ‖g x‖^2/(2*L) ≤ f x-f xstar := by linarith
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2*L)).mp hdiv

lemma gradient_step_nonexpansive {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (L γ : ℝ) (hL : 0 < L) (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (hγ : 0 ≤ γ) (hγL : γ ≤ 1/L) (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (x : E) :
    ‖x-xstar-γ • g x‖ ≤ ‖x-xstar‖ := by
  have hs := convex_support hconv hgrad x xstar
  have hg := gradient_sq_le_gap hgrad L hL hlip xstar hmin x
  rw [show xstar-x=-(x-xstar) by abel, inner_neg_right] at hs
  have hi : ‖g x‖^2 ≤ 2*L*⟪g x,x-xstar⟫_ℝ := by nlinarith
  have hγL' : γ*L ≤ 1 := (le_div_iff₀ hL).mp hγL
  have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ γ/L by positivity)
  have hnorm : ‖x-xstar-γ • g x‖^2 = ‖x-xstar‖^2-2*γ*⟪g x,x-xstar⟫_ℝ+γ^2*‖g x‖^2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hprod : γ^2*‖g x‖^2 ≤ (γ/L)*‖g x‖^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (le_div_iff₀ hL).mpr
    nlinarith [mul_le_mul_of_nonneg_left hγL' hγ]
  have hcancel : (γ/L)*(2*L*⟪g x,x-xstar⟫_ℝ)=2*γ*⟪g x,x-xstar⟫_ℝ := by
    field_simp
    <;> ring
  rw [hcancel] at hm
  nlinarith [norm_nonneg (x-xstar-γ • g x), norm_nonneg (x-xstar)]

lemma inexact_radius_step {f : E → ℝ} {g : E → E}
    (hconv : ConvexOn ℝ univ f) (hgrad : ∀ x, HasGradientAt f (g x) x)
    (L γ : ℝ) (hL : 0 < L) (hlip : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (hγ : 0 ≤ γ) (hγL : γ ≤ 1/L) (xstar : E) (hmin : ∀ x, f xstar ≤ f x)
    (x e b : E) :
    let a := x-xstar-γ • g x
    ‖x-γ • (g x+e)-xstar‖^2 ≤ ‖x-xstar‖^2-
      2*γ*⟪e-b,a⟫_ℝ-2*γ*⟪b,a⟫_ℝ+γ^2*‖e‖^2 := by
  dsimp only
  have hn := gradient_step_nonexpansive hconv hgrad L γ hL hlip hγ hγL xstar hmin x
  have he : x-γ • (g x+e)-xstar=(x-xstar-γ • g x)-γ • e := by module
  rw [he, norm_sub_sq_real, real_inner_smul_right, real_inner_comm e (x-xstar-γ • g x),
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_sub_left]
  nlinarith [norm_nonneg (x-xstar-γ • g x)]

end
end ClippedSGD.Radius
