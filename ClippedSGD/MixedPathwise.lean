import ClippedSGD.FiniteHorizonPathwise
open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.MixedPathwise
open Potential LinearSchedule FiniteHorizonPathwise
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Radius telescope for every prefix whose starting states are localized. -/
theorem radius_prefix_mixed_bound {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L η R B V : ℝ) (hL : 0 < L) (hη : 0 < η)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (hstep : η ≤ 1/(2*L)) (T m : ℕ) (hm : m ≤ T)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x e b : ℕ → E) (M : ℕ → ℝ)
    (hupdate : ∀ t < T, x (t+2)=x (t+1)-step η T (t+1) • (gradient f (x (t+1))+e (t+1)))
    (hradius : ∀ t < m, ‖x (t+1)-xstar‖ ≤ 2*R)
    (hbias : ∀ t < m, ‖b (t+1)‖ ≤ B)
    (hmean : ∀ t < m, M (t+1) ≤ V) :
    ‖x (m+1)-xstar‖^2 ≤ ‖x 1-xstar‖^2+
      (∑t∈Finset.range m, ((step η T (t+1))^2*(‖e (t+1)‖^2-M (t+1))-2*step η T (t+1)*⟪e (t+1)-b (t+1),radiusDirection f η T xstar x (t+1)⟫_ℝ))+
      4*R*η*m*B+η^2*m*V := by
  have hηL : η ≤ 1/L := hstep.trans (by apply one_div_le_one_div_of_le hL; linarith)
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := ih (by omega) (fun t ht => hradius t (by omega)) (fun t ht => hbias t (by omega)) (fun t ht => hmean t (by omega))
    have hst := step_pos η hη T (m+1) (by omega) (by omega)
    have hsle := step_le η hη.le T (m+1) (by omega) (by omega)
    have ha := Radius.gradient_step_nonexpansive hconv (fun y => (hdiff y).hasGradientAt)
      L (step η T (m+1)) hL hlip hst.le (hsle.trans hηL) xstar hmin (x (m+1))
    have haR : ‖radiusDirection f η T xstar x (m+1)‖ ≤ 2*R := ha.trans (hradius m (by omega))
    have hi := real_inner_le_norm (-(b (m+1))) (radiusDirection f η T xstar x (m+1))
    rw [inner_neg_left, norm_neg] at hi
    have hiB := mul_le_mul (hbias m (by omega)) haR (norm_nonneg _) hB
    have hbterm : -2*step η T (m+1)*⟪b (m+1),radiusDirection f η T xstar x (m+1)⟫_ℝ ≤ 4*R*η*B := by
      have h1 := mul_le_mul_of_nonneg_left (hi.trans hiB) (show 0 ≤ 2*step η T (m+1) by positivity)
      have h2 := mul_le_mul_of_nonneg_right hsle (show 0 ≤ 4*R*B by positivity)
      nlinarith only [h1, h2]
    have heterm : (step η T (m+1))^2*M (m+1) ≤ η^2*V :=
      (mul_le_mul_of_nonneg_left (hmean m (by omega)) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (by nlinarith) hV)
    have hs := Radius.inexact_radius_step hconv (fun y => (hdiff y).hasGradientAt)
      L (step η T (m+1)) hL hlip hst.le (hsle.trans hηL) xstar hmin (x (m+1)) (e (m+1)) (b (m+1))
    change _ ≤ ‖x (m+1)-xstar‖^2-
      2*step η T (m+1)*⟪e (m+1)-b (m+1),radiusDirection f η T xstar x (m+1)⟫_ℝ-
      2*step η T (m+1)*⟪b (m+1),radiusDirection f η T xstar x (m+1)⟫_ℝ+
      (step η T (m+1))^2*‖e (m+1)‖^2 at hs
    rw [← hupdate m (by omega)] at hs
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    nlinarith only [hp, hs, hbterm, heterm]

/-- Potential telescope for every prefix whose starting states are localized. -/
theorem potential_prefix_mixed_bound {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L η R B V : ℝ) (hL : 0 < L) (hη : 0 < η)
    (hR : 0 ≤ R) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (hstep : η ≤ 1/(2*L)) (T m : ℕ) (hT : 0 < T) (hm : m ≤ T)
    (xstar : E) (x e b : ℕ → E) (M : ℕ → ℝ)
    (hupdate : ∀ t < T, x (t+2)=x (t+1)-step η T (t+1) • (gradient f (x (t+1))+e (t+1)))
    (henergy : ∀ t < m, energy η T xstar x t ≤ 2*R^2)
    (hbias : ∀ t < m, ‖b (t+1)‖ ≤ B)
    (hmean : ∀ t < m, M (t+1) ≤ V) :
    objective f η T xstar x m+energy η T xstar x m ≤ ‖x 1-xstar‖^2/2+
      (∑t∈Finset.range m,
        (2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1)*(‖e (t+1)‖^2-M (t+1))+
        ⟪e (t+1)-b (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ))+
      3*R*η*m*B+4*η^2*m*V := by
  have hp := scaled_potential hconv hdiff L η hL hη hlip hstep T m hT hm xstar x e hupdate
  have hsum := Finset.sum_le_sum (s := Finset.range m) (f := fun t =>
      2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1)*‖e (t+1)‖^2+
        ⟪e (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ)
      (g := fun t =>
        (2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1)*(‖e (t+1)‖^2-M (t+1))+
        ⟪e (t+1)-b (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ)+3*R*η*B+4*η^2*V) (by
    intro t ht
    have htm := Finset.mem_range.mp ht
    have hcoef := error_coefficient_bound η hη T (t+1) (by omega) (by omega)
    have htpos := tailSum_pos (step η T) T (t+1) hT (by omega)
      (fun j hj hjT => step_pos η hη T j hj hjT)
    have h1pos := tailSum_pos (step η T) T 1 hT (by omega)
      (fun j hj hjT => step_pos η hη T j hj hjT)
    have hc := (mul_le_mul_of_nonneg_left (hmean t htm)
      (by positivity : 0 ≤ 2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1))).trans
      (mul_le_mul_of_nonneg_right hcoef hV)
    have he := henergy t htm
    have hd := noiseDirection_bound η R hη hR T (t+1) (by omega) (by omega) xstar x
      (by simpa only [Nat.add_sub_cancel] using he)
    have hi := (real_inner_le_norm (b (t+1)) (noiseDirection η T xstar x (t+1))).trans
      (mul_le_mul (hbias t htm) hd (norm_nonneg _) hB)
    dsimp only
    rw [inner_sub_left]
    nlinarith only [hc, hi])
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib] at hp
  simp only [Finset.sum_add_distrib]
  nlinarith only [hp, hsum]

end
end ClippedSGD.MixedPathwise
