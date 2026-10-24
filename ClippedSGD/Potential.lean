import ClippedSGD
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The pathwise potential of the last-iterate analysis, for inexact gradient steps and
convex-combination comparators. Indices follow the paper: `x 1` is the initial point, and
update `t` produces `x (t+1)`. -/
open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.Potential
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def comparator (xstar : E) (x : ℕ → E) (w : ℕ → ℝ) : ℕ → E
  | 0 => xstar
  | t+1 => (1-w t/w (t+1)) • x (t+1)+(w t/w (t+1)) • comparator xstar x w t

def distanceEnergy (xstar : E) (x : ℕ → E) (w : ℕ → ℝ) (t : ℕ) : ℝ :=
  w t/2*‖comparator xstar x w t-x (t+1)‖^2

lemma comparator_displacement (xstar : E) (x : ℕ → E) (w : ℕ → ℝ) (t : ℕ) :
    comparator xstar x w (t+1)-x (t+1) =
      (w t/w (t+1)) • (comparator xstar x w t-x (t+1)) := by
  simp only [comparator, sub_smul, one_smul, smul_sub]
  abel

lemma weighted_step {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (xstar : E) (x e : ℕ → E) (w η : ℕ → ℝ) (t : ℕ)
    (hw : 0 < w (t+1)) (hw0 : 0 ≤ w t) (hwmono : w t ≤ w (t+1))
    (hη : 0 < η (t+1)) (hstep : η (t+1) ≤ 1/(2*L))
    (hupdate : x (t+2)=x (t+1)-η (t+1) • (gradient f (x (t+1))+e (t+1))) :
    η (t+1)*w (t+1)*(f (x (t+2))-f (comparator xstar x w (t+1)))+
      distanceEnergy xstar x w (t+1) ≤ distanceEnergy xstar x w t+
      2*(η (t+1))^2*w (t+1)*‖e (t+1)‖^2+
      η (t+1)*w t*⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ := by
  have hs := ClippedSGD.paper_one_step hconv hdiff hL hlip hη hstep
    (x (t+1)) (comparator xstar x w (t+1)) (e (t+1))
  dsimp only at hs
  rw [← hupdate] at hs
  have h := mul_le_mul_of_nonneg_left hs hw.le
  have hr0 : 0 ≤ w t/w (t+1) := div_nonneg hw0 hw.le
  have hr1 : w t/w (t+1) ≤ 1 := (div_le_one hw).mpr hwmono
  have hmul : w (t+1)*(w t/w (t+1))=w t := by field_simp
  have hcoef : w (t+1)*(w t/w (t+1))^2 ≤ w t := by nlinarith
  have hdist : ‖x (t+1)-comparator xstar x w (t+1)‖^2 =
      (w t/w (t+1))^2*‖comparator xstar x w t-x (t+1)‖^2 := by
    rw [norm_sub_rev, comparator_displacement, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr0, mul_pow]
  rw [hdist, comparator_displacement, real_inner_smul_right] at h
  have hnorm := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ‖comparator xstar x w t-x (t+1)‖)
  have he : 0 ≤ (η (t+1))^2*w (t+1)*‖e (t+1)‖^2 := by positivity
  have hinner : w (t+1)*(η (t+1)*((w t/w (t+1))*
      ⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ)) =
      η (t+1)*w t*⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ := by
    calc
      _ = η (t+1)*(w (t+1)*(w t/w (t+1)))*
          ⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ := by ring
      _ = _ := by rw [hmul]
  simp only [distanceEnergy, norm_sub_rev (comparator xstar x w (t+1)) (x (t+2))]
  nlinarith only [h, hnorm, he, hinner]

def gapPrefix (G w : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑t∈Finset.range m, (w (t+1)-w t)*G (t+1)

def objectivePotential (G w η S : ℕ → ℝ) (m : ℕ) : ℝ :=
  η m*w m*G (m+1)+S (m+1)*gapPrefix G w m

lemma coefficient_balance (w η S : ℕ → ℝ) (t : ℕ)
    (hS : S t=η t+S (t+1)) (hw : S t*w t=1) (hwnext : S (t+1)*w (t+1)=1) :
    S (t+1)*(w (t+1)-w t)=η t*w t := by
  rw [hS] at hw
  nlinarith only [hw, hwnext]

lemma objectivePotential_terminal (G w η S : ℕ → ℝ) (T : ℕ)
    (hS : S T=η T+S (T+1)) (hw : S T*w T=1) (hterminal : S (T+1)=0) :
    objectivePotential G w η S T = G (T+1) := by
  simp only [hterminal, add_zero] at hS
  rw [objectivePotential, hterminal, zero_mul, add_zero, ← hS, hw, one_mul]

lemma objectivePotential_nonneg (G w η S : ℕ → ℝ) (m : ℕ)
    (hG : ∀ t, 0 ≤ G t) (hw : 0 ≤ w m) (hη : 0 ≤ η m) (hS : 0 ≤ S (m+1))
    (hmono : ∀ t < m, w t ≤ w (t+1)) : 0 ≤ objectivePotential G w η S m := by
  have hgm := hG (m+1)
  unfold objectivePotential
  apply add_nonneg (by positivity)
  apply mul_nonneg hS
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (sub_nonneg.mpr (hmono t (Finset.mem_range.mp ht))) (hG _)

/-- The weighted average of the objective gaps, defined recursively. -/
def recursiveAverage (G η w : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m+1 => (1-η (m+1)*w (m+1))*recursiveAverage G η w m+
      η (m+1)*w (m+1)*G (m+2)

lemma objectivePotential_rec (G w η S : ℕ → ℝ) (m : ℕ)
    (hS : S m=η m+S (m+1)) (hSw : S m*w m=1)
    (hSnext : S (m+1)=η (m+1)+S (m+2))
    (hSwnext : S (m+1)*w (m+1)=1) :
    objectivePotential G w η S (m+1) =
      (1-η (m+1)*w (m+1))*objectivePotential G w η S m+
      η (m+1)*w (m+1)*G (m+2) := by
  have hb := coefficient_balance w η S m hS hSw hSwnext
  have hb1 : 1-η (m+1)*w (m+1)=S (m+2)*w (m+1) := by
    rw [hSnext] at hSwnext
    nlinarith only [hSwnext]
  rw [hb1]
  simp only [objectivePotential, gapPrefix, Finset.sum_range_succ]
  have he : S (m+2)*(w (m+1)-w m)=
      S (m+2)*w (m+1)*(η m*w m) := by
    have hh := congrArg (fun a : ℝ => S (m+2)*w (m+1)*a) hb
    have hh' := congrArg (fun a : ℝ => S (m+2)*(w (m+1)-w m)*a) hSwnext
    dsimp only at hh hh'
    nlinarith only [hh,hh']
  have hh := congrArg (fun a : ℝ => a*G (m+1)) he
  have hh' := congrArg (fun a : ℝ => S (m+2)*
    (∑ t ∈ Finset.range m, (w (t+1)-w t)*G (t+1))*a) hSwnext
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  try dsimp only at hh hh'
  nlinarith only [hh,hh']

/-- The recursive average equals the explicit expression `objectivePotential`. -/
lemma recursiveAverage_eq_objectivePotential (G w η S : ℕ → ℝ) (m : ℕ)
    (hη0 : η 0=0) (hS : ∀ t ≤ m, S t=η t+S (t+1))
    (hSw : ∀ t ≤ m, S t*w t=1) :
    recursiveAverage G η w m=objectivePotential G w η S m := by
  induction m with
  | zero => simp [recursiveAverage, objectivePotential, gapPrefix, hη0]
  | succ m ih =>
    rw [objectivePotential_rec G w η S m (hS m (by omega))
      (hSw m (by omega)) (hS (m+1) le_rfl) (hSw (m+1) le_rfl)]
    rw [recursiveAverage, ih (fun t ht => hS t (by omega)) (fun t ht => hSw t (by omega))]

/-- By convexity, the gap at the comparator is at most the recursive average. -/
lemma comparator_gap_le_recursiveAverage {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (xstar : E) (x : ℕ → E) (w η S : ℕ → ℝ) (m : ℕ)
    (hw : ∀ t ≤ m+1, 0 < w t) (hwmono : ∀ t ≤ m, w t ≤ w (t+1))
    (hη0 : η 0=0) (hS : ∀ t ≤ m, S t=η t+S (t+1))
    (hSw : ∀ t ≤ m+1, S t*w t=1) :
    f (comparator xstar x w (m+1))-f xstar ≤
      recursiveAverage (fun t => f (x t)-f xstar) η w m := by
  induction m with
  | zero =>
    have hS0 : S 0=S 1 := by simpa [hη0] using hS 0 le_rfl
    have hw01 : w 0=w 1 := by
      have h0 := hSw 0 (by omega)
      have h1 := hSw 1 le_rfl
      rw [hS0] at h0
      have hn : S 1 ≠ 0 := by intro hz; rw [hz, zero_mul] at h1; norm_num at h1
      exact mul_left_cancel₀ hn (h0.trans h1.symm)
    simp [comparator, hw01, (hw 1 le_rfl).ne', recursiveAverage]
  | succ m ih =>
    have hp := ih (fun t ht => hw t (by omega)) (fun t ht => hwmono t (by omega))
      (fun t ht => hS t (by omega)) (fun t ht => hSw t (by omega))
    have hr0 : 0 ≤ w (m+1)/w (m+2) := div_nonneg (hw _ (by omega)).le (hw _ le_rfl).le
    have hr1 : w (m+1)/w (m+2) ≤ 1 := (div_le_one (hw _ le_rfl)).mpr (hwmono _ (by omega))
    have hc := hconv.2 (mem_univ (x (m+2))) (mem_univ (comparator xstar x w (m+1)))
      (sub_nonneg.mpr hr1) hr0 (by ring : (1-w (m+1)/w (m+2))+w (m+1)/w (m+2)=1)
    have hratio : w (m+1)/w (m+2)=1-η (m+1)*w (m+1) := by
      apply (div_eq_iff (hw _ le_rfl).ne').mpr
      have hs := hS (m+1) le_rfl
      have hs1 := hSw (m+1) (by omega)
      have hs2 := hSw (m+2) le_rfl
      rw [hs] at hs1
      have ha := congrArg (fun a : ℝ => a*w (m+2)) hs1
      have hb := congrArg (fun a : ℝ => a*w (m+1)) hs2
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      try dsimp only at ha hb
      nlinarith only [ha,hb]
    have hh := mul_le_mul_of_nonneg_left hp hr0
    change f (comparator xstar x w (m+2)) ≤ _ at hc
    simp only [smul_eq_mul] at hc
    rw [hratio] at hc hh
    simp only [recursiveAverage]
    nlinarith only [hc,hh]

/-- The partial-sum potential bound, by induction on the recursive average. -/
theorem recursive_partial_sum_potential {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (xstar : E) (x e : ℕ → E) (w η S : ℕ → ℝ) (m : ℕ)
    (hw : ∀ t ≤ m, 0 < w t) (hwmono : ∀ t < m, w t ≤ w (t+1))
    (hη0 : η 0=0) (hη : ∀ t < m, 0 < η (t+1))
    (hstep : ∀ t < m, η (t+1) ≤ 1/(2*L))
    (hS : ∀ t ≤ m, S t=η t+S (t+1)) (hSw : ∀ t ≤ m, S t*w t=1)
    (hupdate : ∀ t < m, x (t+2)=x (t+1)-η (t+1) • (gradient f (x (t+1))+e (t+1))) :
    recursiveAverage (fun t => f (x t)-f xstar) η w m+distanceEnergy xstar x w m ≤
      distanceEnergy xstar x w 0+
        ∑t∈Finset.range m, (2*(η (t+1))^2*w (t+1)*‖e (t+1)‖^2+
          η (t+1)*w t*⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ) := by
  induction m with
  | zero => simp [recursiveAverage]
  | succ m ih =>
    have hp := ih (fun t ht => hw t (by omega)) (fun t ht => hwmono t (by omega))
      (fun t ht => hη t (by omega)) (fun t ht => hstep t (by omega))
      (fun t ht => hS t (by omega)) (fun t ht => hSw t (by omega))
      (fun t ht => hupdate t (by omega))
    have hc := comparator_gap_le_recursiveAverage hconv xstar x w η S m hw
      (fun t ht => hwmono t (by omega)) hη0 (fun t ht => hS t (by omega)) hSw
    have hs := weighted_step hconv hdiff L hL hlip xstar x e w η m
      (hw _ le_rfl) (hw _ (by omega)).le (hwmono m (by omega))
      (hη m (by omega)) (hstep m (by omega)) (hupdate m (by omega))
    have hh := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (hη m (by omega)).le (hw _ le_rfl).le)
    rw [recursiveAverage, Finset.sum_range_succ]
    nlinarith only [hp,hs,hh]

/-- The partial-sum potential bound with the explicit `objectivePotential`, before
multiplication by `S 1`. -/
theorem partial_sum_potential {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (xstar : E) (x e : ℕ → E) (w η S : ℕ → ℝ) (m : ℕ)
    (hw : ∀ t ≤ m, 0 < w t) (hwmono : ∀ t < m, w t ≤ w (t+1))
    (hη0 : η 0=0) (hη : ∀ t < m, 0 < η (t+1))
    (hstep : ∀ t < m, η (t+1) ≤ 1/(2*L))
    (hS : ∀ t ≤ m, S t=η t+S (t+1)) (hSw : ∀ t ≤ m, S t*w t=1)
    (hupdate : ∀ t < m, x (t+2)=x (t+1)-η (t+1) • (gradient f (x (t+1))+e (t+1))) :
    objectivePotential (fun t => f (x t)-f xstar) w η S m+distanceEnergy xstar x w m ≤
      distanceEnergy xstar x w 0+
        ∑t∈Finset.range m, (2*(η (t+1))^2*w (t+1)*‖e (t+1)‖^2+
          η (t+1)*w t*⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ) := by
  rw [← recursiveAverage_eq_objectivePotential _ w η S m hη0 hS hSw]
  exact recursive_partial_sum_potential hconv hdiff L hL hlip xstar x e w η S m
    hw hwmono hη0 hη hstep hS hSw hupdate

/-- Tail sums of the step sizes, with the paper's convention `S 0 = S 1`. -/
def tailSum (η : ℕ → ℝ) (T t : ℕ) : ℝ := ∑i∈Finset.Ico (max 1 t) (T+1), η i

def inverseTail (η : ℕ → ℝ) (T t : ℕ) : ℝ := 1/tailSum η T t

lemma tailSum_zero (η : ℕ → ℝ) (T : ℕ) : tailSum η T 0=tailSum η T 1 := by simp [tailSum]
lemma tailSum_terminal (η : ℕ → ℝ) (T : ℕ) : tailSum η T (T+1)=0 := by simp [tailSum]

lemma tailSum_rec (η : ℕ → ℝ) (T t : ℕ) (hη0 : η 0=0) (ht : t ≤ T) :
    tailSum η T t=η t+tailSum η T (t+1) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [tailSum_zero, hη0, zero_add]
  · simp only [tailSum, max_eq_right (show 1 ≤ t by omega), max_eq_right (show 1 ≤ t+1 by omega)]
    exact Finset.sum_eq_sum_Ico_succ_bot (by omega) η

lemma tailSum_nonneg (η : ℕ → ℝ) (T t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i) : 0 ≤ tailSum η T t := by
  apply Finset.sum_nonneg
  intro i hi
  have hb := Finset.mem_Ico.mp hi
  exact hη i (le_trans (le_max_left 1 t) hb.1) (by omega)

lemma tailSum_pos (η : ℕ → ℝ) (T t : ℕ) (hT : 0 < T) (ht : t ≤ T)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 < η i) : 0 < tailSum η T t := by
  apply Finset.sum_pos'
  · intro i hi
    have hb := Finset.mem_Ico.mp hi
    exact (hη i (le_trans (le_max_left 1 t) hb.1) (by omega)).le
  · refine ⟨max 1 t, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩, hη _ (le_max_left _ _) ?_⟩ <;> omega

lemma inverseTail_mul (η : ℕ → ℝ) (T t : ℕ) (hT : 0 < T) (ht : t ≤ T)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 < η i) : tailSum η T t*inverseTail η T t=1 := by
  unfold inverseTail
  exact mul_one_div_cancel (tailSum_pos η T t hT ht hη).ne'

lemma inverseTail_pos (η : ℕ → ℝ) (T t : ℕ) (hT : 0 < T) (ht : t ≤ T)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 < η i) : 0 < inverseTail η T t :=
  one_div_pos.mpr (tailSum_pos η T t hT ht hη)

lemma inverseTail_mono (η : ℕ → ℝ) (T t : ℕ) (hT : 0 < T) (ht : t < T)
    (hη0 : η 0=0) (hη : ∀ i, 1 ≤ i → i ≤ T → 0 < η i) :
    inverseTail η T t ≤ inverseTail η T (t+1) := by
  have hηt : 0 ≤ η t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [hη0]
    · exact (hη t ht0 ht.le).le
  apply one_div_le_one_div_of_le (tailSum_pos η T (t+1) hT (by omega) hη)
  rw [tailSum_rec η T t hη0 ht.le]
  linarith

/-- The partial-sum potential bound with weights and comparators built from the step
sizes. -/
theorem stepsize_partial_sum_potential {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (xstar : E) (x e : ℕ → E) (η : ℕ → ℝ) (T m : ℕ) (hT : 0 < T) (hm : m ≤ T)
    (hη0 : η 0=0) (hη : ∀ t, 1 ≤ t → t ≤ T → 0 < η t)
    (hstep : ∀ t, 1 ≤ t → t ≤ T → η t ≤ 1/(2*L))
    (hupdate : ∀ t < T, x (t+2)=x (t+1)-η (t+1) • (gradient f (x (t+1))+e (t+1))) :
    let w := inverseTail η T
    let S := tailSum η T
    objectivePotential (fun t => f (x t)-f xstar) w η S m+distanceEnergy xstar x w m ≤
      distanceEnergy xstar x w 0+
        ∑t∈Finset.range m, (2*(η (t+1))^2*w (t+1)*‖e (t+1)‖^2+
          η (t+1)*w t*⟪e (t+1), comparator xstar x w t-x (t+1)⟫_ℝ) := by
  dsimp only
  exact partial_sum_potential hconv hdiff L hL hlip xstar x e _ η _ m
    (fun t ht => inverseTail_pos η T t hT (ht.trans hm) hη)
    (fun t ht => inverseTail_mono η T t hT (ht.trans_le hm) hη0 hη) hη0
    (fun t ht => hη (t+1) (by omega) (by omega))
    (fun t ht => hstep (t+1) (by omega) (by omega))
    (fun t ht => tailSum_rec η T t hη0 (ht.trans hm))
    (fun t ht => inverseTail_mul η T t hT (ht.trans hm) hη)
    (fun t ht => hupdate t (ht.trans_le hm))

lemma stepsize_terminal_output (G : ℕ → ℝ) (η : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hη0 : η 0=0) (hη : ∀ t, 1 ≤ t → t ≤ T → 0 < η t) :
    objectivePotential G (inverseTail η T) η (tailSum η T) T=G (T+1) :=
  objectivePotential_terminal G _ η _ T (tailSum_rec η T T hη0 le_rfl)
    (inverseTail_mul η T T hT le_rfl hη) (tailSum_terminal η T)

end
end ClippedSGD.Potential
