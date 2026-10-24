import ClippedSGD.MixedEvents
import ClippedSGD.MixedPathwise
open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.MixedLocalization
open Potential LinearSchedule FiniteHorizonPathwise Localization MixedEvents MixedPathwise
noncomputable section

lemma radius_mixed_arithmetic (R Λ ℓ B V : ℝ) (hR : 0 < R) (hΛ : 0 < Λ) (hℓ : 1 ≤ ℓ)
    (T : ℕ) (hbudget : (T : ℝ)*B ≤ 2*Λ*ℓ) (hvariance : (T : ℝ)*V ≤ 2*Λ^2*ℓ) :
    let η := R/(128*Λ*ℓ)
    R^2+7*Λ*(2*Λ*η^2+4*R*η)*ℓ+4*R*η*T*B+η^2*T*V < 13/10*R^2 := by
  obtain ⟨hη,hid,hq⟩ := scale_budgets R Λ ℓ hR hΛ hℓ
  dsimp only at *
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 4*R*(R/(128*Λ*ℓ)) by positivity)
  have hv := mul_le_mul_of_nonneg_left hvariance (sq_nonneg (R/(128*Λ*ℓ)))
  have hi := congrArg (fun a : ℝ => R*a) hid
  dsimp only at hi
  nlinarith only [hb,hv,hq,hi,sq_pos_of_pos hR]

lemma potential_mixed_arithmetic (R Λ ℓ B V : ℝ) (hR : 0 < R) (hΛ : 0 < Λ) (hℓ : 1 ≤ ℓ)
    (T : ℕ) (hbudget : (T : ℝ)*B ≤ 2*Λ*ℓ) (hvariance : (T : ℝ)*V ≤ 2*Λ^2*ℓ) :
    let η := R/(128*Λ*ℓ)
    R^2/2+7*Λ*(8*Λ*η^2+3*R*η)*ℓ+3*R*η*T*B+4*η^2*T*V < 18/25*R^2 := by
  obtain ⟨hη,hid,hq⟩ := scale_budgets R Λ ℓ hR hΛ hℓ
  dsimp only at *
  have hb := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 3*R*(R/(128*Λ*ℓ)) by positivity)
  have hv := mul_le_mul_of_nonneg_left hvariance (show 0 ≤ 4*(R/(128*Λ*ℓ))^2 by positivity)
  have hi := congrArg (fun a : ℝ => R*a) hid
  dsimp only at hi
  nlinarith only [hb,hv,hq,hi,sq_pos_of_pos hR]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- First-exit argument: if the two stopped martingale sums stay below their thresholds,
every iterate stays in the localization region. -/
theorem closure_from_mixed_events {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L R Λ ℓ B V : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hΛ : 0 < Λ) (hℓ : 1 ≤ ℓ) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (hstep : R/(128*Λ*ℓ) ≤ 1/(2*L)) (T : ℕ) (hT : 0 < T)
    (hbudget : (T : ℝ)*B ≤ 2*Λ*ℓ) (hvariance : (T : ℝ)*V ≤ 2*Λ^2*ℓ)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x e b : ℕ → E) (M : ℕ → ℝ)
    (hinitial : ‖x 1-xstar‖ ≤ R)
    (hupdate : ∀ t < T, x (t+2)=x (t+1)-step (R/(128*Λ*ℓ)) T (t+1) • (gradient f (x (t+1))+e (t+1)))
    (hbias : ∀ t < T, active (R/(128*Λ*ℓ)) R T xstar x (t+1) → ‖b (t+1)‖ ≤ B)
    (hmean : ∀ t < T, M (t+1) ≤ V)
    (hG : ∀ m ≤ T, (∑t∈Finset.range m, stopped (R/(128*Λ*ℓ)) R T xstar x
      (fun i => (step (R/(128*Λ*ℓ)) T i)^2*(‖e i‖^2-M i)-2*step (R/(128*Λ*ℓ)) T i*⟪e i-b i,radiusDirection f (R/(128*Λ*ℓ)) T xstar x i⟫_ℝ) (t+1)) ≤ 7*Λ*(2*Λ*(R/(128*Λ*ℓ))^2+4*R*(R/(128*Λ*ℓ)))*ℓ)
    (hH : ∀ m ≤ T, (∑t∈Finset.range m, stopped (R/(128*Λ*ℓ)) R T xstar x
      (fun i => potentialCoefficient (R/(128*Λ*ℓ)) T (i-1)*(‖e i‖^2-M i)+⟪e i-b i,noiseDirection (R/(128*Λ*ℓ)) T xstar x i⟫_ℝ) (t+1)) ≤ 7*Λ*(8*Λ*(R/(128*Λ*ℓ))^2+3*R*(R/(128*Λ*ℓ)))*ℓ) :
    ∀ m ≤ T, ‖x (m+1)-xstar‖^2 < 13/10*R^2 ∧
      objective f (R/(128*Λ*ℓ)) T xstar x m+energy (R/(128*Λ*ℓ)) T xstar x m < 18/25*R^2 := by
  let η := R/(128*Λ*ℓ)
  have hη : 0 < η := (scale_budgets R Λ ℓ hR hΛ hℓ).1
  have hinit : ‖x 1-xstar‖^2 ≤ R^2 := by nlinarith [norm_nonneg (x 1-xstar)]
  have active_result (m : ℕ) (hm : m ≤ T) (ha : active η R T xstar x m) :
      ‖x (m+1)-xstar‖^2 < 13/10*R^2 ∧
        objective f η T xstar x m+energy η T xstar x m < 18/25*R^2 := by
    have hb : ∀ t < m, ‖b (t+1)‖ ≤ B := by
      intro t ht
      apply hbias t (by omega)
      exact fun j hj => ha j (by omega)
    have hg := hG m hm
    have hh := hH m hm
    have heqG : (∑t∈Finset.range m, stopped η R T xstar x
        (fun i => (step η T i)^2*(‖e i‖^2-M i)-2*step η T i*⟪e i-b i,radiusDirection f η T xstar x i⟫_ℝ) (t+1))=
        ∑t∈Finset.range m, ((step η T (t+1))^2*(‖e (t+1)‖^2-M (t+1))-2*step η T (t+1)*⟪e (t+1)-b (t+1),radiusDirection f η T xstar x (t+1)⟫_ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      simpa only [Nat.add_sub_cancel] using stopped_prefix_eq η R T xstar x _ m ha (t+1) (by have := Finset.mem_range.mp ht; omega)
    have heqH : (∑t∈Finset.range m, stopped η R T xstar x
        (fun i => potentialCoefficient η T (i-1)*(‖e i‖^2-M i)+⟪e i-b i,noiseDirection η T xstar x i⟫_ℝ) (t+1))=
        ∑t∈Finset.range m, (potentialCoefficient η T t*(‖e (t+1)‖^2-M (t+1))+⟪e (t+1)-b (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      simpa only [Nat.add_sub_cancel] using stopped_prefix_eq η R T xstar x _ m ha (t+1) (by have := Finset.mem_range.mp ht; omega)
    change (∑t∈Finset.range m, stopped η R T xstar x
      (fun i => (step η T i)^2*(‖e i‖^2-M i)-2*step η T i*⟪e i-b i,radiusDirection f η T xstar x i⟫_ℝ) (t+1)) ≤ _ at hg
    change (∑t∈Finset.range m, stopped η R T xstar x
      (fun i => potentialCoefficient η T (i-1)*(‖e i‖^2-M i)+⟪e i-b i,noiseDirection η T xstar x i⟫_ℝ) (t+1)) ≤ _ at hh
    rw [heqG] at hg
    rw [heqH] at hh
    have hmR : (m : ℝ) ≤ T := by exact_mod_cast hm
    have hbg := mul_le_mul_of_nonneg_right hmR (show 0 ≤ 4*R*η*B by positivity)
    have hbh := mul_le_mul_of_nonneg_right hmR (show 0 ≤ 3*R*η*B by positivity)
    have hqg := mul_le_mul_of_nonneg_right hmR (show 0 ≤ η^2*V by positivity)
    have hqh := mul_le_mul_of_nonneg_right hmR (show 0 ≤ 4*η^2*V by positivity)
    constructor
    · have hr := radius_prefix_mixed_bound hconv hdiff L η R B V hL hη hR.le hB hV hlip hstep T m hm
        xstar hmin x e b M hupdate (fun t ht => (ha t ht).1) hb (fun t ht => hmean t (by omega))
      have hc := radius_mixed_arithmetic R Λ ℓ B V hR hΛ hℓ T hbudget hvariance
      change R^2+7*Λ*(2*Λ*η^2+4*R*η)*ℓ+4*R*η*T*B+η^2*T*V<_ at hc
      nlinarith only [hr, hc, hinit, hg, hbg, hqg]
    · have hr := potential_prefix_mixed_bound hconv hdiff L η R B V hL hη hR.le hB hV hlip hstep T m hT hm
        xstar x e b M hupdate (fun t ht => (ha t ht).2) hb (fun t ht => hmean t (by omega))
      have hc := potential_mixed_arithmetic R Λ ℓ B V hR hΛ hℓ T hbudget hvariance
      change R^2/2+7*Λ*(8*Λ*η^2+3*R*η)*ℓ+3*R*η*T*B+4*η^2*T*V<_ at hc
      have heq : (∑t∈Finset.range m, (potentialCoefficient η T t*(‖e (t+1)‖^2-M (t+1))+
          ⟪e (t+1)-b (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ)) =
          ∑t∈Finset.range m, (2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1)*(‖e (t+1)‖^2-M (t+1))+
            ⟪e (t+1)-b (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htT : t<T := by have := Finset.mem_range.mp ht; omega
        simp only [potentialCoefficient,if_pos htT]
      rw [heq] at hh
      nlinarith only [hr, hc, hinit, hh, hbh, hqh]
  intro m hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    apply active_result m hm
    intro j hj
    have hprev := ih j hj (by omega)
    have hobj := objective_nonneg f η hη T hT xstar hmin x j (by omega)
    constructor
    · nlinarith [norm_nonneg (x (j+1)-xstar), sq_pos_of_pos hR]
    · nlinarith [sq_nonneg R]

end
end ClippedSGD.MixedLocalization
