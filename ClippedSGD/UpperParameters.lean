import ClippedSGD.ClippingConditional
import ClippedSGD.Localization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds

namespace ClippedSGD.UpperParameters
noncomputable section

def threshold (L R σ p ℓ : ℝ) (T : ℕ) : ℝ := max (4*L*R) (σ*((T : ℝ)/ℓ)^(1/p))

def biasBudget (Λ σ p : ℝ) : ℝ := 2*σ^p*Λ^(1-p)
def varianceBudget (Λ σ p : ℝ) : ℝ := 2*σ^p*Λ^(2-p)

lemma threshold_pos (L R σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (T : ℕ) :
    0 < threshold L R σ p ℓ T := lt_of_lt_of_le (by positivity) (le_max_left _ _)

lemma moment_budget (L R σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 0 < p) (hℓ : 0 < ℓ) (T : ℕ) (hT : 0 < T) :
    (T : ℝ)*σ^p ≤ (threshold L R σ p ℓ T)^p*ℓ := by
  have hTr : (0 : ℝ)<T := by exact_mod_cast hT
  have hpow := Real.rpow_le_rpow (show 0 ≤ σ*((T : ℝ)/ℓ)^(1/p) by positivity)
    (le_max_right (4*L*R) (σ*((T : ℝ)/ℓ)^(1/p))) hp.le
  rw [Real.mul_rpow hσ (by positivity), ← Real.rpow_mul (by positivity : (0 : ℝ)≤(T : ℝ)/ℓ),
    div_mul_cancel₀ 1 hp.ne', Real.rpow_one] at hpow
  have hh := mul_le_mul_of_nonneg_right hpow hℓ.le
  have hid : σ^p*((T : ℝ)/ℓ)*ℓ=(T : ℝ)*σ^p := by field_simp; ring
  rw [hid] at hh
  exact hh

lemma clipping_budgets (L R σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 0 < p) (hℓ : 0 < ℓ) (T : ℕ) (hT : 0 < T) :
    let Λ := threshold L R σ p ℓ T
    0 ≤ biasBudget Λ σ p ∧ 0 ≤ varianceBudget Λ σ p ∧
      (T : ℝ)*biasBudget Λ σ p ≤ 2*Λ*ℓ ∧
      (T : ℝ)*varianceBudget Λ σ p ≤ 2*Λ^2*ℓ := by
  let Λ := threshold L R σ p ℓ T
  have hΛ : 0 < Λ := threshold_pos L R σ p ℓ hL hR T
  have hm : (T : ℝ)*σ^p ≤ Λ^p*ℓ := moment_budget L R σ p ℓ hL hR hσ hp hℓ T hT
  have hb := mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*Λ^(1-p) by positivity)
  have hv := mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*Λ^(2-p) by positivity)
  have hp1 : Λ^p*Λ^(1-p)=Λ := by rw [← Real.rpow_add hΛ]; simp
  have hp2 : Λ^p*Λ^(2-p)=Λ^2 := by rw [← Real.rpow_add hΛ]; norm_num
  have hb' : Λ^p*ℓ*(2*Λ^(1-p))=2*Λ*ℓ := by calc
    _ = 2*(Λ^p*Λ^(1-p))*ℓ := by ring
    _ = _ := by rw [hp1]
  have hv' : Λ^p*ℓ*(2*Λ^(2-p))=2*Λ^2*ℓ := by calc
    _ = 2*(Λ^p*Λ^(2-p))*ℓ := by ring
    _ = _ := by rw [hp2]
  rw [hb'] at hb
  rw [hv'] at hv
  change 0 ≤ 2*σ^p*Λ^(1-p) ∧ 0 ≤ 2*σ^p*Λ^(2-p) ∧
    (T : ℝ)*(2*σ^p*Λ^(1-p)) ≤ 2*Λ*ℓ ∧ (T : ℝ)*(2*σ^p*Λ^(2-p)) ≤ 2*Λ^2*ℓ
  refine ⟨by positivity, by positivity, ?_, ?_⟩ <;> nlinarith only [hb, hv]

lemma step_valid (L R σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (hℓ : 1 ≤ ℓ) (T : ℕ) :
    R/(128*threshold L R σ p ℓ T*ℓ) ≤ 1/(2*L) := by
  have hl : 0 < ℓ := by linarith
  have hΛ := threshold_pos L R σ p ℓ hL hR T
  have hg : 4*L*R ≤ threshold L R σ p ℓ T := le_max_left _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < 2*L)).mpr
  have hh := mul_le_mul_of_nonneg_left hℓ (show 0 ≤ 128*threshold L R σ p ℓ T by positivity)
  nlinarith

lemma stochastic_rate_identity (p ℓ : ℝ) (hp : 0 < p) (hℓ : 0 < ℓ) (T : ℕ) (hT : 0 < T) :
    ((T : ℝ)/ℓ)^(1/p)*ℓ/T=(ℓ/T)^((p-1)/p) := by
  have hTr : (0 : ℝ)<T := by exact_mod_cast hT
  have hq : 0 < ℓ/(T : ℝ) := by positivity
  rw [show ((T : ℝ)/ℓ)=(ℓ/(T : ℝ))⁻¹ by field_simp,
    Real.inv_rpow hq.le, ← Real.rpow_neg hq.le]
  calc
    _ = (ℓ/(T : ℝ))^(-(1/p))*(ℓ/(T : ℝ))^1 := by rw [Real.rpow_one]; ring
    _ = (ℓ/(T : ℝ))^(-(1/p)+1) := (Real.rpow_add hq _ _).symm
    _ = _ := by congr 1; field_simp; ring

lemma final_rate_bound (L R σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 0 < p) (hℓ : 0 < ℓ) (T : ℕ) (hT : 0 < T) :
    256*R*threshold L R σ p ℓ T*ℓ/T ≤
      1024*L*R^2*ℓ/T+256*σ*R*(ℓ/T)^((p-1)/p) := by
  have hTr : (0 : ℝ)<T := by exact_mod_cast hT
  have hmax : threshold L R σ p ℓ T ≤ 4*L*R+σ*((T : ℝ)/ℓ)^(1/p) :=
    max_le_add_of_nonneg (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hmax (show 0 ≤ 256*R*ℓ/T by positivity)
  have hid := stochastic_rate_identity p ℓ hp hℓ T hT
  have he : (256*R*ℓ/T)*(4*L*R+σ*((T : ℝ)/ℓ)^(1/p))=
      1024*L*R^2*ℓ/T+256*σ*R*(ℓ/T)^((p-1)/p) := by
    rw [← hid]
    ring
  rw [he] at hh
  convert hh using 1 <;> ring

lemma confidence_log (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ Real.log (6/δ) ∧ 3*Real.exp (-Real.log (6/δ)) ≤ δ := by
  have hpos : (0 : ℝ)<6/δ := by positivity
  constructor
  · apply (Real.le_log_iff_exp_le hpos).mpr
    apply le_trans (by linarith [Real.exp_one_lt_d9] : Real.exp 1≤6)
    apply (le_div_iff₀ hδ).mpr
    linarith
  · rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
    nlinarith

open Set Potential LinearSchedule FiniteHorizonPathwise
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The last-iterate gap bound on the localization event. -/
theorem terminal_rate_of_localized {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (L R σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ) (hp : 0 < p) (hℓ : 1 ≤ ℓ)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (T : ℕ) (hT : 0 < T) (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → E)
    (hpotential : objective f (R/(128*threshold L R σ p ℓ T*ℓ)) T xstar x T+
      energy (R/(128*threshold L R σ p ℓ T*ℓ)) T xstar x T < 18/25*R^2)
    (hradius : ‖x (T+1)-xstar‖^2 < 13/10*R^2) :
    f (x (T+1))-f xstar ≤
      min (1024*L*R^2*ℓ/T+256*σ*R*(ℓ/T)^((p-1)/p)) (13*L*R^2/20) := by
  let Λ := threshold L R σ p ℓ T
  let η := R/(128*Λ*ℓ)
  have hΛ : 0 < Λ := threshold_pos L R σ p ℓ hL hR T
  have hl : 0 < ℓ := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hTr : (0 : ℝ)<T := by exact_mod_cast hT
  have hG : 0 ≤ f (x (T+1))-f xstar := sub_nonneg.mpr (hmin _)
  have hE := energy_nonneg η hη T hT xstar x T le_rfl
  change objective f η T xstar x T+energy η T xstar x T<_ at hpotential
  rw [terminal_objective f η hη T hT] at hpotential
  have hsmall : η*T/2*(f (x (T+1))-f xstar) < R^2 := by
    nlinarith [sq_pos_of_pos hR, mul_nonneg hη.le hG]
  have hgap : f (x (T+1))-f xstar < 256*R*Λ*ℓ/T := by
    have hh := (lt_div_iff₀ (show 0 < η*T/2 by positivity)).mpr
      (by nlinarith only [hsmall] : (f (x (T+1))-f xstar)*(η*T/2)<R^2)
    convert hh using 1
    dsimp [η]
    field_simp
    <;> ring
  have hzero := Radius.gradient_zero_at_minimizer (fun y => (hdiff y).hasGradientAt) xstar hmin
  have hs := smooth_upper (fun y => (hdiff y).hasGradientAt) hlip xstar (x (T+1))
  rw [hzero, inner_zero_left, add_zero] at hs
  have hcap : f (x (T+1))-f xstar ≤ 13*L*R^2/20 := by
    have hh := mul_lt_mul_of_pos_left hradius (show 0 < L/2 by positivity)
    nlinarith only [hs, hh]
  exact le_min (hgap.le.trans (final_rate_bound L R σ p ℓ hL hR hσ hp hl T hT)) hcap

end
end ClippedSGD.UpperParameters
