import ClippedSGD
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! Radial clipping, its pointwise estimates, and the second-moment centering identity. -/
open Set MeasureTheory
open scoped InnerProductSpace
namespace ClippedSGD.Clipping
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def clip (Λ : ℝ) (g : E) : E := if ‖g‖ ≤ Λ then g else (Λ/‖g‖) • g

lemma clip_eq_self (Λ : ℝ) (g : E) (hg : ‖g‖ ≤ Λ) : clip Λ g = g := by simp [clip, hg]
lemma clip_zero (Λ : ℝ) (hΛ : 0 ≤ Λ) : clip Λ (0 : E) = 0 := by simp [clip, hΛ]

lemma norm_clip (Λ : ℝ) (hΛ : 0 ≤ Λ) (g : E) : ‖clip Λ g‖ ≤ Λ := by
  by_cases hg : ‖g‖ ≤ Λ
  · simpa [clip, hg] using hg
  · have hg0 : 0 < ‖g‖ := lt_of_le_of_lt hΛ (lt_of_not_ge hg)
    rw [clip, if_neg hg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hg0.ne']

/-- Clipping cannot increase distance to any point in the clipping ball. -/
lemma error_contracts (Λ : ℝ) (hΛ : 0 ≤ Λ) (g μ : E) (hμ : ‖μ‖ ≤ Λ) :
    ‖clip Λ g-μ‖ ≤ ‖g-μ‖ := by
  by_cases hg : ‖g‖ ≤ Λ
  · rw [clip_eq_self Λ g hg]
  have hgΛ : Λ < ‖g‖ := lt_of_not_ge hg
  have hg0 : 0 < ‖g‖ := lt_of_le_of_lt hΛ hgΛ
  let c := Λ/‖g‖
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one hg0).mpr hgΛ.le
  have hcn : c*‖g‖ = Λ := div_mul_cancel₀ _ hg0.ne'
  have hi : ⟪g, μ⟫_ℝ ≤ ‖g‖*Λ :=
    (real_inner_le_norm g μ).trans (mul_le_mul_of_nonneg_left hμ (norm_nonneg _))
  have hi' := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hc1)
  have hsq : ‖c • g-μ‖^2 ≤ ‖g-μ‖^2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc0, real_inner_smul_left]
    nlinarith [sq_nonneg (‖g‖-Λ)]
  rw [clip, if_neg hg]
  nlinarith [norm_nonneg (c • g-μ), norm_nonneg (g-μ)]

lemma error_range (Λ : ℝ) (hΛ : 0 ≤ Λ) (g μ : E) (hμ : ‖μ‖ ≤ Λ/2) :
    ‖clip Λ g-μ‖ ≤ 3*Λ/2 := by
  have h := (norm_sub_le (clip Λ g) μ).trans (add_le_add (norm_clip Λ hΛ g) hμ)
  linarith

lemma correction_norm (Λ : ℝ) (hΛ : 0 ≤ Λ) (g : E) (hg : Λ < ‖g‖) :
    ‖clip Λ g-g‖ = ‖g‖-Λ := by
  have hg0 : 0 < ‖g‖ := lt_of_le_of_lt hΛ hg
  have he : (Λ/‖g‖) • g-g = (Λ/‖g‖-1) • g := by rw [sub_smul, one_smul]
  rw [clip, if_neg (not_le.mpr hg), he, norm_smul,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ((div_le_one hg0).mpr hg.le))]
  have hn := div_mul_cancel₀ Λ hg0.ne'
  nlinarith

lemma correction_le_noise (Λ : ℝ) (hΛ : 0 ≤ Λ) (g μ : E) (hμ : ‖μ‖ ≤ Λ) :
    ‖clip Λ g-g‖ ≤ ‖g-μ‖ := by
  by_cases hg : ‖g‖ ≤ Λ
  · rw [clip_eq_self Λ g hg, sub_self, norm_zero]
    exact norm_nonneg _
  · rw [correction_norm Λ hΛ g (lt_of_not_ge hg)]
    have h := norm_sub_norm_le g μ
    linarith

lemma large_noise_on_clipping (Λ : ℝ) (g μ : E) (hμ : ‖μ‖ ≤ Λ/2)
    (hg : Λ < ‖g‖) : Λ/2 < ‖g-μ‖ := by
  have h := norm_sub_norm_le g μ
  linarith

/-- `‖clip Λ g - g‖ ≤ (Λ/2)^(1-p) ‖g - μ‖^p` whenever `‖μ‖ ≤ Λ/2`. -/
lemma correction_moment (Λ p : ℝ) (hΛ : 0 < Λ) (hp : 1 ≤ p)
    (g μ : E) (hμ : ‖μ‖ ≤ Λ/2) :
    ‖clip Λ g-g‖ ≤ (Λ/2)^(1-p)*‖g-μ‖^p := by
  by_cases hg : ‖g‖ ≤ Λ
  · rw [clip_eq_self Λ g hg, sub_self, norm_zero]
    positivity
  · have hx : Λ/2 < ‖g-μ‖ := large_noise_on_clipping Λ g μ hμ (lt_of_not_ge hg)
    have hx0 : 0 < ‖g-μ‖ := lt_trans (by positivity) hx
    apply (correction_le_noise Λ hΛ.le g μ (by linarith)).trans
    calc
      _ = ‖g-μ‖^(1-p)*‖g-μ‖^p := by rw [← Real.rpow_add hx0]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by positivity) hx.le (by linarith))
        (Real.rpow_nonneg (norm_nonneg _) _)

lemma error_second_moment (Λ p : ℝ) (hΛ : 0 < Λ) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (g μ : E) (hμ : ‖μ‖ ≤ Λ/2) :
    ‖clip Λ g-μ‖^2 ≤ (3*Λ/2)^(2-p)*‖g-μ‖^p := by
  have he := error_range Λ hΛ.le g μ hμ
  have hc := error_contracts Λ hΛ.le g μ (by linarith)
  by_cases hz : ‖clip Λ g-μ‖ = 0
  · rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    positivity
  · have hpos : 0 < ‖clip Λ g-μ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    calc
      _ = ‖clip Λ g-μ‖^(2-p)*‖clip Λ g-μ‖^p := by
        rw [← Real.rpow_add hpos]
        norm_num
      _ ≤ _ := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) he (by linarith))
        (Real.rpow_le_rpow (norm_nonneg _) hc hp)
        (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_clip (Λ : ℝ) : Measurable (clip (E := E) Λ) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    measurable_id ((measurable_const.div measurable_norm).smul measurable_id)

variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

lemma integrable_clip (Λ : ℝ) (hΛ : 0 ≤ Λ) (g : Ω → E) (hg : Measurable g) :
    Integrable (fun ω => clip Λ (g ω)) ν := by
  apply Integrable.mono' (integrable_const Λ) ((measurable_clip Λ).comp hg).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => norm_clip Λ hΛ (g ω))

lemma norm_le_one_add_rpow (x p : ℝ) (hx : 0 ≤ x) (hp : 1 ≤ p) : x ≤ 1+x^p := by
  by_cases hx1 : x ≤ 1
  · linarith [Real.rpow_nonneg hx p]
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hp
    rw [Real.rpow_one] at h
    linarith

/-- The second-moment centering identity in a Hilbert space. -/
theorem centering_identity (e : Ω → E) (he : Integrable e ν)
    (he2 : Integrable (fun ω => ‖e ω‖^2) ν) :
    (∫ ω, ‖e ω-(∫ a, e a ∂ν)‖^2 ∂ν) =
      (∫ ω, ‖e ω‖^2 ∂ν)-‖∫ a, e a ∂ν‖^2 := by
  let b := ∫ a, e a ∂ν
  have hf (ω : Ω) : ‖e ω-b‖^2 = ‖e ω‖^2-2*⟪b,e ω⟫_ℝ+‖b‖^2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  change (∫ ω, ‖e ω-b‖^2 ∂ν) = (∫ ω, ‖e ω‖^2 ∂ν)-‖b‖^2
  simp_rw [hf]
  have hi : Integrable (fun ω => 2*⟪b,e ω⟫_ℝ) ν := (he.const_inner b).const_mul 2
  have hj : Integrable (fun ω => ‖e ω‖^2-2*⟪b,e ω⟫_ℝ) ν := he2.sub hi
  rw [integral_add hj (integrable_const _),
    integral_sub he2 hi, integral_const_mul,
    integral_inner he b, integral_const]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, real_inner_self_eq_norm_sq]
  dsimp [b]
  rw [real_inner_self_eq_norm_sq]
  ring

end
end ClippedSGD.Clipping
