import ClippedSGD.Clipping
import Mathlib.Probability.Kernel.CondDistrib

/-! Conditional bias and second-moment bounds for clipped observations. Conditional
distributions are formed for the observations, which take values in a second-countable
Hilbert space, so the underlying probability space is arbitrary. -/
open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace ClippedSGD.ClippingConditional
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]
  (m : MeasurableSpace Ω) (hm : m ≤ m₀)

include hm

/-- The conditional Jensen inequality for the norm, from the regular conditional law of
the observation. -/
theorem norm_condExp_le (f : Ω → E) (hf : Integrable f ν) :
    (fun ω => ‖ν[f|m] ω‖) ≤ᵐ[ν] ν[fun ω => ‖f ω‖|m] := by
  letI : MeasurableSpace Ω := m₀
  have hX : @Measurable Ω Ω m₀ m id := measurable_id.mono le_rfl hm
  have hv := condExp_ae_eq_integral_condDistrib' (X := id) hX hf
  have hn := condExp_ae_eq_integral_condDistrib (X := id) hX hf.1.aemeasurable
    continuous_norm.stronglyMeasurable hf.norm
  simp only [MeasurableSpace.comap_id, id_eq] at hv hn
  filter_upwards [hv, hn] with ω hω hnorm
  rw [hω, hnorm]
  exact norm_integral_le_integral_norm _

open Clipping

lemma condExp_norm_bound (f : Ω → E) (hf : Integrable f ν) (C : ℝ)
    (hbound : ∀ᵐ ω ∂ν, ‖f ω‖ ≤ C) : ∀ᵐ ω ∂ν, ‖ν[f|m] ω‖ ≤ C := by
  letI : MeasurableSpace Ω := m₀
  have hn := norm_condExp_le ν m hm f hf
  have hmono := condExp_mono (m := m) hf.norm (integrable_const C) hbound
  rw [condExp_const hm] at hmono
  exact hn.trans hmono

lemma integrable_predictable_center (Λ : ℝ) (μ : Ω → E)
    (hμ : StronglyMeasurable[m] μ) (hbound : ∀ᵐ ω ∂ν, ‖μ ω‖ ≤ Λ/2) : Integrable μ ν :=
  Integrable.mono' (integrable_const (Λ/2)) (hμ.mono hm).aestronglyMeasurable hbound

/-- The conditional bias of clipping, bounded through the conditional central `p`th
moment. -/
theorem conditional_bias (Λ p σ : ℝ) (hΛ : 0 < Λ) (hp : 1 ≤ p)
    (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ)
    (hbound : ∀ᵐ ω ∂ν, ‖μ ω‖ ≤ Λ/2)
    (hpm : Integrable (fun ω => ‖g ω-μ ω‖^p) ν)
    (hmean : ν[fun ω => g ω-μ ω|m] =ᵐ[ν] 0)
    (hmoment : ν[fun ω => ‖g ω-μ ω‖^p|m] ≤ᵐ[ν] fun _ => σ^p) :
    (fun ω => ‖ν[fun a => clip Λ (g a)-μ a|m] ω‖) ≤ᵐ[ν]
      fun _ => (Λ/2)^(1-p)*σ^p := by
  letI : MeasurableSpace Ω := m₀
  have hμint := integrable_predictable_center ν m hm Λ μ hμ hbound
  have he : Integrable (fun ω => clip Λ (g ω)-μ ω) ν :=
    (integrable_clip ν Λ hΛ.le g hg).sub hμint
  have hn : Integrable (fun ω => g ω-μ ω) ν := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hpm)
      (hg.aestronglyMeasurable.sub (hμ.mono hm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => norm_le_one_add_rpow _ p (norm_nonneg _) hp)
  have hc : Integrable (fun ω => clip Λ (g ω)-g ω) ν := by
    convert he.sub hn using 1
    ext ω
    change clip Λ (g ω)-g ω=(clip Λ (g ω)-μ ω)-(g ω-μ ω)
    abel
  have hsum := condExp_add hc hn m
  have hid : (fun ω => (clip Λ (g ω)-g ω)+(g ω-μ ω))=(fun ω => clip Λ (g ω)-μ ω) := by
    ext ω
    abel
  change ν[fun ω => (clip Λ (g ω)-g ω)+(g ω-μ ω)|m] =ᵐ[ν] _ at hsum
  rw [hid] at hsum
  have hnorm := norm_condExp_le ν m hm (fun ω => clip Λ (g ω)-g ω) hc
  have hmono := condExp_mono (m := m) hc.norm (hpm.const_mul ((Λ/2)^(1-p)))
    (hbound.mono (fun ω hω => correction_moment Λ p hΛ hp (g ω) (μ ω) hω))
  have hscale := condExp_smul ((Λ/2)^(1-p)) (fun ω => ‖g ω-μ ω‖^p) m (μ := ν)
  filter_upwards [hsum, hmean, hnorm, hmono, hscale, hmoment] with ω hs hm0 hn' hb hscl hmo
  simp only [Pi.add_apply, Pi.zero_apply] at hs hm0
  rw [hm0, add_zero] at hs
  rw [hs]
  apply hn'.trans
  apply hb.trans
  change ν[fun ω => (Λ/2)^(1-p)*‖g ω-μ ω‖^p|m] ω =
    (Λ/2)^(1-p)*ν[fun ω => ‖g ω-μ ω‖^p|m] ω at hscl
  rw [hscl]
  exact mul_le_mul_of_nonneg_left hmo (by positivity)

lemma integrable_clipped_error_sq (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ)
    (hbound : ∀ᵐ ω ∂ν, ‖μ ω‖ ≤ Λ/2) :
    Integrable (fun ω => ‖clip Λ (g ω)-μ ω‖^2) ν := by
  letI : MeasurableSpace Ω := m₀
  have hmeas : @Measurable Ω ℝ m₀ _ (fun ω => ‖clip Λ (g ω)-μ ω‖^2) :=
    (((measurable_clip Λ).comp hg).sub (hμ.mono hm).measurable).norm.pow_const 2
  apply Integrable.mono' (integrable_const ((3*Λ/2)^2)) hmeas.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (error_range Λ hΛ (g ω) (μ ω) hω) 2

/-- The conditional second moment of the clipped observation, bounded through the
conditional central `p`th moment. -/
theorem conditional_second (Λ p σ : ℝ) (hΛ : 0 < Λ) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ)
    (hbound : ∀ᵐ ω ∂ν, ‖μ ω‖ ≤ Λ/2)
    (hpm : Integrable (fun ω => ‖g ω-μ ω‖^p) ν)
    (hmoment : ν[fun ω => ‖g ω-μ ω‖^p|m] ≤ᵐ[ν] fun _ => σ^p) :
    ν[fun ω => ‖clip Λ (g ω)-μ ω‖^2|m] ≤ᵐ[ν] fun _ => (3*Λ/2)^(2-p)*σ^p := by
  letI : MeasurableSpace Ω := m₀
  have he2 := integrable_clipped_error_sq ν m hm Λ hΛ.le g μ hg hμ hbound
  have hmono := condExp_mono (m := m) he2 (hpm.const_mul ((3*Λ/2)^(2-p)))
    (hbound.mono (fun ω hω => error_second_moment Λ p hΛ hp hp2 (g ω) (μ ω) hω))
  have hscale := condExp_smul ((3*Λ/2)^(2-p)) (fun ω => ‖g ω-μ ω‖^p) m (μ := ν)
  filter_upwards [hmono, hscale, hmoment] with ω hb hscl hmo
  apply hb.trans
  change ν[fun ω => (3*Λ/2)^(2-p)*‖g ω-μ ω‖^p|m] ω =
    (3*Λ/2)^(2-p)*ν[fun ω => ‖g ω-μ ω‖^p|m] ω at hscl
  rw [hscl]
  exact mul_le_mul_of_nonneg_left hmo (by positivity)

theorem conditional_centered_range (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ)
    (hbound : ∀ᵐ ω ∂ν, ‖μ ω‖ ≤ Λ/2) :
    ∀ᵐ ω ∂ν, ‖(clip Λ (g ω)-μ ω)-ν[fun a => clip Λ (g a)-μ a|m] ω‖ ≤ 2*Λ := by
  letI : MeasurableSpace Ω := m₀
  have hc := integrable_clip ν Λ hΛ g hg
  have hμint := integrable_predictable_center ν m hm Λ μ hμ hbound
  have hs := condExp_sub hc hμint m
  rw [condExp_of_stronglyMeasurable hm hμ hμint] at hs
  have hb := condExp_norm_bound ν m hm (fun ω => clip Λ (g ω)) hc Λ
    (Filter.Eventually.of_forall (fun ω => norm_clip Λ hΛ (g ω)))
  filter_upwards [hs, hb] with ω hs hb
  change ν[fun a => clip Λ (g a)-μ a|m] ω = ν[fun a => clip Λ (g a)|m] ω-μ ω at hs
  have heq : (clip Λ (g ω)-μ ω)-ν[fun a => clip Λ (g a)-μ a|m] ω =
      clip Λ (g ω)-ν[fun a => clip Λ (g a)|m] ω := by rw [hs]; abel
  rw [heq]
  have h := (norm_sub_le (clip Λ (g ω)) (ν[fun a => clip Λ (g a)|m] ω)).trans
    (add_le_add (norm_clip Λ hΛ (g ω)) hb)
  linarith

/-- The conditional variance identity in a Hilbert space. -/
theorem conditional_centering_identity (e : Ω → E) (he : Integrable e ν)
    (he2 : Integrable (fun ω => ‖e ω‖^2) ν) :
    ν[fun ω => ‖e ω-ν[e|m] ω‖^2|m] =ᵐ[ν]
      fun ω => ν[fun a => ‖e a‖^2|m] ω-‖ν[e|m] ω‖^2 := by
  letI : MeasurableSpace Ω := m₀
  have hX : @Measurable Ω Ω m₀ m id := measurable_id.mono le_rfl hm
  let κ : @Kernel Ω E m _ := @condDistrib Ω Ω E _ _ _ m₀ m e id ν _
  letI : MeasurableSpace (Ω × E) := m.prod inferInstance
  let joint : @Measure (Ω × E) (m.prod inferInstance) :=
    @Measure.map Ω (Ω × E) m₀ (m.prod inferInstance) (fun ω => (ω,e ω)) ν
  have hXa : @AEMeasurable Ω Ω m m₀ id ν := @Measurable.aemeasurable Ω Ω m₀ m id ν hX
  have hjoint : AEMeasurable (fun ω => (ω,e ω)) ν :=
    @AEMeasurable.prodMk Ω Ω E m₀ m _ ν id e hXa he.1.aemeasurable
  have hsnd : @StronglyMeasurable (Ω × E) E _ (m.prod inferInstance) Prod.snd :=
    stronglyMeasurable_id.comp_measurable measurable_snd
  have hmap : Integrable (fun q : Ω × E => q.2) joint :=
    (integrable_map_measure hsnd.aestronglyMeasurable hjoint).mpr he
  have hsqmap : Integrable (fun q : Ω × E => ‖q.2‖^2) joint :=
    (integrable_map_measure (hsnd.norm.pow 2).aestronglyMeasurable hjoint).mpr he2
  have hi : ∀ᵐ ω ∂ν, Integrable (fun y : E => y) (κ ω) :=
    hmap.condDistrib_ae (mβ := m) hXa he.1.aemeasurable
  have hi2 : ∀ᵐ ω ∂ν, Integrable (fun y : E => ‖y‖^2) (κ ω) :=
    hsqmap.condDistrib_ae (mβ := m) hXa he.1.aemeasurable
  have hb := condExp_ae_eq_integral_condDistrib' (X := id) hX he
  have hsecond := condExp_ae_eq_integral_condDistrib (X := id) hX he.1.aemeasurable
    (continuous_norm.pow 2).stronglyMeasurable he2
  have heL2 := (memLp_two_iff_integrable_sq_norm he.1).mpr he2
  have huL2 := heL2.sub (heL2.condExp (m := m))
  have hu2 : Integrable (fun ω => ‖e ω-ν[e|m] ω‖^2) ν := huL2.integrable_norm_pow (by norm_num)
  have hbm : StronglyMeasurable[m] (ν[e|m]) := stronglyMeasurable_condExp
  have hfun : @StronglyMeasurable (Ω × E) ℝ _ (m.prod inferInstance)
      (fun q => ‖q.2-ν[e|m] q.1‖^2) :=
    (hsnd.sub (hbm.comp_measurable measurable_fst)).norm.pow 2
  have hcenter := condExp_prod_ae_eq_integral_condDistrib hX he.1.aemeasurable hfun hu2
  simp only [MeasurableSpace.comap_id, id_eq] at hb hsecond hcenter
  filter_upwards [hi, hi2, hb, hsecond, hcenter] with ω hiω hi2ω hbω hsω hcω
  rw [hcω, hbω, hsω]
  exact centering_identity (κ ω) (fun y : E => y) hiω hi2ω

lemma conditional_centered_second_le (e : Ω → E) (he : Integrable e ν)
    (he2 : Integrable (fun ω => ‖e ω‖^2) ν) :
    ν[fun ω => ‖e ω-ν[e|m] ω‖^2|m] ≤ᵐ[ν] ν[fun a => ‖e a‖^2|m] := by
  letI : MeasurableSpace Ω := m₀
  filter_upwards [conditional_centering_identity ν m hm e he he2] with ω hω
  rw [hω]
  exact sub_le_self _ (sq_nonneg _)

/-- Estimates for the clipped observation error, set to zero off a predictable event on
which the gradient is bounded. -/
theorem stopped_clipping_estimates (Λ p σ : ℝ) (hΛ : 0 < Λ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g)
    (hμ : StronglyMeasurable[m] μ) (s : Set Ω) (hs : MeasurableSet[m] s)
    (hbound : ∀ᵐ ω ∂ν, ω ∈ s → ‖μ ω‖ ≤ Λ/2)
    (hpm : Integrable (fun ω => ‖g ω-μ ω‖^p) ν)
    (hmean : ν[fun ω => g ω-μ ω|m] =ᵐ[ν] 0)
    (hmoment : ν[fun ω => ‖g ω-μ ω‖^p|m] ≤ᵐ[ν] fun _ => σ^p) :
    let e := s.indicator (fun ω => clip Λ (g ω)-μ ω)
    Integrable e ν ∧ Integrable (fun ω => ‖e ω‖^2) ν ∧
      (∀ᵐ ω ∂ν, ‖e ω‖ ≤ 3*Λ/2) ∧
      ((fun ω => ‖ν[e|m] ω‖) ≤ᵐ[ν] fun _ => (Λ/2)^(1-p)*σ^p) ∧
      (ν[fun ω => ‖e ω‖^2|m] ≤ᵐ[ν] fun _ => (3*Λ/2)^(2-p)*σ^p) ∧
      (∀ᵐ ω ∂ν, ‖e ω-ν[e|m] ω‖ ≤ 2*Λ) ∧
      (ν[fun ω => ‖e ω-ν[e|m] ω‖^2|m] ≤ᵐ[ν] ν[fun ω => ‖e ω‖^2|m]) := by
  letI : MeasurableSpace Ω := m₀
  have hs0 : MeasurableSet s := hm _ hs
  have hgs : Measurable (s.indicator g) := hg.indicator hs0
  have hμs : StronglyMeasurable[m] (s.indicator μ) := hμ.indicator hs
  have hμsb : ∀ᵐ ω ∂ν, ‖s.indicator μ ω‖ ≤ Λ/2 := by
    filter_upwards [hbound] with ω hω
    by_cases hx : ω ∈ s
    · simpa [hx] using hω hx
    · simp only [Set.indicator_of_not_mem hx, norm_zero]
      positivity
  have hp0 : 0 < p := by linarith
  have hpow : (fun ω => ‖s.indicator g ω-s.indicator μ ω‖^p)=
      s.indicator (fun ω => ‖g ω-μ ω‖^p) := by
    funext ω
    by_cases hx : ω ∈ s
    · simp [hx]
    · simp [hx, Real.zero_rpow hp0.ne']
  have hpm' : Integrable (fun ω => ‖s.indicator g ω-s.indicator μ ω‖^p) ν := by
    rw [hpow]
    exact hpm.indicator hs0
  have hn : Integrable (fun ω => g ω-μ ω) ν := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hpm)
      (hg.aestronglyMeasurable.sub (hμ.mono hm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => norm_le_one_add_rpow _ p (norm_nonneg _) hp)
  have hmean' : ν[fun ω => s.indicator g ω-s.indicator μ ω|m] =ᵐ[ν] 0 := by
    rw [← Set.indicator_sub]
    filter_upwards [condExp_indicator hn hs, hmean] with ω hc hm0
    rw [hc]
    by_cases hx : ω ∈ s <;> simp [hx, hm0]
  have hmoment' : ν[fun ω => ‖s.indicator g ω-s.indicator μ ω‖^p|m] ≤ᵐ[ν] fun _ => σ^p := by
    rw [hpow]
    filter_upwards [condExp_indicator hpm hs, hmoment] with ω hc hmo
    rw [hc]
    by_cases hx : ω ∈ s
    · simpa [hx] using hmo
    · simp only [Set.indicator_of_not_mem hx]
      exact Real.rpow_nonneg hσ p
  have heq : (fun ω => clip Λ (s.indicator g ω)-s.indicator μ ω)=
      s.indicator (fun ω => clip Λ (g ω)-μ ω) := by
    funext ω
    by_cases hx : ω ∈ s <;> simp [hx, clip_zero Λ hΛ.le]
  have hei : Integrable (fun ω => clip Λ (s.indicator g ω)-s.indicator μ ω) ν :=
    (integrable_clip ν Λ hΛ.le _ hgs).sub (integrable_predictable_center ν m hm Λ _ hμs hμsb)
  have hei2 := integrable_clipped_error_sq ν m hm Λ hΛ.le _ _ hgs hμs hμsb
  have herange := hμsb.mono (fun ω hω => error_range Λ hΛ.le (s.indicator g ω) (s.indicator μ ω) hω)
  have hebias := conditional_bias ν m hm Λ p σ hΛ hp _ _ hgs hμs hμsb hpm' hmean' hmoment'
  have hesecond := conditional_second ν m hm Λ p σ hΛ (by linarith) hp2 _ _ hgs hμs hμsb hpm' hmoment'
  have hecenter := conditional_centered_range ν m hm Λ hΛ.le _ _ hgs hμs hμsb
  have hevariance := conditional_centered_second_le ν m hm _ hei hei2
  rw [heq] at hei hebias
  have heqp : ∀ ω, clip Λ (s.indicator g ω)-s.indicator μ ω=
      s.indicator (fun ω => clip Λ (g ω)-μ ω) ω := congrFun heq
  simp_rw [heqp] at hei2 herange hesecond hecenter hevariance
  exact ⟨hei, hei2, herange, hebias, hesecond, hecenter, hevariance⟩

omit hm in
lemma bias_factor_bound (Λ p : ℝ) (hΛ : 0 < Λ) (hp2 : p ≤ 2) :
    (Λ/2)^(1-p) ≤ 2*Λ^(1-p) := by
  have hhalf : (1/2 : ℝ)^(1-p) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ)<1/2)
      (by norm_num : (1/2 : ℝ)≤1) (by linarith : (-1 : ℝ)≤1-p)
    norm_num at h ⊢
    exact h
  rw [div_eq_mul_inv, Real.mul_rpow hΛ.le (by norm_num : (0 : ℝ)≤2⁻¹)]
  simpa only [one_div, mul_comm] using
    mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hΛ.le (1-p))

omit hm in
lemma second_factor_bound (Λ p : ℝ) (hΛ : 0 < Λ) (hp : 1 ≤ p) :
    (3*Λ/2)^(2-p) ≤ 2*Λ^(2-p) := by
  have hratio : (3/2 : ℝ)^(2-p) ≤ 2 := by
    have h := Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ)≤3/2)
      (by linarith : 2-p≤1)
    linarith
  rw [show 3*Λ/2=Λ*(3/2) by ring, Real.mul_rpow hΛ.le (by norm_num : (0 : ℝ)≤3/2)]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hΛ.le (2-p))

end
end ClippedSGD.ClippingConditional
