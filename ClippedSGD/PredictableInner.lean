import ClippedSGD.ClippingConditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace
namespace ClippedSGD.PredictableInner
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]
  (m : MeasurableSpace Ω) (hm : m ≤ m₀)
include hm

/-- A predictable vector can be pulled out of the conditional expectation of an inner
product. -/
theorem condExp_inner (e a : Ω → E) (he : Integrable e ν)
    (ha : StronglyMeasurable[m] a) (hi : Integrable (fun ω => ⟪a ω,e ω⟫_ℝ) ν) :
    ν[fun ω => ⟪a ω,e ω⟫_ℝ|m] =ᵐ[ν] fun ω => ⟪a ω,ν[e|m] ω⟫_ℝ := by
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
  have hik : ∀ᵐ ω ∂ν, Integrable (fun y : E => y) (κ ω) :=
    hmap.condDistrib_ae (mβ := m) hXa he.1.aemeasurable
  have hb := condExp_ae_eq_integral_condDistrib' (X := id) hX he
  have hfun : @StronglyMeasurable (Ω × E) ℝ _ (m.prod inferInstance)
      (fun q => ⟪a q.1,q.2⟫_ℝ) := (ha.comp_measurable measurable_fst).inner hsnd
  have hc := condExp_prod_ae_eq_integral_condDistrib hX he.1.aemeasurable hfun hi
  simp only [MeasurableSpace.comap_id, id_eq] at hb hc
  filter_upwards [hik, hb, hc] with ω hikω hbω hcω
  rw [hcω, hbω]
  exact integral_inner hikω (a ω)

lemma integrable_inner_of_bound (e a : Ω → E) (he : Integrable e ν)
    (ha : StronglyMeasurable[m] a) (A : ℝ) (hA : ∀ᵐ ω ∂ν, ‖a ω‖ ≤ A) :
    Integrable (fun ω => ⟪a ω,e ω⟫_ℝ) ν := by
  letI : MeasurableSpace Ω := m₀
  apply Integrable.mono' (he.norm.const_mul A)
    (((ha.mono hm).aestronglyMeasurable).inner he.1)
  filter_upwards [hA] with ω hω
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

lemma conditional_inner_variance (e a : Ω → E) (he : Integrable e ν)
    (he2 : Integrable (fun ω => ‖e ω‖^2) ν) (ha : StronglyMeasurable[m] a)
    (A V : ℝ) (hA0 : 0 ≤ A) (hA : ∀ᵐ ω ∂ν, ‖a ω‖ ≤ A)
    (hsecond : ν[fun ω => ‖e ω‖^2|m] ≤ᵐ[ν] fun _ => V) :
    Integrable (fun ω => ⟪a ω,e ω⟫_ℝ^2) ν ∧
      (ν[fun ω => ⟪a ω,e ω⟫_ℝ^2|m] ≤ᵐ[ν] fun _ => A^2*V) := by
  letI : MeasurableSpace Ω := m₀
  have hbound : (fun ω => ⟪a ω,e ω⟫_ℝ^2) ≤ᵐ[ν] fun ω => A^2*‖e ω‖^2 := by
    filter_upwards [hA] with ω hω
    have hh := (norm_inner_le_norm (𝕜 := ℝ) (a ω) (e ω)).trans
      (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
    rw [Real.norm_eq_abs] at hh
    have hn : 0 ≤ A*‖e ω‖ := by positivity
    have hs := (sq_le_sq₀ (abs_nonneg ⟪a ω,e ω⟫_ℝ) hn).mpr hh
    simpa only [sq_abs, mul_pow] using hs
  have hi : Integrable (fun ω => ⟪a ω,e ω⟫_ℝ^2) ν := by
    apply Integrable.mono' (he2.const_mul (A^2))
      ((((ha.mono hm).aestronglyMeasurable).inner he.1).pow 2)
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ⟪a ω,e ω⟫_ℝ)] using hω
  refine ⟨hi, ?_⟩
  have hh := condExp_mono (m := m) hi (he2.const_mul (A^2)) hbound
  have hs := condExp_smul (A^2) (fun ω => ‖e ω‖^2) m (μ := ν)
  change ν[fun ω => A^2*‖e ω‖^2|m] =ᵐ[ν] fun ω => A^2*ν[fun ω => ‖e ω‖^2|m] ω at hs
  filter_upwards [hh, hs, hsecond] with ω hhω hsω hvω
  rw [hsω] at hhω
  exact hhω.trans (mul_le_mul_of_nonneg_left hvω (sq_nonneg _))

lemma centered_condExp_zero (e : Ω → E) (he : Integrable e ν) :
    ν[fun ω => e ω-ν[e|m] ω|m] =ᵐ[ν] 0 := by
  letI : MeasurableSpace Ω := m₀
  have hs := condExp_sub he (integrable_condExp (m := m) (f := e) (μ := ν)) m
  have hid := condExp_of_stronglyMeasurable hm
    (stronglyMeasurable_condExp (m := m) (f := e) (μ := ν))
    (integrable_condExp (m := m) (f := e) (μ := ν))
  rw [hid] at hs
  filter_upwards [hs] with ω hω
  simpa only [Pi.sub_apply, sub_self, Pi.zero_apply] using hω

lemma inner_condExp_zero (e a : Ω → E) (he : Integrable e ν)
    (ha : StronglyMeasurable[m] a) (A : ℝ) (hA : ∀ᵐ ω ∂ν, ‖a ω‖ ≤ A)
    (hmean : ν[e|m] =ᵐ[ν] 0) : ν[fun ω => ⟪a ω,e ω⟫_ℝ|m] =ᵐ[ν] 0 := by
  letI : MeasurableSpace Ω := m₀
  have hc := condExp_inner ν m hm e a he ha (integrable_inner_of_bound ν m hm e a he ha A hA)
  filter_upwards [hc, hmean] with ω hcω hmω
  simpa only [hmω, Pi.zero_apply, inner_zero_right] using hcω

end
end ClippedSGD.PredictableInner
