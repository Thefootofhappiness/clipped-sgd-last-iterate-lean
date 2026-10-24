import ClippedSGD.UpperNoise

/-! Increments of the mixed martingale in the known-horizon proof: a centered stopped
square plus a linear martingale term. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
namespace ClippedSGD.MixedNoise
open UpperConcentration ClippingConditional PredictableInner
variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

lemma centered_nonnegative (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (Y : Ω → ℝ) (hY : @Measurable Ω ℝ m₀ _ Y)
    (K V : ℝ) (hK : 0 < K) (hV : 0 ≤ V)
    (hb : ∀ᵐ ω ∂ν, 0 ≤ Y ω ∧ Y ω ≤ K)
    (hmean : ν[Y|m] ≤ᵐ[ν] fun _ => V) :
    Integrable Y ν ∧
    (ν[fun ω => Y ω-ν[Y|m] ω|m] =ᵐ[ν] 0) ∧
    (∀ᵐ ω ∂ν, |Y ω-ν[Y|m] ω| ≤ K) ∧
    (ν[fun ω => (Y ω-ν[Y|m] ω)^2|m] ≤ᵐ[ν] fun _ => K*V) := by
  letI : MeasurableSpace Ω := m₀
  have hab : ∀ᵐ ω ∂ν, |Y ω| ≤ K := hb.mono (fun ω h => by simpa only [abs_of_nonneg h.1] using h.2)
  have hi := integrable_of_abs_bound ν Y hY K hab
  have hi2 : Integrable (fun ω => (Y ω)^2) ν := by
    apply integrable_of_abs_bound ν _ (hY.pow_const 2) (K^2)
    filter_upwards [hb] with ω hω
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hω.1 hK.le).mpr hω.2
  have hp := condExp_nonneg (m := m) (μ := ν) (hb.mono (fun _ h => h.1))
  have hu := condExp_mono (m := m) hi (integrable_const K) (hb.mono (fun _ h => h.2))
  rw [condExp_const hm K] at hu
  have hsq : (fun ω => (Y ω)^2) ≤ᵐ[ν] fun ω => K*Y ω := by
    filter_upwards [hb] with ω hω
    nlinarith [mul_nonneg hω.1 (sub_nonneg.mpr hω.2)]
  have hm2 := condExp_mono (m := m) hi2 (hi.const_mul K) hsq
  have hscale := condExp_smul K Y m (μ := ν)
  change ν[fun ω => K*Y ω|m] =ᵐ[ν] fun ω => K*ν[Y|m] ω at hscale
  have hvariance := conditional_centered_second_le ν m hm Y hi
    (by simpa only [Real.norm_eq_abs, sq_abs] using hi2)
  simp only [Real.norm_eq_abs, sq_abs] at hvariance
  refine ⟨hi, centered_condExp_zero ν m hm Y hi, ?_, ?_⟩
  · filter_upwards [hb,hp,hu] with ω hbω hpω huω
    change 0 ≤ ν[Y|m] ω at hpω
    exact abs_le.mpr ⟨by linarith [hbω.1,hbω.2], by linarith [hbω.1,hbω.2]⟩
  · filter_upwards [hvariance,hm2,hscale,hmean] with ω hvω hmω hsω hbω
    change ν[fun ω => (Y ω)^2|m] ω ≤ ν[fun ω => K*Y ω|m] ω at hmω
    rw [hsω] at hmω
    exact hvω.trans (hmω.trans (mul_le_mul_of_nonneg_left hbω hK.le))

/-- A conditional triangle inequality for second moments, from a weighted square
inequality. -/
lemma conditional_mixed_second (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : MeasurableSpace Ω) (D H : Ω → ℝ) (hD : @Measurable Ω ℝ m₀ _ D) (hH : @Measurable Ω ℝ m₀ _ H)
    (d h V bD bH : ℝ) (hd : 0 < d) (hh : 0 < h) (hV : 0 ≤ V)
    (hDb : ∀ᵐ ω ∂ν, |D ω| ≤ bD) (hHb : ∀ᵐ ω ∂ν, |H ω| ≤ bH)
    (hD2 : ν[fun ω => (D ω)^2|m] ≤ᵐ[ν] fun _ => d^2*V)
    (hH2 : ν[fun ω => (H ω)^2|m] ≤ᵐ[ν] fun _ => h^2*V) :
    ν[fun ω => (D ω+H ω)^2|m] ≤ᵐ[ν] fun _ => (d+h)^2*V := by
  letI : MeasurableSpace Ω := m₀
  have intsq (X : Ω → ℝ) (hmX : Measurable X) (B : ℝ)
      (hB : ∀ᵐ ω ∂ν, |X ω| ≤ B) : Integrable (fun ω => (X ω)^2) ν := by
    apply integrable_of_abs_bound ν _ (hmX.pow_const 2) (B^2)
    filter_upwards [hB] with ω hω
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hω)).mpr hω
  have hiD := intsq D hD bD hDb
  have hiH := intsq H hH bH hHb
  have hiX := intsq (fun ω => D ω+H ω) (hD.add hH) (bD+bH) (by
    filter_upwards [hDb,hHb] with ω hdω hhω
    exact (abs_add _ _).trans (add_le_add hdω hhω))
  have hpoint : (fun ω => (D ω+H ω)^2) ≤ᵐ[ν]
      fun ω => ((d+h)/d)*(D ω)^2+((d+h)/h)*(H ω)^2 := by
    apply Eventually.of_forall
    intro ω
    have hsq := sq_nonneg (h*D ω-d*H ω)
    apply (mul_le_mul_iff_of_pos_right (mul_pos hd hh)).mp
    field_simp
    nlinarith only [hsq]
  have hc := condExp_mono (m := m) hiX
    ((hiD.const_mul ((d+h)/d)).add (hiH.const_mul ((d+h)/h))) hpoint
  have ha := condExp_add (hiD.const_mul ((d+h)/d)) (hiH.const_mul ((d+h)/h)) m
  have hsD := condExp_smul ((d+h)/d) (fun ω => (D ω)^2) m (μ := ν)
  have hsH := condExp_smul ((d+h)/h) (fun ω => (H ω)^2) m (μ := ν)
  filter_upwards [hc,ha,hsD,hsH,hD2,hH2] with ω hcω haω hdω hhω hDω hHω
  change ν[fun ω => (D ω+H ω)^2|m] ω ≤
    ν[fun ω => ((d+h)/d)*(D ω)^2+((d+h)/h)*(H ω)^2|m] ω at hcω
  change ν[fun ω => ((d+h)/d)*(D ω)^2+((d+h)/h)*(H ω)^2|m] ω =
    ν[fun ω => ((d+h)/d)*(D ω)^2|m] ω + ν[fun ω => ((d+h)/h)*(H ω)^2|m] ω at haω
  change ν[fun ω => ((d+h)/d)*(D ω)^2|m] ω = ((d+h)/d)*ν[fun ω => (D ω)^2|m] ω at hdω
  change ν[fun ω => ((d+h)/h)*(H ω)^2|m] ω = ((d+h)/h)*ν[fun ω => (H ω)^2|m] ω at hhω
  rw [haω,hdω,hhω] at hcω
  apply hcω.trans
  have hcD := mul_le_mul_of_nonneg_left hDω (by positivity : 0 ≤ (d+h)/d)
  have hcH := mul_le_mul_of_nonneg_left hHω (by positivity : 0 ≤ (d+h)/h)
  have he : (d+h)/d*(d^2*V)+(d+h)/h*(h^2*V)=(d+h)^2*V := by field_simp; ring
  exact (add_le_add hcD hcH).trans_eq he


/-- Conditional mean, range, and conditional second moment of a centered square plus a
martingale increment; `a` and `A` bound the coefficients. -/
lemma mixed_increment_properties (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (Y H : Ω → ℝ)
    (hY : @Measurable Ω ℝ m₀ _ Y) (hH : @Measurable Ω ℝ m₀ _ H)
    (Λ V α a A : ℝ) (hΛ : 0 < Λ) (hV : 0 ≤ V)
    (hα : 0 ≤ α) (ha : 0 < a) (hαa : α ≤ a) (hA : 0 < A)
    (hYb : ∀ᵐ ω ∂ν, 0 ≤ Y ω ∧ Y ω ≤ 4*Λ^2)
    (hYm : ν[Y|m] ≤ᵐ[ν] fun _ => V)
    (hHm : ν[H|m] =ᵐ[ν] 0)
    (hHb : ∀ᵐ ω ∂ν, |H ω| ≤ 2*Λ*A)
    (hH2 : ν[fun ω => (H ω)^2|m] ≤ᵐ[ν] fun _ => A^2*V) :
    (ν[fun ω => α*(Y ω-ν[Y|m] ω)+H ω|m] =ᵐ[ν] 0) ∧
    (∀ᵐ ω ∂ν, |α*(Y ω-ν[Y|m] ω)+H ω| ≤ 4*Λ^2*a+2*Λ*A) ∧
    (ν[fun ω => (α*(Y ω-ν[Y|m] ω)+H ω)^2|m] ≤ᵐ[ν]
      fun _ => (2*Λ*a+A)^2*V) := by
  letI : MeasurableSpace Ω := m₀
  obtain ⟨hiY,hmD,hbD,hvD⟩ := centered_nonnegative ν m hm Y hY (4*Λ^2) V
    (by positivity) hV hYb hYm
  let D : Ω → ℝ := fun ω => α*(Y ω-ν[Y|m] ω)
  have hdmeas : Measurable D := (hY.sub ((stronglyMeasurable_condExp (m := m)).mono hm).measurable).const_mul α
  have hbscaled : ∀ᵐ ω ∂ν, |D ω| ≤ 4*Λ^2*a := by
    filter_upwards [hbD] with ω hω
    dsimp only [D]
    rw [abs_mul,abs_of_nonneg hα]
    exact (mul_le_mul_of_nonneg_left hω hα).trans (by nlinarith [sq_nonneg Λ])
  have hvscaled : ν[fun ω => (D ω)^2|m] ≤ᵐ[ν] fun _ => (2*Λ*a)^2*V := by
    have he : (fun ω => (D ω)^2)=(fun ω => α^2*(Y ω-ν[Y|m] ω)^2) := by funext ω; dsimp [D]; ring
    rw [he]
    have hs := condExp_smul (α^2) (fun ω => (Y ω-ν[Y|m] ω)^2) m (μ := ν)
    change ν[fun ω => α^2*(Y ω-ν[Y|m] ω)^2|m] =ᵐ[ν]
      fun ω => α^2*ν[fun ω => (Y ω-ν[Y|m] ω)^2|m] ω at hs
    filter_upwards [hs,hvD] with ω hsω hvω
    rw [hsω]
    have hc := mul_le_mul_of_nonneg_left hvω (sq_nonneg α)
    apply hc.trans
    have hsqa : α^2 ≤ a^2 := (sq_le_sq₀ hα ha.le).mpr hαa
    have ht := mul_le_mul_of_nonneg_right hsqa (show 0 ≤ 4*Λ^2*V by positivity)
    nlinarith only [ht]
  have hiD : Integrable D ν := (hiY.sub integrable_condExp).const_mul α
  have hiH := integrable_of_abs_bound ν H hH (2*Λ*A) hHb
  refine ⟨?_, ?_, ?_⟩
  · have hs := condExp_smul α (fun ω => Y ω-ν[Y|m] ω) m (μ := ν)
    have hh := condExp_add hiD hiH m
    filter_upwards [hs,hh,hmD,hHm] with ω hsω hhω hmω hHω
    change ν[fun ω => D ω+H ω|m] ω=ν[D|m] ω+ν[H|m] ω at hhω
    change ν[D|m] ω=α*ν[fun ω => Y ω-ν[Y|m] ω|m] ω at hsω
    change ν[fun ω => D ω+H ω|m] ω=0
    rw [hhω,hsω,hmω,hHω]
    simp
  · filter_upwards [hbscaled,hHb] with ω hdω hhω
    exact (abs_add _ _).trans (add_le_add hdω hhω)
  · exact conditional_mixed_second ν m D H hdmeas hH (2*Λ*a) A V _ _
      (by positivity) hA hV hbscaled hHb hvscaled hH2

end ClippedSGD.MixedNoise
