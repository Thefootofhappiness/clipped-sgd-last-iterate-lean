import ClippedSGD.ClippingConditional
import ClippedSGD.PredictableInner

/-! Global decomposition of a clipped stochastic gradient (`lem:global-clipping`):
without any bound on the true gradient `μ`, writes `clip Λ g = A • μ + ε + u` where
`A = E[clipFactor Λ g | m] ∈ [0, 1]`, `‖ε‖ ≤ σ^p Λ^(1-p)`, `‖u‖ ≤ 2 Λ`, and
`E[‖u‖^2 | m] ≤ (2 Λ)^(2-p) σ^p`. -/
open Set MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace ClippedSGD.GlobalClipping
open Clipping ClippingConditional PredictableInner
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Scalar clipping factor `α(v) = min(1, Λ / ‖v‖)` (with `α(0) = 1`). -/
def scalarFactor (Λ r : ℝ) : ℝ := if r ≤ Λ then 1 else Λ / r

/-- Vector clipping factor `α(v) = scalarFactor Λ ‖v‖`. -/
def clipFactor (Λ : ℝ) (v : E) : ℝ := scalarFactor Λ ‖v‖

lemma clip_eq_clipFactor_smul (Λ : ℝ) (v : E) :
    clip Λ v = clipFactor Λ v • v := by
  unfold clip clipFactor scalarFactor
  split_ifs with h
  · simp
  · rfl

lemma scalarFactor_bounds (Λ r : ℝ) (hΛ : 0 ≤ Λ) (hr : 0 ≤ r) :
    0 ≤ scalarFactor Λ r ∧ scalarFactor Λ r ≤ 1 := by
  unfold scalarFactor
  split_ifs with h
  · exact ⟨ zero_le_one, le_rfl ⟩
  · have hrpos : 0 < r := lt_of_le_of_lt hΛ (lt_of_not_ge h)
    exact ⟨ div_nonneg hΛ hr, (div_le_one hrpos).mpr (le_of_not_ge h) ⟩

lemma clipFactor_bounds (Λ : ℝ) (hΛ : 0 ≤ Λ) (v : E) :
    0 ≤ clipFactor Λ v ∧ clipFactor Λ v ≤ 1 :=
  scalarFactor_bounds Λ ‖v‖ hΛ (norm_nonneg v)

lemma scalarFactor_sub_le (Λ r s : ℝ) (hΛ : 0 < Λ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |scalarFactor Λ r - scalarFactor Λ s| ≤ |r - s| / Λ ∧
      |scalarFactor Λ r - scalarFactor Λ s| ≤ 1 := by
  have hb1 := scalarFactor_bounds Λ r hΛ.le hr
  have hb2 := scalarFactor_bounds Λ s hΛ.le hs
  refine ⟨ ?_, abs_sub_le_iff.mpr ⟨ by linarith, by linarith ⟩ ⟩
  unfold scalarFactor
  split_ifs with hrΛ hsΛ hsΛ
  · simp [div_nonneg (abs_nonneg _) hΛ.le]
  · have hspos : 0 < s := lt_of_lt_of_le hΛ (le_of_not_ge hsΛ)
    have hdiff : 1 - Λ / s = (s - Λ) / s := by field_simp
    rw [hdiff, abs_of_nonneg (div_nonneg (by linarith) hspos.le),
      abs_of_nonpos (by linarith : r - s ≤ 0)]
    have h1 : (s - Λ) / s ≤ (s - Λ) / Λ :=
      div_le_div_of_nonneg_left (by linarith) hΛ (le_of_not_ge hsΛ)
    have h2 : (s - Λ) / Λ ≤ -(r - s) / Λ :=
      div_le_div_of_nonneg_right (by linarith) hΛ.le
    exact h1.trans h2
  · have hrpos : 0 < r := lt_of_lt_of_le hΛ (le_of_not_ge hrΛ)
    have hdiff : Λ / r - 1 = -((r - Λ) / r) := by field_simp
    rw [hdiff, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le),
      abs_of_nonneg (by linarith : 0 ≤ r - s)]
    have h1 : (r - Λ) / r ≤ (r - Λ) / Λ :=
      div_le_div_of_nonneg_left (by linarith) hΛ (le_of_not_ge hrΛ)
    have h2 : (r - Λ) / Λ ≤ (r - s) / Λ :=
      div_le_div_of_nonneg_right (by linarith) hΛ.le
    exact h1.trans h2
  · have hrpos : 0 < r := lt_of_lt_of_le hΛ (le_of_not_ge hrΛ)
    have hspos : 0 < s := lt_of_lt_of_le hΛ (le_of_not_ge hsΛ)
    have hdiff : Λ / r - Λ / s = Λ * (s - r) / (r * s) := by field_simp; ring
    rw [hdiff, abs_div, abs_mul, abs_of_pos hΛ, abs_of_pos (mul_pos hrpos hspos), abs_sub_comm]
    have hden : Λ * Λ ≤ r * s := mul_le_mul (le_of_not_ge hrΛ) (le_of_not_ge hsΛ) hΛ.le hrpos.le
    calc
      Λ * |r - s| / (r * s) ≤ Λ * |r - s| / (Λ * Λ) :=
        div_le_div_of_nonneg_left (mul_nonneg hΛ.le (abs_nonneg _)) (mul_pos hΛ hΛ) hden
      _ = |r - s| / Λ := by field_simp; ring

lemma clipFactor_sub_le (Λ : ℝ) (hΛ : 0 < Λ) (u v : E) :
    |clipFactor Λ u - clipFactor Λ v| ≤ min (‖u - v‖ / Λ) 1 := by
  have hs := scalarFactor_sub_le Λ ‖u‖ ‖v‖ hΛ (norm_nonneg u) (norm_nonneg v)
  refine le_min ?_ hs.2
  exact hs.1.trans (div_le_div_of_nonneg_right (abs_norm_sub_norm_le u v) hΛ.le)

/-- Pointwise bias inequality `‖(α(g) - α(μ)) (g - μ)‖ ≤ Λ^(1-p) ‖g - μ‖^p` for `1 ≤ p ≤ 2`. -/
lemma global_bias_pointwise (Λ p : ℝ) (hΛ : 0 < Λ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (g μ : E) :
    ‖(clipFactor Λ g - clipFactor Λ μ) • (g - μ)‖ ≤ Λ ^ (1 - p) * ‖g - μ‖ ^ p := by
  rw [norm_smul, Real.norm_eq_abs]
  have hlip := clipFactor_sub_le Λ hΛ g μ
  by_cases hz : ‖g - μ‖ = 0
  · rw [hz, mul_zero]
    positivity
  · have hx : 0 < ‖g - μ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    by_cases hxΛ : ‖g - μ‖ ≤ Λ
    · have h1 : |clipFactor Λ g - clipFactor Λ μ| ≤ ‖g - μ‖ / Λ :=
        hlip.trans (min_le_left _ _)
      have h2 : |clipFactor Λ g - clipFactor Λ μ| * ‖g - μ‖ ≤ Λ ^ (-1 : ℝ) * ‖g - μ‖ ^ 2 := by
        rw [Real.rpow_neg_one]
        calc
          |clipFactor Λ g - clipFactor Λ μ| * ‖g - μ‖ ≤ (‖g - μ‖ / Λ) * ‖g - μ‖ :=
            mul_le_mul_of_nonneg_right h1 hx.le
          _ = Λ⁻¹ * ‖g - μ‖ ^ 2 := by ring
      have h3 : ‖g - μ‖ ^ 2 = ‖g - μ‖ ^ (2 - p) * ‖g - μ‖ ^ p := by
        rw [← Real.rpow_two, ← Real.rpow_add hx]
        ring_nf
      have h4 : ‖g - μ‖ ^ (2 - p) ≤ Λ ^ (2 - p) :=
        Real.rpow_le_rpow hx.le hxΛ (by linarith)
      calc
        |clipFactor Λ g - clipFactor Λ μ| * ‖g - μ‖
          ≤ Λ ^ (-1 : ℝ) * (‖g - μ‖ ^ (2 - p) * ‖g - μ‖ ^ p) := by
            rw [← h3]
            exact h2
        _ ≤ Λ ^ (-1 : ℝ) * (Λ ^ (2 - p) * ‖g - μ‖ ^ p) := by
            gcongr
        _ = (Λ ^ (-1 : ℝ) * Λ ^ (2 - p)) * ‖g - μ‖ ^ p := by ring
        _ = Λ ^ (1 - p) * ‖g - μ‖ ^ p := by
            rw [← Real.rpow_add hΛ]
            ring_nf
    · have hΛx : Λ < ‖g - μ‖ := lt_of_not_ge hxΛ
      have h1 : |clipFactor Λ g - clipFactor Λ μ| ≤ 1 := hlip.trans (min_le_right _ _)
      have h2 : ‖g - μ‖ ^ (1 - p) ≤ Λ ^ (1 - p) :=
        Real.rpow_le_rpow_of_nonpos hΛ hΛx.le (by linarith)
      calc
        |clipFactor Λ g - clipFactor Λ μ| * ‖g - μ‖ ≤ 1 * ‖g - μ‖ :=
          mul_le_mul_of_nonneg_right h1 hx.le
        _ = ‖g - μ‖ ^ (1 - p) * ‖g - μ‖ ^ p := by
          rw [one_mul, ← Real.rpow_add hx]
          simp
        _ ≤ Λ ^ (1 - p) * ‖g - μ‖ ^ p :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx.le p)

/-- Nonexpansiveness of `clip Λ` on the whole space `E`. -/
lemma clip_nonexpansive (Λ : ℝ) (hΛ : 0 ≤ Λ) (u v : E) :
    ‖clip Λ u - clip Λ v‖ ≤ ‖u - v‖ := by
  by_cases hv : ‖v‖ ≤ Λ
  · rw [clip_eq_self Λ v hv]
    exact error_contracts Λ hΛ u v hv
  · by_cases hu : ‖u‖ ≤ Λ
    · rw [clip_eq_self Λ u hu, norm_sub_rev u (clip Λ v), norm_sub_rev u v]
      exact error_contracts Λ hΛ v u hu
    · have huΛ : Λ < ‖u‖ := lt_of_not_ge hu
      have hvΛ : Λ < ‖v‖ := lt_of_not_ge hv
      have hu0 : 0 < ‖u‖ := lt_of_le_of_lt hΛ huΛ
      have hv0 : 0 < ‖v‖ := lt_of_le_of_lt hΛ hvΛ
      have hcu : 0 ≤ Λ / ‖u‖ := div_nonneg hΛ hu0.le
      have hcv : 0 ≤ Λ / ‖v‖ := div_nonneg hΛ hv0.le
      have hcs : ⟪u, v⟫_ℝ ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
      have hprod : Λ ^ 2 ≤ ‖u‖ * ‖v‖ := by nlinarith
      have hsq : ‖clip Λ u - clip Λ v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
        rw [clip, if_neg hu, clip, if_neg hv, norm_sub_sq_real, norm_sub_sq_real,
          norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hcu, abs_of_nonneg hcv,
          div_mul_cancel₀ _ hu0.ne', div_mul_cancel₀ _ hv0.ne',
          real_inner_smul_left, real_inner_smul_right]
        have h1 : 2 * Λ ^ 2 - 2 * ((Λ / ‖u‖) * ((Λ / ‖v‖) * ⟪u, v⟫_ℝ)) =
            (2 * Λ ^ 2 / (‖u‖ * ‖v‖)) * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ) := by
          field_simp
          ring
        have h2 : 2 * Λ ^ 2 / (‖u‖ * ‖v‖) ≤ 2 := by
          rw [div_le_iff₀ (mul_pos hu0 hv0)]
          nlinarith
        have h3 : (2 * Λ ^ 2 / (‖u‖ * ‖v‖)) * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ) ≤
            2 * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
        nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
      nlinarith [norm_nonneg (clip Λ u - clip Λ v), norm_nonneg (u - v)]

lemma global_variance_pointwise (Λ p : ℝ) (hΛ : 0 < Λ) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (g μ : E) :
    ‖clip Λ g - clip Λ μ‖ ^ 2 ≤ (2 * Λ) ^ (2 - p) * ‖g - μ‖ ^ p := by
  have h1 : ‖clip Λ g - clip Λ μ‖ ≤ 2 * Λ := by
    have h := (norm_sub_le (clip Λ g) (clip Λ μ)).trans
      (add_le_add (norm_clip Λ hΛ.le g) (norm_clip Λ hΛ.le μ))
    linarith
  have h2 : ‖clip Λ g - clip Λ μ‖ ≤ ‖g - μ‖ := clip_nonexpansive Λ hΛ.le g μ
  by_cases hz : ‖clip Λ g - clip Λ μ‖ = 0
  · rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    positivity
  · have hpos : 0 < ‖clip Λ g - clip Λ μ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    calc
      ‖clip Λ g - clip Λ μ‖ ^ 2 =
          ‖clip Λ g - clip Λ μ‖ ^ (2 - p) * ‖clip Λ g - clip Λ μ‖ ^ p := by
        rw [← Real.rpow_add hpos]
        norm_num
      _ ≤ (2 * Λ) ^ (2 - p) * ‖g - μ‖ ^ p := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) h1 (by linarith))
        (Real.rpow_le_rpow (norm_nonneg _) h2 hp0)
        (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_scalarFactor (Λ : ℝ) : Measurable (scalarFactor Λ) := by
  unfold scalarFactor
  exact Measurable.ite (measurableSet_Iic) measurable_const (measurable_const.div measurable_id)

lemma measurable_clipFactor (Λ : ℝ) : Measurable (clipFactor (E := E) Λ) :=
  (measurable_scalarFactor Λ).comp measurable_norm

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} (ν : Measure Ω) [IsProbabilityMeasure ν]
  (m : MeasurableSpace Ω) (hm : m ≤ m₀)
include hm

/-- Pull an `m`-measurable vector out of a scalar-vector conditional expectation. -/
theorem condExp_smul_predictable_vec (φ : Ω → ℝ) (a : Ω → E)
    (hφ : Integrable φ ν) (ha : StronglyMeasurable[m] a)
    (hi : Integrable (fun ω => φ ω • a ω) ν) :
    ν[fun ω => φ ω • a ω | m] =ᵐ[ν] fun ω => ν[φ | m] ω • a ω := by
  letI : MeasurableSpace Ω := m₀
  have hX : @Measurable Ω Ω m₀ m id := measurable_id.mono le_rfl hm
  let κ : @Kernel Ω ℝ m _ := @condDistrib Ω Ω ℝ _ _ _ m₀ m φ id ν _
  letI : MeasurableSpace (Ω × ℝ) := m.prod inferInstance
  let joint : @Measure (Ω × ℝ) (m.prod inferInstance) :=
    @Measure.map Ω (Ω × ℝ) m₀ (m.prod inferInstance) (fun ω => (ω, φ ω)) ν
  have hXa : @AEMeasurable Ω Ω m m₀ id ν := @Measurable.aemeasurable Ω Ω m₀ m id ν hX
  have hjoint : AEMeasurable (fun ω => (ω, φ ω)) ν :=
    @AEMeasurable.prodMk Ω Ω ℝ m₀ m _ ν id φ hXa hφ.1.aemeasurable
  have hsnd : @StronglyMeasurable (Ω × ℝ) ℝ _ (m.prod inferInstance) Prod.snd :=
    stronglyMeasurable_id.comp_measurable measurable_snd
  have hmap : Integrable (fun q : Ω × ℝ => q.2) joint :=
    (integrable_map_measure hsnd.aestronglyMeasurable hjoint).mpr hφ
  have hik : ∀ᵐ ω ∂ν, Integrable (fun y : ℝ => y) (κ ω) :=
    hmap.condDistrib_ae (mβ := m) hXa hφ.1.aemeasurable
  have hb := condExp_ae_eq_integral_condDistrib' (X := id) hX hφ
  have hfun : @StronglyMeasurable (Ω × ℝ) E _ (m.prod inferInstance)
      (fun q => q.2 • a q.1) := hsnd.smul (ha.comp_measurable measurable_fst)
  have hc := condExp_prod_ae_eq_integral_condDistrib hX hφ.1.aemeasurable hfun hi
  simp only [MeasurableSpace.comap_id, id_eq] at hb hc
  filter_upwards [hik, hb, hc] with ω hikω hbω hcω
  rw [hcω, hbω]
  exact integral_smul_const (fun y : ℝ => y) (a ω)

/-- Pull an `m`-measurable scalar out of a scalar-vector conditional expectation. -/
theorem condExp_predictable_scalar_smul (ψ : Ω → ℝ) (e : Ω → E)
    (he : Integrable e ν) (hψ : StronglyMeasurable[m] ψ)
    (hi : Integrable (fun ω => ψ ω • e ω) ν) :
    ν[fun ω => ψ ω • e ω | m] =ᵐ[ν] fun ω => ψ ω • ν[e | m] ω := by
  letI : MeasurableSpace Ω := m₀
  have hX : @Measurable Ω Ω m₀ m id := measurable_id.mono le_rfl hm
  let κ : @Kernel Ω E m _ := @condDistrib Ω Ω E _ _ _ m₀ m e id ν _
  letI : MeasurableSpace (Ω × E) := m.prod inferInstance
  let joint : @Measure (Ω × E) (m.prod inferInstance) :=
    @Measure.map Ω (Ω × E) m₀ (m.prod inferInstance) (fun ω => (ω, e ω)) ν
  have hXa : @AEMeasurable Ω Ω m m₀ id ν := @Measurable.aemeasurable Ω Ω m₀ m id ν hX
  have hjoint : AEMeasurable (fun ω => (ω, e ω)) ν :=
    @AEMeasurable.prodMk Ω Ω E m₀ m _ ν id e hXa he.1.aemeasurable
  have hsnd : @StronglyMeasurable (Ω × E) E _ (m.prod inferInstance) Prod.snd :=
    stronglyMeasurable_id.comp_measurable measurable_snd
  have hmap : Integrable (fun q : Ω × E => q.2) joint :=
    (integrable_map_measure hsnd.aestronglyMeasurable hjoint).mpr he
  have hik : ∀ᵐ ω ∂ν, Integrable (fun y : E => y) (κ ω) :=
    hmap.condDistrib_ae (mβ := m) hXa he.1.aemeasurable
  have hb := condExp_ae_eq_integral_condDistrib' (X := id) hX he
  have hfun : @StronglyMeasurable (Ω × E) E _ (m.prod inferInstance)
      (fun q => ψ q.1 • q.2) := (hψ.comp_measurable measurable_fst).smul hsnd
  have hc := condExp_prod_ae_eq_integral_condDistrib hX he.1.aemeasurable hfun hi
  simp only [MeasurableSpace.comap_id, id_eq] at hb hc
  filter_upwards [hik, hb, hc] with ω hikω hbω hcω
  rw [hcω, hbω]
  exact integral_smul (ψ ω) (fun y : E => y)

/-- Conditional variance reduction against an `m`-measurable reference vector `c`:
`E[‖X - E[X|m]‖^2 | m] ≤ E[‖X - c‖^2 | m]`. -/
theorem conditional_variance_le_of_predictable (X c : Ω → E)
    (hX : Integrable X ν) (hc : Integrable c ν) (hcm : StronglyMeasurable[m] c)
    (hXc2 : Integrable (fun ω => ‖X ω - c ω‖ ^ 2) ν) :
    ν[fun ω => ‖X ω - ν[X | m] ω‖ ^ 2 | m] ≤ᵐ[ν]
      ν[fun ω => ‖X ω - c ω‖ ^ 2 | m] := by
  letI : MeasurableSpace Ω := m₀
  have hsub : Integrable (fun ω => X ω - c ω) ν := hX.sub hc
  have hce := condExp_sub hX hc m
  rw [condExp_of_stronglyMeasurable hm hcm hc] at hce
  have hred := conditional_centered_second_le ν m hm (fun ω => X ω - c ω) hsub hXc2
  have heq : (fun ω => ‖(X ω - c ω) - ν[fun a => X a - c a | m] ω‖ ^ 2) =ᵐ[ν]
      (fun ω => ‖X ω - ν[X | m] ω‖ ^ 2) := by
    filter_upwards [hce] with ω hω
    change ν[fun a => X a - c a | m] ω = ν[X | m] ω - c ω at hω
    rw [hω]
    congr 2
    abel
  exact (condExp_congr_ae heq).symm.trans_le hred

/-- `lem:global-clipping`: global decomposition of `clip Λ g` conditionally on `m`. -/
theorem global_clipping_estimates (Λ p σ : ℝ) (hΛ : 0 < Λ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ)
    (hμi : Integrable μ ν)
    (hpm : Integrable (fun ω => ‖g ω - μ ω‖ ^ p) ν)
    (hmean : ν[fun ω => g ω - μ ω | m] =ᵐ[ν] 0)
    (hmoment : ν[fun ω => ‖g ω - μ ω‖ ^ p | m] ≤ᵐ[ν] fun _ => σ ^ p) :
    let αg : Ω → ℝ := fun ω => clipFactor Λ (g ω)
    let C : Ω → E := fun ω => clip Λ (g ω)
    let A : Ω → ℝ := ν[αg | m]
    let ε : Ω → E := fun ω => ν[C | m] ω - A ω • μ ω
    let u : Ω → E := fun ω => C ω - ν[C | m] ω
    Integrable C ν ∧
      (∀ᵐ ω ∂ν, 0 ≤ A ω ∧ A ω ≤ 1) ∧
      (∀ᵐ ω ∂ν, ‖ε ω‖ ≤ σ ^ p * Λ ^ (1 - p)) ∧
      (∀ᵐ ω ∂ν, ‖u ω‖ ≤ 2 * Λ) ∧
      (ν[fun ω => ‖u ω‖ ^ 2 | m] ≤ᵐ[ν] fun _ => (2 * Λ) ^ (2 - p) * σ ^ p) := by
  letI : MeasurableSpace Ω := m₀
  let αg : Ω → ℝ := fun ω => clipFactor Λ (g ω)
  let αμ : Ω → ℝ := fun ω => clipFactor Λ (μ ω)
  let C : Ω → E := fun ω => clip Λ (g ω)
  let A : Ω → ℝ := ν[αg | m]
  let ε : Ω → E := fun ω => ν[C | m] ω - A ω • μ ω
  let u : Ω → E := fun ω => C ω - ν[C | m] ω
  let ξ : Ω → E := fun ω => g ω - μ ω
  have hCi : Integrable C ν := integrable_clip ν Λ hΛ.le g hg
  have hαgm : Measurable αg := (measurable_clipFactor Λ).comp hg
  have hαgi : Integrable αg ν := by
    apply Integrable.mono' (integrable_const 1) hαgm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    have hb := clipFactor_bounds Λ hΛ.le (g ω)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hA_bounds : ∀ᵐ ω ∂ν, 0 ≤ A ω ∧ A ω ≤ 1 := by
    have h0 : 0 ≤ᵐ[ν] A := condExp_nonneg (Filter.Eventually.of_forall
      (fun ω => (clipFactor_bounds Λ hΛ.le (g ω)).1))
    have h1 : A ≤ᵐ[ν] fun _ => (1 : ℝ) := by
      have hm1 := condExp_mono (m := m) hαgi (integrable_const 1)
        (Filter.Eventually.of_forall (fun ω => (clipFactor_bounds Λ hΛ.le (g ω)).2))
      rwa [condExp_const hm] at hm1
    filter_upwards [h0, h1] with ω h0ω h1ω
    exact ⟨ h0ω, h1ω ⟩
  have hξi : Integrable ξ ν := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hpm)
      (hg.aestronglyMeasurable.sub (hμ.mono hm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => norm_le_one_add_rpow _ p (norm_nonneg _) hp1)
  have hαgμi : Integrable (fun ω => αg ω • μ ω) ν := by
    apply Integrable.mono' hμi.norm (hαgm.aestronglyMeasurable.smul (hμ.mono hm).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro ω
    have hb := clipFactor_bounds Λ hΛ.le (g ω)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hαgξi : Integrable (fun ω => αg ω • ξ ω) ν := by
    apply Integrable.mono' hξi.norm
      (hαgm.aestronglyMeasurable.smul (hg.aestronglyMeasurable.sub (hμ.mono hm).aestronglyMeasurable))
    apply Filter.Eventually.of_forall
    intro ω
    have hb := clipFactor_bounds Λ hΛ.le (g ω)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hαμm : StronglyMeasurable[m] αμ :=
    ((measurable_clipFactor Λ).comp hμ.measurable).stronglyMeasurable
  have hαμξi : Integrable (fun ω => αμ ω • ξ ω) ν := by
    apply Integrable.mono' hξi.norm
      ((hαμm.mono hm).aestronglyMeasurable.smul (hg.aestronglyMeasurable.sub (hμ.mono hm).aestronglyMeasurable))
    apply Filter.Eventually.of_forall
    intro ω
    have hb := clipFactor_bounds Λ hΛ.le (μ ω)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hb.2
  have hC_decomp : C = fun ω => αg ω • μ ω + αg ω • ξ ω := by
    funext ω
    dsimp [C, αg, ξ]
    rw [clip_eq_clipFactor_smul, smul_sub, add_sub_cancel]
  have hce_decomp : ν[C | m] =ᵐ[ν] fun ω => A ω • μ ω + ν[fun a => (αg a - αμ a) • ξ a | m] ω := by
    have h1 : ν[C | m] =ᵐ[ν] ν[fun ω => αg ω • μ ω | m] + ν[fun ω => αg ω • ξ ω | m] := by
      rw [hC_decomp]
      exact condExp_add hαgμi hαgξi m
    have h2 := condExp_smul_predictable_vec ν m hm αg μ hαgi hμ hαgμi
    have h3 := condExp_predictable_scalar_smul ν m hm αμ ξ hξi hαμm hαμξi
    have h4 : ν[fun ω => αμ ω • ξ ω | m] =ᵐ[ν] 0 := by
      filter_upwards [h3, hmean] with ω h3ω hmω
      change ν[fun a => αμ a • ξ a | m] ω = αμ ω • ν[ξ | m] ω at h3ω
      rw [h3ω, hmω, Pi.zero_apply, smul_zero]
    have h5 := condExp_sub hαgξi hαμξi m
    have hdiff_eq : (fun ω => αg ω • ξ ω - αμ ω • ξ ω) = (fun ω => (αg ω - αμ ω) • ξ ω) := by
      funext ω
      rw [sub_smul]
    filter_upwards [h1, h2, h4, h5] with ω h1ω h2ω h4ω h5ω
    change ν[C | m] ω = ν[fun a => αg a • μ a | m] ω + ν[fun a => αg a • ξ a | m] ω at h1ω
    change ν[fun a => (αg a • ξ a) - (αμ a • ξ a) | m] ω =
      ν[fun a => αg a • ξ a | m] ω - ν[fun a => αμ a • ξ a | m] ω at h5ω
    rw [hdiff_eq] at h5ω
    rw [h1ω, h2ω, h5ω, h4ω, Pi.zero_apply, sub_zero]
  have hε_bound : ∀ᵐ ω ∂ν, ‖ε ω‖ ≤ σ ^ p * Λ ^ (1 - p) := by
    have hdiffi : Integrable (fun ω => (αg ω - αμ ω) • ξ ω) ν := by
      convert hαgξi.sub hαμξi using 1
      ext ω
      simp [sub_smul]
    have hnorm := norm_condExp_le ν m hm (fun ω => (αg ω - αμ ω) • ξ ω) hdiffi
    have hmono := condExp_mono (m := m) hdiffi.norm (hpm.const_mul (Λ ^ (1 - p)))
      (Filter.Eventually.of_forall (fun ω => global_bias_pointwise Λ p hΛ hp1 hp2 (g ω) (μ ω)))
    have hscale := condExp_smul (Λ ^ (1 - p)) (fun ω => ‖g ω - μ ω‖ ^ p) m (μ := ν)
    filter_upwards [hce_decomp, hnorm, hmono, hscale, hmoment] with ω hce hn hmo hs hmom
    have hεω : ε ω = ν[fun a => (αg a - αμ a) • ξ a | m] ω := by
      dsimp [ε]
      rw [hce, add_sub_cancel_left]
    rw [hεω]
    apply hn.trans (hmo.trans _)
    change ν[fun a => Λ ^ (1 - p) * ‖g a - μ a‖ ^ p | m] ω =
      Λ ^ (1 - p) * ν[fun a => ‖g a - μ a‖ ^ p | m] ω at hs
    rw [hs, mul_comm (σ ^ p)]
    exact mul_le_mul_of_nonneg_left hmom (Real.rpow_nonneg hΛ.le _)
  have hu_range : ∀ᵐ ω ∂ν, ‖u ω‖ ≤ 2 * Λ := by
    have hb := condExp_norm_bound ν m hm C hCi Λ
      (Filter.Eventually.of_forall (fun ω => norm_clip Λ hΛ.le (g ω)))
    filter_upwards [hb] with ω hbω
    have h := (norm_sub_le (C ω) (ν[C | m] ω)).trans
      (add_le_add (norm_clip Λ hΛ.le (g ω)) hbω)
    linarith
  have hu_var : ν[fun ω => ‖u ω‖ ^ 2 | m] ≤ᵐ[ν] fun _ => (2 * Λ) ^ (2 - p) * σ ^ p := by
    let Cμ : Ω → E := fun ω => clip Λ (μ ω)
    have hCμm : StronglyMeasurable[m] Cμ :=
      ((measurable_clip Λ).comp hμ.measurable).stronglyMeasurable
    have hCμi : Integrable Cμ ν := integrable_clip ν Λ hΛ.le μ (hμ.mono hm).measurable
    have hCCμ2 : Integrable (fun ω => ‖C ω - Cμ ω‖ ^ 2) ν := by
      apply Integrable.mono' (integrable_const ((2 * Λ) ^ 2))
        ((((measurable_clip Λ).comp hg).sub ((hCμm.mono hm).measurable)).norm.pow_const 2).aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h : ‖C ω - Cμ ω‖ ≤ 2 * Λ := by
        have h' := (norm_sub_le (C ω) (Cμ ω)).trans
          (add_le_add (norm_clip Λ hΛ.le (g ω)) (norm_clip Λ hΛ.le (μ ω)))
        linarith
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have hred := conditional_variance_le_of_predictable ν m hm C Cμ hCi hCμi hCμm hCCμ2
    have hmono := condExp_mono (m := m) hCCμ2 (hpm.const_mul ((2 * Λ) ^ (2 - p)))
      (Filter.Eventually.of_forall
        (fun ω => global_variance_pointwise Λ p hΛ (by linarith) hp2 (g ω) (μ ω)))
    have hscale := condExp_smul ((2 * Λ) ^ (2 - p)) (fun ω => ‖g ω - μ ω‖ ^ p) m (μ := ν)
    filter_upwards [hred, hmono, hscale, hmoment] with ω hr hmo hs hmom
    apply hr.trans (hmo.trans _)
    change ν[fun a => (2 * Λ) ^ (2 - p) * ‖g a - μ a‖ ^ p | m] ω =
      (2 * Λ) ^ (2 - p) * ν[fun a => ‖g a - μ a‖ ^ p | m] ω at hs
    rw [hs]
    exact mul_le_mul_of_nonneg_left hmom (by positivity)
  exact ⟨ hCi, hA_bounds, hε_bound, hu_range, hu_var ⟩

/-- Last part of `lem:global-clipping`: when `σ ≤ 1` and `Λ ≥ 4`,
`d = C - A • μ = ε + u` satisfies `‖d‖ ≤ 3 Λ`, `‖E[d|m]‖ ≤ 2 Λ^(1-p)`,
`‖d - E[d|m]‖ ≤ 2 Λ`, and `E[‖d‖^2|m] ≤ 4 Λ^(2-p)`. -/
theorem global_clipping_normalized (Λ p σ : ℝ) (hΛ4 : 4 ≤ Λ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (g μ : Ω → E) (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ)
    (hμi : Integrable μ ν)
    (hpm : Integrable (fun ω => ‖g ω - μ ω‖ ^ p) ν)
    (hmean : ν[fun ω => g ω - μ ω | m] =ᵐ[ν] 0)
    (hmoment : ν[fun ω => ‖g ω - μ ω‖ ^ p | m] ≤ᵐ[ν] fun _ => σ ^ p) :
    let αg : Ω → ℝ := fun ω => clipFactor Λ (g ω)
    let C : Ω → E := fun ω => clip Λ (g ω)
    let A : Ω → ℝ := ν[αg | m]
    let d : Ω → E := fun ω => C ω - A ω • μ ω
    Integrable d ν ∧ Integrable (fun ω => ‖d ω‖ ^ 2) ν ∧
      (∀ᵐ ω ∂ν, 0 ≤ A ω ∧ A ω ≤ 1) ∧
      (∀ᵐ ω ∂ν, ‖ν[d | m] ω‖ ≤ 2 * Λ ^ (1 - p)) ∧
      (ν[fun ω => ‖d ω‖ ^ 2 | m] ≤ᵐ[ν] fun _ => 4 * Λ ^ (2 - p)) ∧
      (∀ᵐ ω ∂ν, ‖d ω‖ ≤ 3 * Λ) ∧
      (∀ᵐ ω ∂ν, ‖d ω - ν[d | m] ω‖ ≤ 2 * Λ) := by
  letI : MeasurableSpace Ω := m₀
  have hΛ : 0 < Λ := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  obtain ⟨ hCi, hA, hε, hu_range, hu_var ⟩ :=
    global_clipping_estimates ν m hm Λ p σ hΛ hp1 hp2 g μ hg hμ hμi hpm hmean hmoment
  let αg : Ω → ℝ := fun ω => clipFactor Λ (g ω)
  let C : Ω → E := fun ω => clip Λ (g ω)
  let A : Ω → ℝ := ν[αg | m]
  let ε : Ω → E := fun ω => ν[C | m] ω - A ω • μ ω
  let u : Ω → E := fun ω => C ω - ν[C | m] ω
  let d : Ω → E := fun ω => C ω - A ω • μ ω
  have hσp : σ ^ p ≤ 1 := Real.rpow_le_one hσ0 hσ1 (by linarith)
  have hΛ1p_le_one : Λ ^ (1 - p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ1 (by linarith)
  have hΛ1p_le_Λ : Λ ^ (1 - p) ≤ Λ :=
    hΛ1p_le_one.trans hΛ1
  have h2_2p : (2 : ℝ) ^ (2 - p) ≤ 2 := by
    have h := Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith : 2 - p ≤ 1)
    linarith
  have h2Λ_2p : (2 * Λ) ^ (2 - p) * σ ^ p ≤ 2 * Λ ^ (2 - p) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hΛ.le]
    calc
      (2 : ℝ) ^ (2 - p) * Λ ^ (2 - p) * σ ^ p
        ≤ (2 : ℝ) ^ (2 - p) * Λ ^ (2 - p) * 1 :=
          mul_le_mul_of_nonneg_left hσp (by positivity)
      _ = (2 : ℝ) ^ (2 - p) * Λ ^ (2 - p) := mul_one _
      _ ≤ 2 * Λ ^ (2 - p) := mul_le_mul_of_nonneg_right h2_2p (by positivity)
  have hε_le_1p : ∀ᵐ ω ∂ν, ‖ε ω‖ ≤ Λ ^ (1 - p) := by
    filter_upwards [hε] with ω hω
    calc
      ‖ε ω‖ ≤ σ ^ p * Λ ^ (1 - p) := hω
      _ ≤ 1 * Λ ^ (1 - p) := mul_le_mul_of_nonneg_right hσp (by positivity)
      _ = Λ ^ (1 - p) := one_mul _
  have hd_eq : d = fun ω => ε ω + u ω := by
    funext ω
    dsimp [d, ε, u]
    abel
  have hd_range : ∀ᵐ ω ∂ν, ‖d ω‖ ≤ 3 * Λ := by
    filter_upwards [hε_le_1p, hu_range] with ω hεω huω
    have h : d ω = ε ω + u ω := by dsimp [d, ε, u]; abel
    rw [h]
    have htri := (norm_add_le (ε ω) (u ω)).trans (add_le_add hεω huω)
    linarith [hΛ1p_le_Λ]
  have hAm : StronglyMeasurable[m] A := stronglyMeasurable_condExp
  have hAμm : StronglyMeasurable[m] (fun ω => A ω • μ ω) := hAm.smul hμ
  have hdm : AEStronglyMeasurable d ν :=
    ((measurable_clip Λ).comp hg).aestronglyMeasurable.sub (hAμm.mono hm).aestronglyMeasurable
  have hdi : Integrable d ν := Integrable.mono' (integrable_const (3 * Λ)) hdm hd_range
  have hd2i : Integrable (fun ω => ‖d ω‖ ^ 2) ν := by
    apply Integrable.mono' (integrable_const ((3 * Λ) ^ 2)) (hdm.norm.pow 2)
    filter_upwards [hd_range] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hAμi : Integrable (fun ω => A ω • μ ω) ν := by
    convert hCi.sub hdi using 1
    funext ω
    dsimp [d]
    abel
  have hcd : ν[d | m] =ᵐ[ν] ε := by
    have hs := condExp_sub hCi hAμi m
    rw [condExp_of_stronglyMeasurable hm hAμm hAμi] at hs
    exact hs
  have hcd_bound : ∀ᵐ ω ∂ν, ‖ν[d | m] ω‖ ≤ 2 * Λ ^ (1 - p) := by
    filter_upwards [hcd, hε_le_1p] with ω hcdω hεω
    rw [hcdω]
    have : 0 ≤ Λ ^ (1 - p) := Real.rpow_nonneg hΛ.le _
    linarith
  have hd_center : ∀ᵐ ω ∂ν, ‖d ω - ν[d | m] ω‖ ≤ 2 * Λ := by
    filter_upwards [hcd, hu_range] with ω hcdω huω
    have heq : d ω - ν[d | m] ω = u ω := by
      rw [hcdω]
      dsimp [d, ε, u]
      abel
    rw [heq]
    exact huω
  have hd_second : ν[fun ω => ‖d ω‖ ^ 2 | m] ≤ᵐ[ν] fun _ => 4 * Λ ^ (2 - p) := by
    have hcenter := conditional_centering_identity ν m hm d hdi hd2i
    have hu_eq : (fun ω => ‖d ω - ν[d | m] ω‖ ^ 2) =ᵐ[ν] (fun ω => ‖u ω‖ ^ 2) := by
      filter_upwards [hcd] with ω hcdω
      have heq : d ω - ν[d | m] ω = u ω := by
        rw [hcdω]
        dsimp [d, ε, u]
        abel
      rw [heq]
    have hce_u := condExp_congr_ae (m := m) hu_eq
    filter_upwards [hcenter, hce_u, hu_var, hcd, hε_le_1p] with ω hcω hcuω huvω hcdω hεω
    have h1 : ν[fun a => ‖d a‖ ^ 2 | m] ω =
        ν[fun a => ‖u a‖ ^ 2 | m] ω + ‖ε ω‖ ^ 2 := by
      linarith [hcω, hcuω, show ‖ν[d | m] ω‖ ^ 2 = ‖ε ω‖ ^ 2 by rw [hcdω]]
    have h2 : ν[fun a => ‖u a‖ ^ 2 | m] ω ≤ 2 * Λ ^ (2 - p) := huvω.trans h2Λ_2p
    have h3 : ‖ε ω‖ ^ 2 ≤ 1 := by
      have := hεω.trans hΛ1p_le_one
      nlinarith [norm_nonneg (ε ω)]
    have h4 : (1 : ℝ) ≤ Λ ^ (2 - p) :=
      Real.one_le_rpow hΛ1 (by linarith)
    linarith
  exact ⟨ hdi, hd2i, hA, hcd_bound, hd_second, hd_range, hd_center ⟩

end
end ClippedSGD.GlobalClipping
