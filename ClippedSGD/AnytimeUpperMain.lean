import ClippedSGD.GlobalClipping
import ClippedSGD.SuffixPotential
import ClippedSGD.EnergyBudget
import ClippedSGD.AnytimeParameters
import ClippedSGD.UpperRun

/-!
# Time-Uniform Upper Bound for Horizon-Free Clipped SGD (`thm:anytime-upper`)

This module formalizes the time-uniform upper bound (`thm:anytime-upper`) and its proof
(`app:anytime-upper-radius`, `app:anytime-upper-potential`, `app:anytime-upper-direct`,
`app:anytime-upper-scaling`):
- Time-varying schedule clipped SGD iterates (`anytimeIterate`, `normRun`, `anytimeRun`).
- Global radius event `ℛ_δ` (`anytime_radius_event`).
- Suffix potential concentration at a fixed horizon `T ≥ 2k` (`anytime_horizon_event`).
- Normalized time-uniform upper bound across all `T ≥ 1` (`anytime_upper_normalized`).
- Rescaling to general `(L, R, σ)` and the theorem itself (`anytime_upper_centered`, `anytime_upper`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators InnerProductSpace ENNReal

set_option autoImplicit false

namespace ClippedSGD.AnytimeUpperMain

open Clipping ClippingConditional GlobalClipping Potential Radius SuffixPotential
  EnergyBudget AnytimeParameters UpperRun

noncomputable section

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m₀ : MeasurableSpace Ω}

/-! ## 1. Horizon-Free Clipped SGD Iterates and Predictability -/

/-- Horizon-free clipped SGD iterates with time-varying step size `η : ℕ → ℝ` and
clipping level `Λ : ℕ → ℝ` (`eq:anytime-upper-schedule`).
Index `t` is the paper's `x_t`; index `0` repeats `x_1`. -/
def anytimeIterate (x₁ : E) (η Λ : ℕ → ℝ) (g : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => fun _ => x₁
  | 1 => fun _ => x₁
  | t + 2 => fun ω =>
      anytimeIterate x₁ η Λ g (t + 1) ω - η (t + 1) • clip (Λ (t + 1)) (g (t + 1) ω)

/-- Normalized horizon-free clipped SGD run (`L' ≤ 1, R = 1, σ' ≤ 1`). -/
def normRun (x₁ : E) (p : ℝ) (g : ℕ → Ω → E) : ℕ → Ω → E :=
  anytimeIterate x₁ (normStep p (c_p p)) (normLambda p) g

/-- Horizon-free clipped SGD run with schedule (`eq:anytime-upper-schedule`):
`η_t = (R / Q) c_p t ^ (-a) / ℓ_t²`, `λ_t = 4 Q t ^ b`. -/
def anytimeRun (x₁ : E) (L R σ p : ℝ) (g : ℕ → Ω → E) : ℕ → Ω → E :=
  anytimeIterate x₁ (anytimeStep L R σ p) (anytimeLambda L R σ p) g

lemma anytimeIterate_adapted (𝓕 : Filtration ℕ m₀) (x₁ : E) (η Λ : ℕ → ℝ) (g : ℕ → Ω → E)
    (hg : ∀ t, @Measurable Ω E (𝓕 t) _ (g t)) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (anytimeIterate x₁ η Λ g (t + 1)) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    change StronglyMeasurable[𝓕 (t + 1)] (fun ω =>
      anytimeIterate x₁ η Λ g (t + 1) ω - η (t + 1) • clip (Λ (t + 1)) (g (t + 1) ω))
    exact (ih.mono (𝓕.mono (by omega))).sub
      (((measurable_clip (Λ (t + 1))).comp (hg (t + 1))).stronglyMeasurable.const_smul _)

lemma anytimeIterate_gradient_predictable {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (𝓕 : Filtration ℕ m₀) (x₁ : E) (η Λ : ℕ → ℝ) (g : ℕ → Ω → E)
    (hg : ∀ t, @Measurable Ω E (𝓕 t) _ (g t)) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (fun ω => gradient f (anytimeIterate x₁ η Λ g (t + 1) ω)) :=
  (gradient_continuous L hL hlip).comp_stronglyMeasurable
    (anytimeIterate_adapted 𝓕 x₁ η Λ g hg t)

lemma anytimeIterate_inexact (f : E → ℝ) (x₁ : E) (η Λ : ℕ → ℝ) (g : ℕ → Ω → E)
    (t : ℕ) (ω : Ω) :
    anytimeIterate x₁ η Λ g (t + 2) ω =
      anytimeIterate x₁ η Λ g (t + 1) ω -
        η (t + 1) • (gradient f (anytimeIterate x₁ η Λ g (t + 1) ω) +
          (clip (Λ (t + 1)) (g (t + 1) ω) - gradient f (anytimeIterate x₁ η Λ g (t + 1) ω))) := by
  simp only [anytimeIterate, add_sub_cancel]

lemma anytimeIterate_radius_bound (x₁ xstar : E) (R : ℝ) (η Λ : ℕ → ℝ)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i) (hΛ : ∀ i, 1 ≤ i → 0 ≤ Λ i)
    (g : ℕ → Ω → E) (hinit : ‖x₁ - xstar‖ ≤ R) (t : ℕ) (ω : Ω) :
    ‖anytimeIterate x₁ η Λ g (t + 1) ω - xstar‖ ≤
      R + ∑ i ∈ Finset.range t, η (i + 1) * Λ (i + 1) := by
  induction t with
  | zero => simpa [anytimeIterate] using hinit
  | succ t ih =>
    have hηt : 0 ≤ η (t + 1) := hη (t + 1) (by omega)
    have hΛt : 0 ≤ Λ (t + 1) := hΛ (t + 1) (by omega)
    have heq : anytimeIterate x₁ η Λ g (t + 2) ω - xstar =
        (anytimeIterate x₁ η Λ g (t + 1) ω - xstar) -
          η (t + 1) • clip (Λ (t + 1)) (g (t + 1) ω) := by
      change (anytimeIterate x₁ η Λ g (t + 1) ω - η (t + 1) • clip (Λ (t + 1)) (g (t + 1) ω)) - xstar = _
      rw [sub_right_comm]
    have hn := norm_sub_le (anytimeIterate x₁ η Λ g (t + 1) ω - xstar)
      (η (t + 1) • clip (Λ (t + 1)) (g (t + 1) ω))
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hηt] at hn
    have hclip := mul_le_mul_of_nonneg_left (norm_clip (Λ (t + 1)) hΛt (g (t + 1) ω)) hηt
    rw [Finset.sum_range_succ]
    linarith

lemma anytimeIterate_gradient_integrable (ν : Measure Ω) [IsProbabilityMeasure ν]
    (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (L R : ℝ) (η Λ : ℕ → ℝ) (hL : 0 < L)
    (hη : ∀ i, 1 ≤ i → 0 ≤ η i) (hΛ : ∀ i, 1 ≤ i → 0 ≤ Λ i)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y) (hinit : ‖x₁ - xstar‖ ≤ R)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g) (t : ℕ) :
    Integrable (fun ω => gradient f (anytimeIterate x₁ η Λ g (t + 1) ω)) ν := by
  have hm := anytimeIterate_gradient_predictable L hL.le hlip 𝓕 x₁ η Λ g
    (fun i => (hg i).measurable) t
  apply Integrable.mono'
    (integrable_const (L * (R + ∑ i ∈ Finset.range t, η (i + 1) * Λ (i + 1))))
    ((hm.mono (𝓕.le t)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  have hz := Radius.gradient_zero_at_minimizer (fun y => (hdiff y).hasGradientAt) xstar hmin
  have hh := hlip (anytimeIterate x₁ η Λ g (t + 1) ω) xstar
  rw [hz, sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (anytimeIterate_radius_bound x₁ xstar R η Λ hη hΛ g hinit t ω) hL.le)

/-! ## 2. Global Radius Event `ℛ_δ` -/

/-- `app:anytime-upper-radius`: in the normalized regime (`L' ≤ 1, R = 1, σ' ≤ 1`),
the global radius event `ℛ_δ = {∀ t ≥ 1, ‖x_t - x^*‖² ≤ h²}` fails with probability at most
`exp(-h) = δ / 100`. -/
theorem anytime_radius_event (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L' σ' p δ : ℝ) (hL' : 0 < L') (hL'1 : L' ≤ 1) (hσ'0 : 0 ≤ σ') (hσ'1 : σ' ≤ 1)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L' * ‖y - z‖)
    (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y) (hinit : ‖x₁ - xstar‖ ≤ 1)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t, Integrable (fun ω =>
      ‖g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω)‖ ^ p) ν)
    (hmean : ∀ t, ν[fun ω =>
      g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω) | 𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t, ν[fun ω =>
      ‖g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω)‖ ^ p | 𝓕 t] ≤ᵐ[ν]
      fun _ => σ' ^ p) :
    ν {ω | ∃ t : ℕ, 1 ≤ t ∧ (confH δ) ^ (2 : ℕ) < ‖normRun x₁ p g t ω - xstar‖ ^ (2 : ℕ)} ≤
      ENNReal.ofReal (Real.exp (-confH δ)) := by
  let x := normRun x₁ p g
  let η := normStep p (c_p p)
  let Λ := normLambda p
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hη_nn : ∀ i, 1 ≤ i → 0 ≤ η i := fun i _ => normStep_nonneg (p := p) (c := c_p p) hc_pos.le i
  have hΛ_nn : ∀ i, 1 ≤ i → 0 ≤ Λ i := fun i _ => normLambda_nonneg p i
  have hx_meas : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1)) :=
    anytimeIterate_adapted 𝓕 x₁ η Λ g (fun t => (hg t).measurable)
  have hμ_meas : ∀ t, StronglyMeasurable[𝓕 t] (fun ω => gradient f (x (t + 1) ω)) :=
    anytimeIterate_gradient_predictable L' hL'.le hlip 𝓕 x₁ η Λ g (fun t => (hg t).measurable)
  have hμ_int : ∀ t, Integrable (fun ω => gradient f (x (t + 1) ω)) ν :=
    anytimeIterate_gradient_integrable ν 𝓕 hdiff L' 1 η Λ hL' hη_nn hΛ_nn hlip x₁ xstar
      hmin hinit g hg
  let P_rad : ℕ → Ω → ℝ := fun t ω => ‖x (t + 1) ω - xstar‖ ^ (2 : ℕ)
  have hP_adap : Adapted 𝓕 P_rad := fun t =>
    (((hx_meas t).sub stronglyMeasurable_const).norm.pow 2)
  have hP_nn : ∀ t ω, 0 ≤ P_rad t ω := fun _ _ => sq_nonneg _
  let α_raw : ℕ → Ω → ℝ := fun t ω => clipFactor (Λ (t + 1)) (g (t + 1) ω)
  let A_raw : ℕ → Ω → ℝ := fun t => ν[α_raw t | 𝓕 t]
  let d_raw : ℕ → Ω → E := fun t ω =>
    clip (Λ (t + 1)) (g (t + 1) ω) - A_raw t ω • gradient f (x (t + 1) ω)
  let w_rad : ℕ → Ω → E := fun t ω => (-2 * η (t + 1)) • (x (t + 1) ω - xstar)
  have hglob : ∀ t,
      Integrable (d_raw t) ν ∧ Integrable (fun ω => ‖d_raw t ω‖ ^ (2 : ℕ)) ν ∧
      (∀ᵐ ω ∂ν, 0 ≤ A_raw t ω ∧ A_raw t ω ≤ 1) ∧
      (∀ᵐ ω ∂ν, ‖ν[d_raw t | 𝓕 t] ω‖ ≤ normB p (t + 1)) ∧
      (ν[fun ω => ‖d_raw t ω‖ ^ (2 : ℕ) | 𝓕 t] ≤ᵐ[ν] fun _ => 2 * normV p (t + 1)) ∧
      (∀ᵐ ω ∂ν, ‖d_raw t ω‖ ≤ 3 * Λ (t + 1)) ∧
      (∀ᵐ ω ∂ν, ‖d_raw t ω - ν[d_raw t | 𝓕 t] ω‖ ≤ 2 * Λ (t + 1)) := by
    intro t
    have hΛ4 : 4 ≤ Λ (t + 1) := normLambda_ge_four hp (by omega)
    have h := global_clipping_normalized ν (𝓕 t) (𝓕.le t) (Λ (t + 1)) p σ'
      hΛ4 hσ'0 hσ'1 hp.le hp2 (g (t + 1)) (fun ω => gradient f (x (t + 1) ω))
      (((hg (t + 1)).mono (𝓕.le (t + 1))).measurable)
      (hμ_meas t) (hμ_int t) (hpm t) (hmean t) (hmoment t)
    have hB_eq : 2 * (Λ (t + 1)) ^ (1 - p) = normB p (t + 1) := rfl
    have hV_eq : 4 * (Λ (t + 1)) ^ (2 - p) = 2 * normV p (t + 1) := by
      unfold normV; ring
    simpa only [α_raw, A_raw, d_raw, hB_eq, hV_eq] using h
  have hd_meas : ∀ t, StronglyMeasurable[𝓕 (t + 1)] (d_raw t) := by
    intro t
    have hC : StronglyMeasurable[𝓕 (t + 1)] (fun ω => clip (Λ (t + 1)) (g (t + 1) ω)) :=
      ((measurable_clip (Λ (t + 1))).comp (hg (t + 1)).measurable).stronglyMeasurable
    have hA : StronglyMeasurable[𝓕 t] (A_raw t) := stronglyMeasurable_condExp
    exact hC.sub ((hA.smul (hμ_meas t)).mono (𝓕.mono (by omega)))
  have hw_meas : ∀ t, StronglyMeasurable[𝓕 t] (w_rad t) := fun t =>
    ((hx_meas t).sub stronglyMeasurable_const).const_smul (-2 * η (t + 1))
  let ℰ_rad : Set Ω := {ω | ∀ t : ℕ, 0 ≤ A_raw t ω ∧ A_raw t ω ≤ 1}
  have hℰ_ae : ∀ᵐ ω ∂ν, ω ∈ ℰ_rad := ae_all_iff.mpr (fun t => (hglob t).2.2.1)
  have hℰ_compl : ν ℰ_radᶜ = 0 := ae_iff.mp hℰ_ae
  have hstep_rec : ∀ m, ∀ ω ∈ ℰ_rad ∩ Set.univ,
      P_rad (m + 1) ω ≤ P_rad 0 ω +
        ∑ t ∈ Finset.range (m + 1),
          (2 * (η (t + 1)) ^ (2 : ℕ) * ‖d_raw t ω‖ ^ (2 : ℕ) + ⟪d_raw t ω, w_rad t ω⟫_ℝ) := by
    intro m ω hω
    have hAω : ∀ t, 0 ≤ A_raw t ω ∧ A_raw t ω ≤ 1 := hω.1
    induction m with
    | zero =>
      rw [Finset.range_one, Finset.sum_singleton]
      have hη0 : 0 ≤ η 1 := hη_nn 1 le_rfl
      have hη_half : η 1 ≤ 1 / 2 := (normStep_le_c hp hc_pos.le le_rfl).trans
        (by linarith [c_p_le_inv_1000 hp])
      have hL_inv : 1 / 2 ≤ 1 / (2 * L') :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hγ0 : 0 ≤ η 1 * A_raw 0 ω := mul_nonneg hη0 (hAω 0).1
      have hγL : η 1 * A_raw 0 ω ≤ 1 / (2 * L') := by
        calc
          η 1 * A_raw 0 ω ≤ η 1 * 1 := mul_le_mul_of_nonneg_left (hAω 0).2 hη0
          _ ≤ 1 / (2 * L') := by linarith
      have hy : x 2 ω = x 1 ω - η 1 • (A_raw 0 ω • gradient f (x 1 ω) + d_raw 0 ω) := by
        change x 1 ω - η 1 • clip (Λ 1) (g 1 ω) = _
        dsimp [d_raw]
        rw [add_sub_cancel]
      exact global_radius_step hconv hdiff L' hL' hlip xstar hmin
        (x 1 ω) (x 2 ω) (d_raw 0 ω) (η 1) (A_raw 0 ω) hη0 hγ0 hγL hy
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hηm : 0 ≤ η (m + 2) := hη_nn (m + 2) (by omega)
      have hη_half : η (m + 2) ≤ 1 / 2 := (normStep_le_c hp hc_pos.le (by omega)).trans
        (by linarith [c_p_le_inv_1000 hp])
      have hL_inv : 1 / 2 ≤ 1 / (2 * L') :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hγ0 : 0 ≤ η (m + 2) * A_raw (m + 1) ω := mul_nonneg hηm (hAω (m + 1)).1
      have hγL : η (m + 2) * A_raw (m + 1) ω ≤ 1 / (2 * L') := by
        calc
          η (m + 2) * A_raw (m + 1) ω ≤ η (m + 2) * 1 :=
            mul_le_mul_of_nonneg_left (hAω (m + 1)).2 hηm
          _ ≤ 1 / (2 * L') := by linarith
      have hy : x (m + 3) ω =
          x (m + 2) ω - η (m + 2) • (A_raw (m + 1) ω • gradient f (x (m + 2) ω) + d_raw (m + 1) ω) := by
        change x (m + 2) ω - η (m + 2) • clip (Λ (m + 2)) (g (m + 2) ω) = _
        dsimp [d_raw]
        rw [add_sub_cancel]
      have hstep := global_radius_step hconv hdiff L' hL' hlip xstar hmin
        (x (m + 2) ω) (x (m + 3) ω) (d_raw (m + 1) ω) (η (m + 2)) (A_raw (m + 1) ω)
        hηm hγ0 hγL hy
      dsimp [P_rad, w_rad] at ih hstep ⊢
      linarith
  have hw_bound : ∀ t, ∀ ω ∈ (Set.univ : Set Ω),
      ‖w_rad t ω‖ ≤ (2 * η (t + 1)) * Real.sqrt (P_rad t ω) := by
    intro t ω _
    have hηt : 0 ≤ η (t + 1) := hη_nn (t + 1) (by omega)
    dsimp [w_rad, P_rad]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_two, abs_of_nonneg hηt,
      Real.sqrt_sq (norm_nonneg _)]
  have h_eb := energy_budget_infinite ν 𝓕 P_rad hP_adap hP_nn
    (fun _ => Set.univ) (fun t => @MeasurableSet.univ Ω (𝓕 t)) (fun _ _ h => h) ℰ_rad
    d_raw w_rad hd_meas (fun t => (hglob t).1) (fun t => (hglob t).2.1)
    (fun _ _ h => (h (Set.mem_univ _)).elim) hw_meas
    (fun t => 2 * (η (t + 1)) ^ (2 : ℕ))
    (fun t => 2 * η (t + 1))
    (fun t => normB p (t + 1))
    (fun t => 2 * normV p (t + 1))
    (fun t => 3 * Λ (t + 1))
    (fun t => 2 * Λ (t + 1))
    (fun t => by positivity)
    (fun t => by have := hη_nn (t + 1) (by omega); positivity)
    (fun t => normB_nonneg p (t + 1))
    (fun t => by have := normV_nonneg p (t + 1); positivity)
    (fun t => by have := hΛ_nn (t + 1) (by omega); positivity)
    (fun t => by have := hΛ_nn (t + 1) (by omega); positivity)
    hw_bound hstep_rec
    (fun t => (hglob t).2.2.2.1)
    (fun t => (hglob t).2.2.2.2.1)
    (fun t => (hglob t).2.2.2.2.2.1)
    (fun t => (hglob t).2.2.2.2.2.2)
    1 (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
    (288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
    (2 * K_const p * c_p p / ell 1)
    (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
    (16 * c_p p / (ell 1) ^ (2 : ℕ))
    (confH δ)
    zero_le_one
    (by have := K_const_ge_one hp; have := ell_pos le_rfl; positivity)
    (by have := ell_pos le_rfl; positivity)
    (by have := K_const_ge_one hp; have := ell_pos le_rfl; positivity)
    (by have := K_const_ge_one hp; have := ell_pos le_rfl; positivity)
    (by have := ell_pos le_rfl; positivity)
    (by have := four_lt_confH hδ hδ1; linarith)
    (fun N => radA_sum_le hp N)
    (fun t => radK_sup_le hp t)
    (fun N => radB_sum_le hp N)
    (fun N => radV_sum_le hp N)
    (fun t => radJ_sup_le hp t)
  have hH_le : energyThreshold 1
      (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
      (288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
      (2 * K_const p * c_p p / ell 1)
      (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
      (16 * c_p p / (ell 1) ^ (2 : ℕ)) (confH δ) ≤ (confH δ) ^ (2 : ℕ) :=
    global_radius_threshold_le hp hδ hδ1
  have hinit_sq : ∀ ω, P_rad 0 ω ≤ 1 := by
    intro ω
    change ‖x₁ - xstar‖ ^ (2 : ℕ) ≤ 1
    nlinarith [norm_nonneg (x₁ - xstar)]
  have hsub : {ω | ∃ t : ℕ, 1 ≤ t ∧ (confH δ) ^ (2 : ℕ) < ‖x t ω - xstar‖ ^ (2 : ℕ)} ⊆
      {ω ∈ ℰ_rad | P_rad 0 ω ≤ 1 ∧ ∃ m : ℕ, ω ∈ (Set.univ : Set Ω) ∧
        energyThreshold 1
          (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
          (288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
          (2 * K_const p * c_p p / ell 1)
          (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
          (16 * c_p p / (ell 1) ^ (2 : ℕ)) (confH δ) < P_rad (m + 1) ω} ∪ ℰ_radᶜ := by
    intro ω hω
    by_cases hℰ : ω ∈ ℰ_rad
    · left
      rcases hω with ⟨ t, ht1, hgt ⟩
      refine ⟨ hℰ, hinit_sq ω, ?_ ⟩
      rcases Nat.eq_or_lt_of_le ht1 with rfl | ht2
      · exfalso
        have h1 : ‖x 1 ω - xstar‖ ^ (2 : ℕ) ≤ 1 := hinit_sq ω
        have h4 : 4 < confH δ := four_lt_confH hδ hδ1
        nlinarith
      · refine ⟨ t - 2, Set.mem_univ ω, hH_le.trans_lt ?_ ⟩
        have hidx : t - 2 + 1 + 1 = t := by omega
        simpa only [P_rad, hidx] using hgt
    · exact Or.inr hℰ
  calc
    ν {ω | ∃ t : ℕ, 1 ≤ t ∧ (confH δ) ^ (2 : ℕ) < ‖x t ω - xstar‖ ^ (2 : ℕ)}
      ≤ ν ({ω ∈ ℰ_rad | P_rad 0 ω ≤ 1 ∧ ∃ m : ℕ, ω ∈ (Set.univ : Set Ω) ∧
          energyThreshold 1
            (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (2 * K_const p * c_p p / ell 1)
            (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (16 * c_p p / (ell 1) ^ (2 : ℕ)) (confH δ) < P_rad (m + 1) ω} ∪ ℰ_radᶜ) :=
        measure_mono hsub
    _ ≤ ν {ω ∈ ℰ_rad | P_rad 0 ω ≤ 1 ∧ ∃ m : ℕ, ω ∈ (Set.univ : Set Ω) ∧
          energyThreshold 1
            (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (2 * K_const p * c_p p / ell 1)
            (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (16 * c_p p / (ell 1) ^ (2 : ℕ)) (confH δ) < P_rad (m + 1) ω} + ν ℰ_radᶜ :=
        measure_union_le _ _
    _ = ν {ω ∈ ℰ_rad | P_rad 0 ω ≤ 1 ∧ ∃ m : ℕ, ω ∈ (Set.univ : Set Ω) ∧
          energyThreshold 1
            (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (2 * K_const p * c_p p / ell 1)
            (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (16 * c_p p / (ell 1) ^ (2 : ℕ)) (confH δ) < P_rad (m + 1) ω} := by
        rw [hℰ_compl, add_zero]
    _ ≤ ENNReal.ofReal (Real.exp (-confH δ)) := h_eb

/-! ## 3. Shifted Filtration and Suffix Potential Concentration -/

/-- Shifted filtration `𝓕_s i = 𝓕 (s + i)`. -/
def shiftFiltration (𝓕 : Filtration ℕ m₀) (s : ℕ) : Filtration ℕ m₀ where
  seq i := 𝓕 (s + i)
  mono' i j hij := 𝓕.mono (by omega)
  le' i := 𝓕.le (s + i)

lemma suffixIter_adapted (𝓕 : Filtration ℕ m₀) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1))) (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    StronglyMeasurable[shiftFiltration 𝓕 (k - 1) i]
      (fun ω => suffixIter (fun j => x j ω) k (i + 1)) := by
  have hidx : k - 1 + i + 1 = k + i := by omega
  change StronglyMeasurable[𝓕 (k - 1 + i)] (x (k + i))
  rw [← hidx]
  exact hx (k - 1 + i)

lemma suffixComparator_adapted (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1))) (w : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    StronglyMeasurable[shiftFiltration 𝓕 (k - 1) i]
      (fun ω => comparator xstar (suffixIter (fun j => x j ω) k) w i) := by
  induction i with
  | zero => exact stronglyMeasurable_const
  | succ i ih =>
    change StronglyMeasurable[shiftFiltration 𝓕 (k - 1) (i + 1)] (fun ω =>
      (1 - w i / w (i + 1)) • suffixIter (fun j => x j ω) k (i + 1) +
        (w i / w (i + 1)) • comparator xstar (suffixIter (fun j => x j ω) k) w i)
    have hx_i := (suffixIter_adapted 𝓕 x hx k hk i).mono
      ((shiftFiltration 𝓕 (k - 1)).mono (Nat.le_succ i))
    have ih_i := ih.mono ((shiftFiltration 𝓕 (k - 1)).mono (Nat.le_succ i))
    exact (hx_i.const_smul _).add (ih_i.const_smul _)

lemma suffixRecursiveAverage_adapted (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (xstar : E) (x : ℕ → Ω → E) (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1)))
    (η' w : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    StronglyMeasurable[shiftFiltration 𝓕 (k - 1) i]
      (fun ω => recursiveAverage (fun j => f (suffixIter (fun l => x l ω) k j) - f xstar) η' w i) := by
  induction i with
  | zero => exact stronglyMeasurable_const
  | succ i ih =>
    change StronglyMeasurable[shiftFiltration 𝓕 (k - 1) (i + 1)] (fun ω =>
      (1 - η' (i + 1) * w (i + 1)) *
        recursiveAverage (fun j => f (suffixIter (fun l => x l ω) k j) - f xstar) η' w i +
      η' (i + 1) * w (i + 1) * (f (suffixIter (fun l => x l ω) k (i + 2)) - f xstar))
    have ih_i := ih.mono ((shiftFiltration 𝓕 (k - 1)).mono (Nat.le_succ i))
    have hx_i1 := suffixIter_adapted 𝓕 x hx k hk (i + 1)
    have hf_i1 : StronglyMeasurable[shiftFiltration 𝓕 (k - 1) (i + 1)]
        (fun ω => f (suffixIter (fun l => x l ω) k (i + 2)) - f xstar) :=
      (hdiff.continuous.comp_stronglyMeasurable hx_i1).sub stronglyMeasurable_const
    exact (ih_i.const_mul _).add (hf_i1.const_mul _)

lemma suffixPotential_adapted (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (xstar : E) (x : ℕ → Ω → E) (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1)))
    (η : ℕ → ℝ) (T k : ℕ) (hk : 1 ≤ k) :
    Adapted (shiftFiltration 𝓕 (k - 1))
      (fun i ω => suffixPotential f xstar (fun j => x j ω) η T k i) := by
  intro i
  unfold suffixPotential distanceEnergy
  have hrec := suffixRecursiveAverage_adapted 𝓕 hdiff xstar x hx
    (suffixStep η k) (suffixWeight η T k) k hk i
  have hcomp := suffixComparator_adapted 𝓕 xstar x hx (suffixWeight η T k) k hk i
  have hx_i := suffixIter_adapted 𝓕 x hx k hk i
  have hdist := (((hcomp.sub hx_i).norm.pow 2).const_mul (suffixWeight η T k i / 2))
  exact (hrec.add hdist).const_mul (cappedTail η T k)

lemma suffixDirection_adapted (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1)))
    (η : ℕ → ℝ) (T k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    StronglyMeasurable[shiftFiltration 𝓕 (k - 1) i]
      (fun ω => suffixDirection xstar (fun j => x j ω) η T k i) := by
  unfold suffixDirection
  have hcomp := suffixComparator_adapted 𝓕 xstar x hx (suffixWeight η T k) k hk i
  have hx_i : StronglyMeasurable[shiftFiltration 𝓕 (k - 1) i] (x (k + i)) :=
    suffixIter_adapted 𝓕 x hx k hk i
  exact (hcomp.sub hx_i).const_smul _

/-- Predictable radius guard set `J_suf i = {ω | ∀ j ≤ i, ‖x (k + j) ω - xstar‖ ≤ confH δ}`
on the suffix starting at `k`. -/
def suffixGuardSet (xstar : E) (x : ℕ → Ω → E) (δ : ℝ) (k i : ℕ) : Set Ω :=
  {ω | ∀ j ≤ i, ‖x (k + j) ω - xstar‖ ≤ confH δ}

lemma suffixGuardSet_measurable (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1))) (δ : ℝ) (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    MeasurableSet[shiftFiltration 𝓕 (k - 1) i] (suffixGuardSet xstar x δ k i) := by
  unfold suffixGuardSet
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  have hxj : StronglyMeasurable[shiftFiltration 𝓕 (k - 1) i] (x (k + j)) :=
    (suffixIter_adapted 𝓕 x hx k hk j).mono ((shiftFiltration 𝓕 (k - 1)).mono hj)
  exact measurableSet_le (hxj.sub stronglyMeasurable_const).norm.measurable measurable_const

lemma suffixGuardSet_mono (xstar : E) (x : ℕ → Ω → E) (δ : ℝ) (k i : ℕ) :
    suffixGuardSet xstar x δ k (i + 1) ⊆ suffixGuardSet xstar x δ k i := by
  intro ω hω j hj
  exact hω j (by omega)

set_option maxHeartbeats 2000000

/-- `app:anytime-upper-potential`: for any fixed horizon `T ≥ 2 kCut p δ`,
on the global radius event `ℛ_δ = {∀ t ≥ 1, ‖x_t - x^*‖² ≤ h²}`, the terminal suffix potential
`P_T = suffixPotential ... (T + 1 - k)` exceeds `(iota δ T)²` with probability at most
`exp(-iota δ T)`. -/
theorem anytime_horizon_event (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L' σ' p δ : ℝ) (hL' : 0 < L') (hL'1 : L' ≤ 1) (hσ'0 : 0 ≤ σ') (hσ'1 : σ' ≤ 1)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L' * ‖y - z‖)
    (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t, Integrable (fun ω =>
      ‖g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω)‖ ^ p) ν)
    (hmean : ∀ t, ν[fun ω =>
      g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω) | 𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t, ν[fun ω =>
      ‖g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω)‖ ^ p | 𝓕 t] ≤ᵐ[ν]
      fun _ => σ' ^ p)
    (T : ℕ) (hT : 2 * kCut p δ ≤ T) :
    let x := normRun x₁ p g
    let η := normStep p (c_p p)
    let k := kCut p δ
    ν {ω | (∀ t : ℕ, 1 ≤ t → ‖x t ω - xstar‖ ^ (2 : ℕ) ≤ (confH δ) ^ (2 : ℕ)) ∧
      (iota δ T) ^ (2 : ℕ) < suffixPotential f xstar (fun j => x j ω) η T k (T + 1 - k)} ≤
      ENNReal.ofReal (Real.exp (-iota δ T)) := by
  let x := normRun x₁ p g
  let η := normStep p (c_p p)
  let Λ := normLambda p
  let k := kCut p δ
  let N := T + 1 - k
  let 𝓕' := shiftFiltration 𝓕 (k - 1)
  have hk1 : 1 ≤ k := kCut_pos hp hδ hδ1
  have hkT : k ≤ T := by omega
  have hT1 : 1 ≤ T := by omega
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hη0 : η 0 = 0 := normStep_zero p (c_p p)
  have hη_pos : ∀ j, 1 ≤ j → 0 < η j := fun j hj => normStep_pos hc_pos hj
  have hη_nn : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j := fun j hj _ => (hη_pos j hj).le
  have hx_meas : ∀ t, StronglyMeasurable[𝓕 t] (x (t + 1)) :=
    anytimeIterate_adapted 𝓕 x₁ η Λ g (fun t => (hg t).measurable)
  let P_suf : ℕ → Ω → ℝ := fun i ω =>
    if i ≤ N then suffixPotential f xstar (fun j => x j ω) η T k i else 0
  have hP_adap : Adapted 𝓕' P_suf := by
    intro i
    unfold P_suf
    split_ifs with hi
    · exact suffixPotential_adapted 𝓕 hdiff xstar x hx_meas η T k hk1 i
    · exact stronglyMeasurable_zero
  have hP_nn : ∀ i ω, 0 ≤ P_suf i ω := by
    intro i ω
    unfold P_suf
    split_ifs with hi
    · exact suffixPotential_nonneg xstar hmin (fun j => x j ω) η T k i hk1 (by omega) hη0 hη_nn
    · exact le_rfl
  let J_suf : ℕ → Set Ω := suffixGuardSet xstar x δ k
  have hJ_meas : ∀ i, MeasurableSet[𝓕' i] (J_suf i) :=
    suffixGuardSet_measurable 𝓕 xstar x hx_meas δ k hk1
  have hJ_mono : ∀ i, J_suf (i + 1) ⊆ J_suf i :=
    suffixGuardSet_mono xstar x δ k
  let e_suf : ℕ → Ω → E := fun i =>
    (J_suf i).indicator (fun ω => clip (Λ (k + i)) (g (k + i) ω) - gradient f (x (k + i) ω))
  let w_suf : ℕ → Ω → E := fun i ω =>
    suffixDirection xstar (fun j => x j ω) η T k i
  have he_supp : ∀ i < N, ∀ ω, ω ∉ J_suf i → e_suf i ω = 0 :=
    fun i _ ω hω => Set.indicator_of_not_mem hω _
  have hw_meas : ∀ i < N, StronglyMeasurable[𝓕' i] (w_suf i) :=
    fun i _ => suffixDirection_adapted 𝓕 xstar x hx_meas η T k hk1 i
  have he_meas : ∀ i < N, StronglyMeasurable[𝓕' (i + 1)] (e_suf i) := by
    intro i _
    have hidx : k - 1 + (i + 1) = k + i := by omega
    have hg_meas : @Measurable Ω E (𝓕' (i + 1)) _ (g (k + i)) := by
      change @Measurable Ω E (𝓕 (k - 1 + (i + 1))) _ (g (k + i))
      rw [hidx]
      exact (hg (k + i)).measurable
    have hC : StronglyMeasurable[𝓕' (i + 1)] (fun ω => clip (Λ (k + i)) (g (k + i) ω)) :=
      ((measurable_clip (Λ (k + i))).comp hg_meas).stronglyMeasurable
    have hx_i : StronglyMeasurable[𝓕' i] (x (k + i)) :=
      suffixIter_adapted 𝓕 x hx_meas k hk1 i
    have hμ : StronglyMeasurable[𝓕' i] (fun ω => gradient f (x (k + i) ω)) :=
      (gradient_continuous L' hL'.le hlip).comp_stronglyMeasurable hx_i
    have hraw := hC.sub (hμ.mono (𝓕'.mono (by omega)))
    exact hraw.indicator (𝓕'.mono (by omega) _ (hJ_meas i))
  have hstop : ∀ i < N,
      Integrable (e_suf i) ν ∧ Integrable (fun ω => ‖e_suf i ω‖ ^ (2 : ℕ)) ν ∧
      (∀ᵐ ω ∂ν, ‖ν[e_suf i | 𝓕' i] ω‖ ≤ normB p (k + i)) ∧
      (ν[fun ω => ‖e_suf i ω‖ ^ (2 : ℕ) | 𝓕' i] ≤ᵐ[ν] fun _ => normV p (k + i)) ∧
      (∀ᵐ ω ∂ν, ‖e_suf i ω‖ ≤ 2 * Λ (k + i)) ∧
      (∀ᵐ ω ∂ν, ‖e_suf i ω - ν[e_suf i | 𝓕' i] ω‖ ≤ 2 * Λ (k + i)) := by
    intro i _
    have hki1 : 1 ≤ k + i := by omega
    have hΛ_pos : 0 < Λ (k + i) := normLambda_pos hp hki1
    have hidx : k - 1 + i = k + i - 1 := by omega
    have hidx1 : (k - 1 + i) + 1 = k + i := by omega
    have hg_m0 : @Measurable Ω E m₀ _ (g (k + i)) :=
      ((hg (k + i)).mono (𝓕.le (k + i))).measurable
    have hx_i : StronglyMeasurable[𝓕' i] (x (k + i)) :=
      suffixIter_adapted 𝓕 x hx_meas k hk1 i
    have hμ_i : StronglyMeasurable[𝓕' i] (fun ω => gradient f (x (k + i) ω)) :=
      (gradient_continuous L' hL'.le hlip).comp_stronglyMeasurable hx_i
    have hbound : ∀ᵐ ω ∂ν, ω ∈ J_suf i → ‖gradient f (x (k + i) ω)‖ ≤ Λ (k + i) / 2 := by
      apply Filter.Eventually.of_forall
      intro ω hω
      have hdist : ‖x (k + i) ω - xstar‖ ≤ confH δ := hω i le_rfl
      have hz := Radius.gradient_zero_at_minimizer (fun y => (hdiff y).hasGradientAt) xstar hmin
      have hh := hlip (x (k + i) ω) xstar
      rw [hz, sub_zero] at hh
      have h1 : ‖gradient f (x (k + i) ω)‖ ≤ confH δ := by
        calc
          ‖gradient f (x (k + i) ω)‖ ≤ L' * ‖x (k + i) ω - xstar‖ := hh
          _ ≤ 1 * confH δ := mul_le_mul hL'1 hdist (norm_nonneg _) zero_le_one
          _ = confH δ := one_mul _
      have h4 : 4 * confH δ ≤ Λ (k + i) :=
        four_confH_le_normLambda_of_ge_kCut hp hδ hδ1 (by omega)
      have : confH δ ≤ Λ (k + i) / 2 := by
        have : 0 < confH δ := confH_pos hδ hδ1
        linarith
      exact h1.trans this
    have hpm_i : Integrable (fun ω => ‖g (k + i) ω - gradient f (x (k + i) ω)‖ ^ p) ν := by
      simpa only [hidx1] using hpm (k - 1 + i)
    have hmean_i : ν[fun ω => g (k + i) ω - gradient f (x (k + i) ω) | 𝓕' i] =ᵐ[ν] 0 := by
      simpa only [𝓕', shiftFiltration, hidx1] using hmean (k - 1 + i)
    have hmoment_i : ν[fun ω => ‖g (k + i) ω - gradient f (x (k + i) ω)‖ ^ p | 𝓕' i] ≤ᵐ[ν]
        fun _ => σ' ^ p := by
      simpa only [𝓕', shiftFiltration, hidx1] using hmoment (k - 1 + i)
    obtain ⟨ hei, hei2, herange, hebias, hesecond, hecenter, _ ⟩ :=
      stopped_clipping_estimates ν (𝓕' i) (𝓕'.le i) (Λ (k + i)) p σ'
        hΛ_pos hp.le hp2 hσ'0 (g (k + i)) (fun ω => gradient f (x (k + i) ω))
        hg_m0 hμ_i (J_suf i) (hJ_meas i) hbound hpm_i hmean_i hmoment_i
    have hσp : σ' ^ p ≤ 1 := Real.rpow_le_one hσ'0 hσ'1 (by linarith)
    refine ⟨ hei, hei2, ?_, ?_, ?_, hecenter ⟩
    · filter_upwards [hebias] with ω hω
      have hb1 := bias_factor_bound (Λ (k + i)) p hΛ_pos hp2
      have hb2 := mul_le_mul_of_nonneg_right hb1 (Real.rpow_nonneg hσ'0 p)
      have hb3 : 2 * (Λ (k + i)) ^ (1 - p) * σ' ^ p ≤ normB p (k + i) := by
        unfold normB
        calc
          2 * (Λ (k + i)) ^ (1 - p) * σ' ^ p ≤ 2 * (Λ (k + i)) ^ (1 - p) * 1 :=
            mul_le_mul_of_nonneg_left hσp (by positivity)
          _ = 2 * (Λ (k + i)) ^ (1 - p) := mul_one _
      exact hω.trans (hb2.trans hb3)
    · filter_upwards [hesecond] with ω hω
      have hv1 := second_factor_bound (Λ (k + i)) p hΛ_pos hp.le
      have hv2 := mul_le_mul_of_nonneg_right hv1 (Real.rpow_nonneg hσ'0 p)
      have hv3 : 2 * (Λ (k + i)) ^ (2 - p) * σ' ^ p ≤ normV p (k + i) := by
        unfold normV
        have : (0 : ℝ) ≤ (Λ (k + i)) ^ (2 - p) := Real.rpow_nonneg hΛ_pos.le _
        nlinarith
      exact hω.trans (hv2.trans hv3)
    · filter_upwards [herange] with ω hω
      linarith
  have hw_bound : ∀ i < N, ∀ ω ∈ J_suf i,
      ‖w_suf i ω‖ ≤ Real.sqrt (2 * suffixQuadWeight η T k i) * Real.sqrt (P_suf i ω) := by
    intro i hi ω _
    have hiN : i ≤ N := by omega
    simp only [P_suf, if_pos hiN, w_suf]
    exact norm_suffixDirection_le xstar hmin (fun j => x j ω) η T k i hk1 (by omega) hη0 hη_nn
  have hrec : ∀ m < N, ∀ ω ∈ (Set.univ : Set Ω) ∩ J_suf m,
      P_suf (m + 1) ω ≤ P_suf 0 ω +
        ∑ i ∈ Finset.range (m + 1),
          (2 * suffixQuadWeight η T k i * ‖e_suf i ω‖ ^ (2 : ℕ) +
            ⟪e_suf i ω, w_suf i ω⟫_ℝ) := by
    intro m hm ω hω
    have hm1N : m + 1 ≤ N := by omega
    have h0N : 0 ≤ N := Nat.zero_le N
    simp only [P_suf, if_pos hm1N, if_pos h0N]
    let e_raw : ℕ → E := fun j => clip (Λ j) (g j ω) - gradient f (x j ω)
    have hstep_le : ∀ j, 1 ≤ j → j ≤ T → η j ≤ 1 / (2 * L') := by
      intro j hj1 _
      have h1 : η j ≤ 1 / 2 := by
        calc
          η j ≤ c_p p := normStep_le_c hp (c_p_pos hp).le hj1
          _ ≤ 1 / 1000 := c_p_le_inv_1000 hp
          _ ≤ 1 / 2 := by norm_num
      have h2 : 1 / 2 ≤ 1 / (2 * L') :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact h1.trans h2
    have hupd : ∀ i < m + 1,
        x (k + i + 1) ω =
          x (k + i) ω - η (k + i) • (gradient f (x (k + i) ω) + e_raw (k + i)) := by
      intro i _
      have hidx : (k + i - 1) + 1 = k + i := by omega
      have hidx2 : (k + i - 1) + 2 = k + i + 1 := by omega
      have h := anytimeIterate_inexact f x₁ η Λ g (k + i - 1) ω
      simpa only [x, normRun, e_raw, hidx, hidx2] using h
    have hsuf := suffix_partial_sum_potential hconv hdiff L' hL' hlip xstar
      (fun j => x j ω) e_raw η T k (m + 1) hk1 (by omega) hη0
      (fun j hj1 _ => hη_pos j hj1) hstep_le hupd
    refine hsuf.trans_eq ?_
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hω_i : ω ∈ J_suf i := by
      intro j hj
      exact hω.2 j (by omega)
    have he_eq : e_suf i ω = e_raw (k + i) := Set.indicator_of_mem hω_i _
    rw [he_eq]
  let W := cappedTail η T k
  have hW_pos : 0 < W := cappedTail_pos η T k hη_nn
  have ha_nn : ∀ i < N, 0 ≤ 2 * suffixQuadWeight η T k i := by
    intro i _
    unfold suffixQuadWeight
    have := cappedTail_pos η T (k + i) hη_nn
    positivity
  have h_eb := energy_budget_finite ν 𝓕' N P_suf hP_adap hP_nn J_suf hJ_meas hJ_mono Set.univ
    e_suf w_suf he_meas (fun i hi => (hstop i hi).1) (fun i hi => (hstop i hi).2.1)
    he_supp hw_meas
    (fun i => 2 * suffixQuadWeight η T k i)
    (fun i => Real.sqrt (2 * suffixQuadWeight η T k i))
    (fun i => normB p (k + i))
    (fun i => normV p (k + i))
    (fun i => 2 * Λ (k + i))
    (fun i => 2 * Λ (k + i))
    ha_nn
    (fun i _ => Real.sqrt_nonneg _)
    (fun i _ => normB_nonneg p (k + i))
    (fun i _ => normV_nonneg p (k + i))
    (fun i _ => by have := normLambda_nonneg p (k + i); positivity)
    (fun i _ => by have := normLambda_nonneg p (k + i); positivity)
    hw_bound hrec
    (fun i hi => (hstop i hi).2.2.1)
    (fun i hi => (hstop i hi).2.2.2.1)
    (fun i hi => (hstop i hi).2.2.2.2.1)
    (fun i hi => (hstop i hi).2.2.2.2.2)
    ((confH δ) ^ (2 : ℕ) / 2)
    (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ))
    (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
    (2 * K_const p * c_p p / ell 1)
    (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ))
    (2 * Real.sqrt 2 * Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ))
    (iota δ T)
    (by positivity)
    (by have := K_const_pos hp; have := c_p_pos hp; have := ell_pos le_rfl; positivity)
    (by have := K_const_pos hp; have := c_p_pos hp; have := ell_pos le_rfl; positivity)
    (by have := K_const_pos hp; have := c_p_pos hp; have := ell_pos le_rfl; positivity)
    (by have := K_const_pos hp; have := c_p_pos hp; have := ell_pos le_rfl; positivity)
    (by have := K_const_pos hp; have := c_p_pos hp; have := ell_pos le_rfl; positivity)
    (by have := four_lt_iota hδ hδ1 hT1; linarith)
    (sufA_sum_le hp hp2 hT1 hk1 hkT)
    (fun i hi => sufK_sup_le hp hp2 hT1 hk1 i (by omega))
    (sufB_sum_le hp hp2 hT1 hk1 hkT)
    (sufV_sum_le hp hp2 hT1 hk1 hkT)
    (fun i hi => sufJ_sup_le hp hp2 hT1 hk1 i (by omega))
  have hH_le : energyThreshold
      ((confH δ) ^ (2 : ℕ) / 2)
      (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ))
      (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
      (2 * K_const p * c_p p / ell 1)
      (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ))
      (2 * Real.sqrt 2 * Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ))
      (iota δ T) ≤ (iota δ T) ^ (2 : ℕ) :=
    suffix_potential_threshold_le hp hδ hδ1 hT1
  have hsub : {ω | (∀ t : ℕ, 1 ≤ t → ‖x t ω - xstar‖ ^ (2 : ℕ) ≤ (confH δ) ^ (2 : ℕ)) ∧
      (iota δ T) ^ (2 : ℕ) < suffixPotential f xstar (fun j => x j ω) η T k (T + 1 - k)} ⊆
      {ω ∈ (Set.univ : Set Ω) | P_suf 0 ω ≤ (confH δ) ^ (2 : ℕ) / 2 ∧
        ∃ m < N, ω ∈ J_suf m ∧
          energyThreshold
            ((confH δ) ^ (2 : ℕ) / 2)
            (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ))
            (8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ))
            (2 * K_const p * c_p p / ell 1)
            (4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ))
            (2 * Real.sqrt 2 * Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ))
            (iota δ T) < P_suf (m + 1) ω} := by
    intro ω ⟨ hrad, hgt ⟩
    have h0N : 0 ≤ N := Nat.zero_le N
    have hP0 : P_suf 0 ω ≤ (confH δ) ^ (2 : ℕ) / 2 := by
      simp only [P_suf, if_pos h0N, suffixPotential_zero f xstar (fun j => x j ω) η T k hη_nn]
      have hk_rad := hrad k hk1
      linarith
    refine ⟨ Set.mem_univ ω, hP0, T - k, by omega, ?_, ?_ ⟩
    · intro j hj
      have hkj1 : 1 ≤ k + j := by omega
      have hsq := hrad (k + j) hkj1
      have hconf_pos : 0 ≤ confH δ := by have := four_lt_confH hδ hδ1; linarith
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hconf_pos]
      exact Real.sqrt_le_sqrt hsq
    · have hm1 : T - k + 1 = N := by omega
      rw [hm1]
      simp only [P_suf, if_pos (le_rfl : N ≤ N)]
      exact hH_le.trans_lt hgt
  exact (measure_mono hsub).trans h_eb

/-! ## 4. Time-Uniform Upper Bound in the Normalized Regime -/

/-- `app:anytime-upper-direct`: in the normalized regime (`L' ≤ 1, R = 1, σ' ≤ 1`),
with probability at least `1 - δ`, simultaneously for every integer `T ≥ 1`:
`f(x_{T+1}) - f(x^*) ≤ D_p T ^ (-β) ι_T(δ) ^ 4` and `‖x_{T+1} - x^*‖² ≤ h²`. -/
theorem anytime_upper_normalized (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L' σ' p δ : ℝ) (hL' : 0 < L') (hL'1 : L' ≤ 1) (hσ'0 : 0 ≤ σ') (hσ'1 : σ' ≤ 1)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L' * ‖y - z‖)
    (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y) (hinit : ‖x₁ - xstar‖ ≤ 1)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t, Integrable (fun ω =>
      ‖g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω)‖ ^ p) ν)
    (hmean : ∀ t, ν[fun ω =>
      g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω) | 𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t, ν[fun ω =>
      ‖g (t + 1) ω - gradient f (normRun x₁ p g (t + 1) ω)‖ ^ p | 𝓕 t] ≤ᵐ[ν]
      fun _ => σ' ^ p) :
    ENNReal.ofReal (1 - δ) ≤ ν {ω | ∀ T : ℕ, 1 ≤ T →
      f (normRun x₁ p g (T + 1) ω) - f xstar ≤
        D_p p * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) ∧
      ‖normRun x₁ p g (T + 1) ω - xstar‖ ^ (2 : ℕ) ≤ (confH δ) ^ (2 : ℕ)} := by
  let x := normRun x₁ p g
  let η := normStep p (c_p p)
  let k := kCut p δ
  have hk1 : 1 ≤ k := kCut_pos hp hδ hδ1
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hη0 : η 0 = 0 := normStep_zero p (c_p p)
  let B_rad : Set Ω :=
    {ω | ∃ t : ℕ, 1 ≤ t ∧ (confH δ) ^ (2 : ℕ) < ‖x t ω - xstar‖ ^ (2 : ℕ)}
  let B_hor : ℕ → Set Ω := fun i =>
    {ω | (∀ t : ℕ, 1 ≤ t → ‖x t ω - xstar‖ ^ (2 : ℕ) ≤ (confH δ) ^ (2 : ℕ)) ∧
      (iota δ (2 * k + i)) ^ (2 : ℕ) <
        suffixPotential f xstar (fun j => x j ω) η (2 * k + i) k (2 * k + i + 1 - k)}
  have hB_rad : ν B_rad ≤ ENNReal.ofReal (Real.exp (-confH δ)) :=
    anytime_radius_event ν 𝓕 hconv hdiff L' σ' p δ hL' hL'1 hσ'0 hσ'1 hp hp2 hδ hδ1
      hlip x₁ xstar hmin hinit g hg hpm hmean hmoment
  have hB_hor : ∀ i : ℕ, ν (B_hor i) ≤ ENNReal.ofReal (Real.exp (-iota δ (2 * k + i))) :=
    fun i => anytime_horizon_event ν 𝓕 hconv hdiff L' σ' p δ hL' hL'1 hσ'0 hσ'1 hp hp2 hδ hδ1
      hlip x₁ xstar hmin g hg hpm hmean hmoment (2 * k + i) (by omega)
  have hB_union : ν (⋃ i : ℕ, B_hor i) ≤
      ENNReal.ofReal (2 * Real.exp (-confH δ)) := by
    have h1 : ν (⋃ i : ℕ, B_hor i) ≤ ∑' i, ν (B_hor i) := measure_iUnion_le _
    have h2 : ∑' i, ν (B_hor i) ≤ ∑' i, ENNReal.ofReal (Real.exp (-iota δ (2 * k + i))) :=
      ENNReal.tsum_le_tsum hB_hor
    have h3 : ∑' i, ENNReal.ofReal (Real.exp (-iota δ (2 * k + i))) ≤
        ENNReal.ofReal (2 * Real.exp (-confH δ)) := by
      apply ENNReal.tsum_le_of_sum_range_le
      intro N
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.exp_nonneg _)]
      have hexp_h : Real.exp (-confH δ) = δ / 100 := by
        unfold confH
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      have hexp_iota : ∀ t : ℕ, 1 ≤ t →
          Real.exp (-iota δ t) = δ / 100 * ((t : ℝ) ^ (-1 - (1 : ℝ))) := by
        intro t ht
        have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
        unfold iota
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div,
          show (-1 - (1 : ℝ)) = (-2 : ℝ) by ring,
          show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg ht_pos.le, Real.rpow_natCast]
        ring
      have hterm_le : ∀ i : ℕ,
          Real.exp (-iota δ (2 * k + i)) ≤
            (δ / 100) * (((i + 1 : ℕ) : ℝ) ^ (-1 - (1 : ℝ))) := by
        intro i
        have ht_ge : i + 1 ≤ 2 * k + i := by omega
        have ht1 : 1 ≤ 2 * k + i := by omega
        rw [hexp_iota (2 * k + i) ht1]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by exact_mod_cast ht_ge) (by norm_num)
      have hsum_le : (∑ i ∈ Finset.range N, Real.exp (-iota δ (2 * k + i))) ≤
          2 * Real.exp (-confH δ) := by
        calc
          (∑ i ∈ Finset.range N, Real.exp (-iota δ (2 * k + i)))
            ≤ ∑ i ∈ Finset.range N, (δ / 100) * (((i + 1 : ℕ) : ℝ) ^ (-1 - (1 : ℝ))) :=
              Finset.sum_le_sum (fun i _ => hterm_le i)
          _ = (δ / 100) * (∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ (-1 - (1 : ℝ)))) := by
              rw [← Finset.mul_sum]
          _ ≤ (δ / 100) * (1 + 1 / (1 : ℝ)) := by
              apply mul_le_mul_of_nonneg_left (sum_rpow_neg_one_sub_le zero_lt_one N) (by positivity)
          _ = 2 * Real.exp (-confH δ) := by rw [hexp_h]; ring
      exact ENNReal.ofReal_le_ofReal hsum_le
    exact (h1.trans h2).trans h3
  let bad : Set Ω := B_rad ∪ (⋃ i : ℕ, B_hor i)
  have hbad : ν bad ≤ ENNReal.ofReal δ := by
    have hunion : ν bad ≤ ν B_rad + ν (⋃ i : ℕ, B_hor i) := measure_union_le _ _
    have hsum := add_le_add hB_rad hB_union
    have heq : ENNReal.ofReal (Real.exp (-confH δ)) + ENNReal.ofReal (2 * Real.exp (-confH δ)) =
        ENNReal.ofReal (3 * Real.exp (-confH δ)) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (by positivity)]
      congr 1; ring
    rw [heq] at hsum
    have h3 : 3 * Real.exp (-confH δ) ≤ δ := by
      have hexp_h : Real.exp (-confH δ) = δ / 100 := by
        unfold confH
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      linarith
    exact (hunion.trans hsum).trans (ENNReal.ofReal_le_ofReal h3)
  have hgood : ENNReal.ofReal (1 - δ) ≤ ν badᶜ := by
    rw [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
    apply tsub_le_iff_right.mpr
    have hh : (1 : ℝ≥0∞) ≤ ν bad + ν badᶜ := by
      simpa only [union_compl_self, measure_univ] using
        (measure_union_le bad badᶜ : ν (bad ∪ badᶜ) ≤ ν bad + ν badᶜ)
    exact hh.trans ((add_le_add_right hbad (ν badᶜ)).trans_eq (add_comm _ _))
  apply hgood.trans
  apply measure_mono
  intro ω hω T hT1
  have hrad : ∀ t : ℕ, 1 ≤ t → ‖x t ω - xstar‖ ^ (2 : ℕ) ≤ (confH δ) ^ (2 : ℕ) := by
    intro t ht1
    exact le_of_not_gt (fun hgt => hω (Or.inl ⟨ t, ht1, hgt ⟩))
  refine ⟨ ?_, hrad (T + 1) (by omega) ⟩
  by_cases hTk : T < 2 * k
  · -- Early horizons `1 ≤ T < 2k`
    have hgrad : ∀ u, HasGradientAt f (gradient f u) u := fun u => (hdiff u).hasGradientAt
    have hz := Radius.gradient_zero_at_minimizer hgrad xstar hmin
    have hsm := ClippedSGD.smooth_upper hgrad hlip xstar (x (T + 1) ω)
    rw [hz, inner_zero_left, add_zero] at hsm
    have hgap1 : f (x (T + 1) ω) - f xstar ≤ (confH δ) ^ (2 : ℕ) / 2 := by
      have h1 : f (x (T + 1) ω) - f xstar ≤ L' / 2 * ‖x (T + 1) ω - xstar‖ ^ (2 : ℕ) := by
        linarith
      have h2 : L' / 2 * ‖x (T + 1) ω - xstar‖ ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * ‖x (T + 1) ω - xstar‖ ^ (2 : ℕ) := by
        have := sq_nonneg ‖x (T + 1) ω - xstar‖
        nlinarith
      have h3 := hrad (T + 1) (by omega)
      linarith
    exact early_time_rate_bound hp hp2 hδ hδ1 hT1 hTk hgap1
  · -- Late horizons `T ≥ 2k`
    have hT2k : 2 * k ≤ T := le_of_not_gt hTk
    have hkT : k ≤ T := by omega
    have hP_le : suffixPotential f xstar (fun j => x j ω) η T k (T + 1 - k) ≤
        (iota δ T) ^ (2 : ℕ) := by
      apply le_of_not_gt
      intro hgt
      apply hω
      right
      rw [Set.mem_iUnion]
      refine ⟨ T - 2 * k, hrad, ?_ ⟩
      have hidx : 2 * k + (T - 2 * k) = T := by omega
      simpa only [hidx] using hgt
    have hη_nn : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j :=
      fun j hj _ => normStep_nonneg (p := p) (c := c_p p) hc_pos.le j
    have hend := suffix_endpoint_bound hconv hdiff L' hL' hlip xstar hmin
      (fun j => x j ω) η T k hk1 hkT hη0 hη_nn
    have hP_nn : 0 ≤ suffixPotential f xstar (fun j => x j ω) η T k (T + 1 - k) :=
      suffixPotential_nonneg xstar hmin (fun j => x j ω) η T k (T + 1 - k) hk1
        (by omega) hη0 hη_nn
    have hW_pos : 0 < cappedTail η T k := cappedTail_pos η T k hη_nn
    have hend2 : f (x (T + 1) ω) - f xstar ≤
        2 * suffixPotential f xstar (fun j => x j ω) η T k (T + 1 - k) /
          cappedTail η T k := by
      refine hend.trans ?_
      apply div_le_div_of_nonneg_right _ hW_pos.le
      nlinarith
    exact hend2.trans (late_time_rate_bound hp hδ hδ1 hT2k hP_le)

/-! ## 5. Rescaling to General `(L, R, σ)` and `thm:anytime-upper` -/

/-- Positive homogeneity of `clip`: for `Q > 0`, `clip (Q * Λ) (Q • v) = Q • clip Λ v`. -/
lemma clip_smul_pos (Q Λ : ℝ) (hQ : 0 < Q) (v : E) :
    clip (Q * Λ) (Q • v) = Q • clip Λ v := by
  unfold clip
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hQ]
  have hiff : Q * ‖v‖ ≤ Q * Λ ↔ ‖v‖ ≤ Λ := mul_le_mul_left hQ
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; exact h2 (hiff.mp h1)
  · exfalso; exact h1 (hiff.mpr h2)
  · have hdiv : Q * Λ / (Q * ‖v‖) = Λ / ‖v‖ := mul_div_mul_left Λ ‖v‖ hQ.ne'
    rw [hdiv, smul_smul, smul_smul, mul_comm]

/-- Exact coupling between `anytimeRun x₁ L R σ p g` and the normalized run
`normRun 0 p (fun t ω => (1 / Q) • g t ω)`:
for all `t ≥ 1`, `anytimeRun x₁ L R σ p g t ω = x₁ + R • normRun 0 p g' t ω`. -/
lemma anytimeRun_eq_rescaled (x₁ : E) (L R σ p : ℝ) (hL : 0 < L) (hR : 0 < R)
    (g : ℕ → Ω → E) (t : ℕ) (ω : Ω) :
    let Q := scaleQ L R σ
    let g' : ℕ → Ω → E := fun i ω' => (1 / Q) • g i ω'
    anytimeRun x₁ L R σ p g (t + 1) ω = x₁ + R • normRun (0 : E) p g' (t + 1) ω := by
  intro Q g'
  have hQ : 0 < Q := scaleQ_pos hL hR
  induction t with
  | zero =>
    simp [anytimeRun, normRun, anytimeIterate]
  | succ t ih =>
    change anytimeRun x₁ L R σ p g (t + 1) ω -
        anytimeStep L R σ p (t + 1) • clip (anytimeLambda L R σ p (t + 1)) (g (t + 1) ω) =
      x₁ + R • (normRun (0 : E) p g' (t + 1) ω -
        normStep p (c_p p) (t + 1) • clip (normLambda p (t + 1)) (g' (t + 1) ω))
    rw [ih, anytimeStep_eq, anytimeLambda_eq]
    have hg_eq : g (t + 1) ω = Q • g' (t + 1) ω := by
      dsimp [g']
      rw [smul_smul, mul_one_div_cancel hQ.ne', one_smul]
    have hclip : clip (Q * normLambda p (t + 1)) (g (t + 1) ω) =
        Q • clip (normLambda p (t + 1)) (g' (t + 1) ω) := by
      rw [hg_eq]
      exact clip_smul_pos Q (normLambda p (t + 1)) hQ (g' (t + 1) ω)
    rw [hclip, smul_sub, smul_smul, smul_smul]
    have hscalar : R / Q * normStep p (c_p p) (t + 1) * Q =
        R * normStep p (c_p p) (t + 1) := by
      field_simp
    rw [hscalar]
    abel

/-- Rescaled objective `F(y) = (f(x₁ + R • y) - f(x^*)) / (R * Q)`. -/
noncomputable def rescaledObj (f : E → ℝ) (x₁ xstar : E) (R Q : ℝ) (y : E) : ℝ :=
  (f (x₁ + R • y) - f xstar) / (R * Q)

lemma rescaledObj_convex {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (x₁ xstar : E) (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    ConvexOn ℝ univ (rescaledObj f x₁ xstar R Q) := by
  let φ : E →ᵃ[ℝ] E :=
    R • AffineMap.id ℝ E + AffineMap.const ℝ E x₁
  have hφ : ∀ y, f (x₁ + R • y) = (f ∘ φ) y := by
    intro y
    simp [φ, add_comm]
  have hc1 : ConvexOn ℝ univ (f ∘ φ) := hconv.comp_affineMap φ
  have hc_neg : ConvexOn ℝ (univ : Set E) (fun _ => - f xstar) :=
    convexOn_const (- f xstar) convex_univ
  have hc2 : ConvexOn ℝ univ (fun y => f (x₁ + R • y) - f xstar) := by
    have hsum := hc1.add hc_neg
    have heq : (f ∘ φ + fun _ => -f xstar) = (fun y => f (x₁ + R • y) - f xstar) := by
      funext y
      simp [hφ, sub_eq_add_neg]
    exact heq ▸ hsum
  have hc3 := hc2.smul (inv_nonneg.mpr (mul_pos hR hQ).le)
  convert hc3 using 1
  funext y
  unfold rescaledObj
  simp [div_eq_inv_mul]

lemma rescaledObj_hasGradientAt {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (x₁ xstar : E) (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) (y : E) :
    HasGradientAt (rescaledObj f x₁ xstar R Q) ((1 / Q) • gradient f (x₁ + R • y)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun z : E => x₁ + R • z) (R • ContinuousLinearMap.id ℝ E) y := by
    simpa only [zero_add] using
      (hasFDerivAt_const x₁ y).add (R • ContinuousLinearMap.id ℝ E).hasFDerivAt
  have h2 : HasFDerivAt f
      (InnerProductSpace.toDual ℝ E (gradient f (x₁ + R • y))) (x₁ + R • y) :=
    hasGradientAt_iff_hasFDerivAt.mp (hdiff (x₁ + R • y)).hasGradientAt
  have h3 : HasFDerivAt (fun z : E => f (x₁ + R • z) - f xstar)
      ((InnerProductSpace.toDual ℝ E (gradient f (x₁ + R • y))).comp
        (R • ContinuousLinearMap.id ℝ E)) y := by
    simpa only [sub_zero] using (h2.comp y h1).sub (hasFDerivAt_const (f xstar) y)
  have h4 := h3.const_mul ((R * Q)⁻¹)
  have heq_fun : (fun z : E => (R * Q)⁻¹ * (f (x₁ + R • z) - f xstar)) =
      rescaledObj f x₁ xstar R Q := by
    funext z
    unfold rescaledObj
    ring
  rw [heq_fun] at h4
  convert h4 using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply,
    real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
  have hRQ : R * Q ≠ 0 := mul_ne_zero hR.ne' hQ.ne'
  field_simp
  ring

lemma rescaledObj_differentiable {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (x₁ xstar : E) (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) :
    Differentiable ℝ (rescaledObj f x₁ xstar R Q) :=
  fun y => (rescaledObj_hasGradientAt hdiff x₁ xstar R Q hR hQ y).differentiableAt

lemma rescaledObj_gradient {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (x₁ xstar : E) (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) (y : E) :
    gradient (rescaledObj f x₁ xstar R Q) y = (1 / Q) • gradient f (x₁ + R • y) :=
  (rescaledObj_hasGradientAt hdiff x₁ xstar R Q hR hQ y).gradient

/-- `thm:anytime-upper` with centered conditional mean hypothesis
`E[g_t - ∇f(x_t) | 𝓕_{t-1}] = 0`:
For every `δ ∈ (0, 1)`, with probability at least `1 - δ`, simultaneously for every integer `T ≥ 1`,
`f(x_{T+1}) - f(x^*) ≤ D_p R Q T ^ (-β) ι_T(δ) ^ 4` and `‖x_{T+1} - x^*‖² ≤ R² [log(100/δ)]²`. -/
theorem anytime_upper_centered (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L R σ p δ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y) (hinitial : ‖x₁ - xstar‖ ≤ R)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t, Integrable (fun ω =>
      ‖g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)‖ ^ p) ν)
    (hmean : ∀ t, ν[fun ω =>
      g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω) | 𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t, ν[fun ω =>
      ‖g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)‖ ^ p | 𝓕 t] ≤ᵐ[ν]
      fun _ => σ ^ p) :
    ENNReal.ofReal (1 - δ) ≤ ν {ω | ∀ T : ℕ, 1 ≤ T →
      f (anytimeRun x₁ L R σ p g (T + 1) ω) - f xstar ≤
        D_p p * R * scaleQ L R σ * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) ∧
      ‖anytimeRun x₁ L R σ p g (T + 1) ω - xstar‖ ^ (2 : ℕ) ≤
        R ^ (2 : ℕ) * (confH δ) ^ (2 : ℕ)} := by
  let Q := scaleQ L R σ
  have hQ : 0 < Q := scaleQ_pos hL hR
  let L' := L * R / Q
  let σ' := σ / Q
  have hL' : 0 < L' := div_pos (mul_pos hL hR) hQ
  have hL'1 : L' ≤ 1 := (div_le_one hQ).mpr (le_max_left (L * R) σ)
  have hσ'0 : 0 ≤ σ' := div_nonneg hσ hQ.le
  have hσ'1 : σ' ≤ 1 := (div_le_one hQ).mpr (le_max_right (L * R) σ)
  let F := rescaledObj f x₁ xstar R Q
  let ystar : E := (1 / R) • (xstar - x₁)
  let g' : ℕ → Ω → E := fun t ω => (1 / Q) • g t ω
  have hxy_ystar : x₁ + R • ystar = xstar := by
    dsimp [ystar]
    rw [smul_smul, mul_one_div_cancel hR.ne', one_smul, add_sub_cancel]
  have hF_ystar : F ystar = 0 := by
    dsimp [F, rescaledObj]
    rw [hxy_ystar, sub_self, zero_div]
  have hF_min : ∀ y, F ystar ≤ F y := by
    intro y
    rw [hF_ystar]
    unfold F rescaledObj
    exact div_nonneg (sub_nonneg.mpr (hmin _)) (mul_pos hR hQ).le
  have hF_conv : ConvexOn ℝ univ F := rescaledObj_convex hconv x₁ xstar R Q hR hQ
  have hF_diff : Differentiable ℝ F := rescaledObj_differentiable hdiff x₁ xstar R Q hR hQ
  have hF_lip : ∀ y z, ‖gradient F y - gradient F z‖ ≤ L' * ‖y - z‖ := by
    intro y z
    rw [rescaledObj_gradient hdiff x₁ xstar R Q hR hQ y,
      rescaledObj_gradient hdiff x₁ xstar R Q hR hQ z,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hQ)]
    have hsub : (x₁ + R • y) - (x₁ + R • z) = R • (y - z) := by
      rw [add_sub_add_left_eq_sub, ← smul_sub]
    have h1 := hlip (x₁ + R • y) (x₁ + R • z)
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (one_div_nonneg.mpr hQ.le)
    calc
      1 / Q * ‖gradient f (x₁ + R • y) - gradient f (x₁ + R • z)‖
        ≤ 1 / Q * (L * (R * ‖y - z‖)) := h2
      _ = L' * ‖y - z‖ := by dsimp [L']; ring
  have hy_init : ‖(0 : E) - ystar‖ ≤ 1 := by
    dsimp [ystar]
    rw [zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hR),
      norm_sub_rev]
    calc
      (1 / R) * ‖x₁ - xstar‖ ≤ (1 / R) * R := mul_le_mul_of_nonneg_left hinitial (by positivity)
      _ = 1 := one_div_mul_cancel hR.ne'
  have hg'_adap : Adapted 𝓕 g' := fun t => (hg t).const_smul (1 / Q)
  have herr_eq : ∀ t ω,
      g' (t + 1) ω - gradient F (normRun (0 : E) p g' (t + 1) ω) =
        (1 / Q) • (g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)) := by
    intro t ω
    rw [rescaledObj_gradient hdiff x₁ xstar R Q hR hQ,
      ← anytimeRun_eq_rescaled x₁ L R σ p hL hR g t ω, smul_sub]
  have herr_norm : ∀ t ω,
      ‖g' (t + 1) ω - gradient F (normRun (0 : E) p g' (t + 1) ω)‖ ^ p =
        (1 / Q) ^ p * ‖g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)‖ ^ p := by
    intro t ω
    rw [herr_eq t ω, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hQ),
      Real.mul_rpow (by positivity) (norm_nonneg _)]
  have hpm' : ∀ t, Integrable (fun ω =>
      ‖g' (t + 1) ω - gradient F (normRun (0 : E) p g' (t + 1) ω)‖ ^ p) ν := by
    intro t
    simp_rw [herr_norm t]
    exact (hpm t).const_mul ((1 / Q) ^ p)
  have hmean' : ∀ t, ν[fun ω =>
      g' (t + 1) ω - gradient F (normRun (0 : E) p g' (t + 1) ω) | 𝓕 t] =ᵐ[ν] 0 := by
    intro t
    simp_rw [herr_eq t]
    have hsc := condExp_smul (1 / Q)
      (fun ω => g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)) (𝓕 t) (μ := ν)
    filter_upwards [hsc, hmean t] with ω hscω hmω
    change ν[fun a => (1 / Q) •
        (g (t + 1) a - gradient f (anytimeRun x₁ L R σ p g (t + 1) a)) | 𝓕 t] ω =
      (1 / Q) • ν[fun a =>
        g (t + 1) a - gradient f (anytimeRun x₁ L R σ p g (t + 1) a) | 𝓕 t] ω at hscω
    rw [hscω, hmω, Pi.zero_apply, smul_zero]
  have hmoment' : ∀ t, ν[fun ω =>
      ‖g' (t + 1) ω - gradient F (normRun (0 : E) p g' (t + 1) ω)‖ ^ p | 𝓕 t] ≤ᵐ[ν]
      fun _ => σ' ^ p := by
    intro t
    simp_rw [herr_norm t]
    have hsc := condExp_smul ((1 / Q) ^ p)
      (fun ω => ‖g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)‖ ^ p) (𝓕 t) (μ := ν)
    filter_upwards [hsc, hmoment t] with ω hscω hmomω
    change ν[fun a => (1 / Q) ^ p *
        ‖g (t + 1) a - gradient f (anytimeRun x₁ L R σ p g (t + 1) a)‖ ^ p | 𝓕 t] ω =
      (1 / Q) ^ p * ν[fun a =>
        ‖g (t + 1) a - gradient f (anytimeRun x₁ L R σ p g (t + 1) a)‖ ^ p | 𝓕 t] ω at hscω
    rw [hscω]
    have h1 := mul_le_mul_of_nonneg_left hmomω (by positivity : 0 ≤ (1 / Q) ^ p)
    refine h1.trans_eq ?_
    dsimp [σ']
    rw [← Real.mul_rpow (by positivity) hσ, one_div_mul_eq_div]
  have hnorm := anytime_upper_normalized ν 𝓕 hF_conv hF_diff L' σ' p δ
    hL' hL'1 hσ'0 hσ'1 hp hp2 hδ hδ1 hF_lip (0 : E) ystar hF_min hy_init g' hg'_adap
    hpm' hmean' hmoment'
  apply hnorm.trans
  apply measure_mono
  intro ω hω T hT1
  obtain ⟨ hrate, hrad ⟩ := hω T hT1
  have hxy := anytimeRun_eq_rescaled x₁ L R σ p hL hR g T ω
  refine ⟨ ?_, ?_ ⟩
  · have hF_val : F (normRun (0 : E) p g' (T + 1) ω) - F ystar =
        (f (anytimeRun x₁ L R σ p g (T + 1) ω) - f xstar) / (R * Q) := by
      rw [hF_ystar, sub_zero]
      unfold F rescaledObj
      rw [← hxy]
    rw [hF_val, div_le_iff₀ (mul_pos hR hQ)] at hrate
    calc
      f (anytimeRun x₁ L R σ p g (T + 1) ω) - f xstar
        ≤ D_p p * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) * (R * Q) := hrate
      _ = D_p p * R * Q * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) := by ring
  · have hdiff_xy : anytimeRun x₁ L R σ p g (T + 1) ω - xstar =
        R • (normRun (0 : E) p g' (T + 1) ω - ystar) := by
      rw [hxy, ← hxy_ystar, smul_sub]
      abel
    rw [hdiff_xy, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_pow]
    exact mul_le_mul_of_nonneg_left hrad (by positivity)

/-- `thm:anytime-upper`:
Time-uniform upper bound for horizon-free clipped SGD with schedule
`η_t = (R / Q) c_p t ^ (-a) / ℓ_t²`, `λ_t = 4 Q t ^ b`.
For every `δ ∈ (0, 1)`, with probability at least `1 - δ`, simultaneously for every integer `T ≥ 1`:
`f(x_{T+1}) - f(x^*) ≤ D_p R Q T ^ (-β) ι_T(δ) ^ 4` and
`‖x_{T+1} - x^*‖² ≤ R² [log(100 / δ)]²`. -/
theorem anytime_upper (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L R σ p δ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y - gradient f z‖ ≤ L * ‖y - z‖)
    (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y) (hinitial : ‖x₁ - xstar‖ ≤ R)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t, Integrable (fun ω =>
      ‖g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)‖ ^ p) ν)
    (hmean : ∀ t, ν[g (t + 1) | 𝓕 t] =ᵐ[ν]
      fun ω => gradient f (anytimeRun x₁ L R σ p g (t + 1) ω))
    (hmoment : ∀ t, ν[fun ω =>
      ‖g (t + 1) ω - gradient f (anytimeRun x₁ L R σ p g (t + 1) ω)‖ ^ p | 𝓕 t] ≤ᵐ[ν]
      fun _ => σ ^ p) :
    ENNReal.ofReal (1 - δ) ≤ ν {ω | ∀ T : ℕ, 1 ≤ T →
      f (anytimeRun x₁ L R σ p g (T + 1) ω) - f xstar ≤
        D_p p * R * scaleQ L R σ * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) ∧
      ‖anytimeRun x₁ L R σ p g (T + 1) ω - xstar‖ ^ (2 : ℕ) ≤
        R ^ (2 : ℕ) * (confH δ) ^ (2 : ℕ)} := by
  apply anytime_upper_centered ν 𝓕 hconv hdiff L R σ p δ hL hR hσ hp hp2 hδ hδ1
    hlip x₁ xstar hmin hinitial g hg hpm _ hmoment
  intro t
  have hQ : 0 < scaleQ L R σ := scaleQ_pos hL hR
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hη_nn : ∀ i, 1 ≤ i → 0 ≤ anytimeStep L R σ p i := by
    intro i _
    rw [anytimeStep_eq]
    have := normStep_nonneg (p := p) (c := c_p p) hc_pos.le i
    positivity
  have hΛ_nn : ∀ i, 1 ≤ i → 0 ≤ anytimeLambda L R σ p i := by
    intro i _
    rw [anytimeLambda_eq]
    have := normLambda_nonneg p i
    positivity
  have hμ := anytimeIterate_gradient_predictable L hL.le hlip 𝓕 x₁
    (anytimeStep L R σ p) (anytimeLambda L R σ p) g (fun i => (hg i).measurable) t
  have hμi := anytimeIterate_gradient_integrable ν 𝓕 hdiff L R
    (anytimeStep L R σ p) (anytimeLambda L R σ p) hL hη_nn hΛ_nn hlip x₁ xstar hmin
    hinitial g hg t
  exact raw_unbiased_to_centered ν (𝓕 t) (𝓕.le t) (g (t + 1))
    (fun ω => gradient f (anytimeRun x₁ L R σ p g (t + 1) ω))
    (((hg (t + 1)).mono (𝓕.le (t + 1))).measurable) hμ hμi p hp.le (hpm t) (hmean t)

end

end ClippedSGD.AnytimeUpperMain
