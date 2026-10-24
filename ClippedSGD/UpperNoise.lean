import ClippedSGD.UpperRun
import ClippedSGD.PredictableInner
import ClippedSGD.UpperConcentration

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.UpperNoise
open Clipping ClippingConditional Potential LinearSchedule FiniteHorizonPathwise Localization UpperParameters UpperRun PredictableInner
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m₀ : MeasurableSpace Ω}

/-- The cutoff vanishes after the horizon, so the processes are indexed by all times. -/
def stoppingSet (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → Ω → E) (t : ℕ) : Set Ω :=
  if t<T then {ω | active η R T xstar (fun i => x i ω) (t+1)} else ∅

lemma stoppingSet_measurable (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (η R : ℝ) (T t : ℕ) :
    MeasurableSet[𝓕 t] (stoppingSet η R T xstar x t) := by
  unfold stoppingSet
  split_ifs
  · exact active_measurable 𝓕 xstar x hx η R T t
  · exact @MeasurableSet.empty Ω (𝓕 t)

def stopError (f : E → ℝ) (η R Λ : ℝ) (T : ℕ) (xstar : E) (x g : ℕ → Ω → E) (t : ℕ) : Ω → E :=
  (stoppingSet η R T xstar x t).indicator (fun ω => clip Λ (g (t+1) ω)-gradient f (x (t+1) ω))

def bias (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ) (T : ℕ)
    (xstar : E) (x g : ℕ → Ω → E) (t : ℕ) : Ω → E := ν[stopError f η R Λ T xstar x g t|𝓕 t]

def centered (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ) (T : ℕ)
    (xstar : E) (x g : ℕ → Ω → E) (t : ℕ) : Ω → E :=
  fun ω => stopError f η R Λ T xstar x g t ω-bias ν 𝓕 f η R Λ T xstar x g t ω

structure Estimates (ν : Measure Ω) (m : MeasurableSpace Ω) (e : Ω → E) (Λ B V : ℝ) : Prop where
  integrable : Integrable e ν
  square_integrable : Integrable (fun ω => ‖e ω‖^2) ν
  range_bound : ∀ᵐ ω ∂ν, ‖e ω‖ ≤ 2*Λ
  bias_bound : ∀ᵐ ω ∂ν, ‖ν[e|m] ω‖ ≤ B
  second_bound : ν[fun ω => ‖e ω‖^2|m] ≤ᵐ[ν] fun _ => V
  centered_range : ∀ᵐ ω ∂ν, ‖e ω-ν[e|m] ω‖ ≤ 2*Λ
  centered_second : ν[fun ω => ‖e ω-ν[e|m] ω‖^2|m] ≤ᵐ[ν] fun _ => V

/-- The conditional moment estimates for the stopped oracle error. -/
theorem stopped_estimates (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hdiff : Differentiable ℝ f) (L η R Λ σ p : ℝ)
    (hL : 0 < L) (hΛ : 0 < Λ) (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hguard : 4*L*R ≤ Λ) (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (T : ℕ) (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x g : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (hg : Adapted 𝓕 g)
    (hpm : ∀ t < T, Integrable (fun ω => ‖g (t+1) ω-gradient f (x (t+1) ω)‖^p) ν)
    (hmean : ∀ t < T, ν[fun ω => g (t+1) ω-gradient f (x (t+1) ω)|𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t < T, ν[fun ω => ‖g (t+1) ω-gradient f (x (t+1) ω)‖^p|𝓕 t] ≤ᵐ[ν] fun _ => σ^p)
    (t : ℕ) : Estimates ν (𝓕 t) (stopError f η R Λ T xstar x g t) Λ (biasBudget Λ σ p) (varianceBudget Λ σ p) := by
  have hB : 0 ≤ biasBudget Λ σ p := by unfold biasBudget; positivity
  have hV : 0 ≤ varianceBudget Λ σ p := by unfold varianceBudget; positivity
  by_cases ht : t<T
  · have hμ : StronglyMeasurable[𝓕 t] (fun ω => gradient f (x (t+1) ω)) :=
      (gradient_continuous L hL.le hlip).comp_stronglyMeasurable (hx t)
    have hgs : Measurable (g (t+1)) := ((hg (t+1)).mono (𝓕.le (t+1))).measurable
    have hset := stoppingSet_measurable 𝓕 xstar x hx η R T t
    have hbound : ∀ᵐ ω ∂ν, ω ∈ stoppingSet η R T xstar x t → ‖gradient f (x (t+1) ω)‖ ≤ Λ/2 := by
      apply Eventually.of_forall
      intro ω hω
      have ha : active η R T xstar (fun i => x i ω) (t+1) := by simpa only [stoppingSet, if_pos ht, mem_setOf_eq] using hω
      have hz := Radius.gradient_zero_at_minimizer (fun y => (hdiff y).hasGradientAt) xstar hmin
      have hh := hlip (x (t+1) ω) xstar
      rw [hz, sub_zero] at hh
      have hd := mul_le_mul_of_nonneg_left (ha t (by omega)).1 hL.le
      nlinarith only [hh, hd, hguard]
    obtain ⟨hei, hei2, herange, hebias, hesecond, hecenter, hevariance⟩ :=
      stopped_clipping_estimates ν (𝓕 t) (𝓕.le t) Λ p σ hΛ hp hp2 hσ _ _ hgs hμ
        (stoppingSet η R T xstar x t) hset hbound (hpm t ht) (hmean t ht) (hmoment t ht)
    dsimp only [stopError]
    refine ⟨hei, hei2, ?_, ?_, ?_, hecenter, ?_⟩
    · exact herange.mono (fun ω hω => by linarith)
    · filter_upwards [hebias] with ω hω
      have hb := mul_le_mul_of_nonneg_right (bias_factor_bound Λ p hΛ hp2) (Real.rpow_nonneg hσ p)
      unfold biasBudget
      nlinarith only [hω, hb]
    · filter_upwards [hesecond] with ω hω
      have hv := mul_le_mul_of_nonneg_right (second_factor_bound Λ p hΛ hp) (Real.rpow_nonneg hσ p)
      unfold varianceBudget
      nlinarith only [hω, hv]
    · filter_upwards [hevariance, hesecond] with ω hvω hsω
      have hv := mul_le_mul_of_nonneg_right (second_factor_bound Λ p hΛ hp) (Real.rpow_nonneg hσ p)
      unfold varianceBudget
      nlinarith only [hvω, hsω, hv]
  · have he : stopError f η R Λ T xstar x g t=0 := by funext ω; simp [stopError, stoppingSet, ht]
    rw [he]
    constructor
    · exact integrable_zero _ _ _
    · simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact integrable_zero _ _ _
    · exact Eventually.of_forall (fun ω => by simp only [Pi.zero_apply, norm_zero]; positivity)
    · simpa [condExp_const (𝓕.le t)] using hB
    · have hz : (fun ω : Ω => ‖(0 : Ω → E) ω‖^2)=(fun _ => (0 : ℝ)) := by funext ω; simp
      rw [hz, condExp_const (𝓕.le t)]
      exact Eventually.of_forall (fun _ => hV)
    · simp only [condExp_zero, Pi.zero_apply, sub_zero, norm_zero]
      exact Eventually.of_forall (fun ω => by positivity)
    · simp only [condExp_zero, Pi.zero_apply, sub_zero, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [condExp_const (𝓕.le t)]
      exact Eventually.of_forall (fun _ => hV)


lemma stopError_measurable (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (η R Λ : ℝ) (T : ℕ) (xstar : E) (x g : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (hg : Adapted 𝓕 g) (t : ℕ) :
    StronglyMeasurable[𝓕 (t+1)] (stopError f η R Λ T xstar x g t) := by
  have hμ := (gradient_continuous L hL hlip).comp_stronglyMeasurable (hx t)
  have hraw := (((measurable_clip Λ).comp (hg (t+1)).measurable).stronglyMeasurable).sub
    (hμ.mono (𝓕.mono (by omega)))
  exact hraw.indicator (𝓕.mono (by omega) _ (stoppingSet_measurable 𝓕 xstar x hx η R T t))

lemma centered_measurable (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (η R Λ : ℝ) (T : ℕ) (xstar : E) (x g : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (hg : Adapted 𝓕 g) (t : ℕ) :
    StronglyMeasurable[𝓕 (t+1)] (centered ν 𝓕 f η R Λ T xstar x g t) :=
  (stopError_measurable 𝓕 L hL hlip η R Λ T xstar x g hx hg t).sub
    ((stronglyMeasurable_condExp (m := 𝓕 t)).mono (𝓕.mono (by omega)))

lemma centered_integrable (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ)
    (T : ℕ) (xstar : E) (x g : ℕ → Ω → E) (t : ℕ)
    (he : Integrable (stopError f η R Λ T xstar x g t) ν) :
    Integrable (centered ν 𝓕 f η R Λ T xstar x g t) ν := he.sub integrable_condExp

lemma centered_square_integrable (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    (f : E → ℝ) (η R Λ B V : ℝ) (T : ℕ) (xstar : E) (x g : ℕ → Ω → E) (t : ℕ)
    (he : Estimates ν (𝓕 t) (stopError f η R Λ T xstar x g t) Λ B V) :
    Integrable (fun ω => ‖centered ν 𝓕 f η R Λ T xstar x g t ω‖^2) ν := by
  have hL2 := (memLp_two_iff_integrable_sq_norm he.integrable.1).mpr he.square_integrable
  exact (hL2.sub (hL2.condExp (m := 𝓕 t))).integrable_norm_pow (by norm_num)

lemma centered_mean_zero (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    (f : E → ℝ) (η R Λ : ℝ) (T : ℕ) (xstar : E) (x g : ℕ → Ω → E) (t : ℕ)
    (he : Integrable (stopError f η R Λ T xstar x g t) ν) :
    ν[centered ν 𝓕 f η R Λ T xstar x g t|𝓕 t] =ᵐ[ν] 0 :=
  centered_condExp_zero ν (𝓕 t) (𝓕.le t) _ he

def stopRadius (f : E → ℝ) (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → Ω → E) (t : ℕ) : Ω → E :=
  (stoppingSet η R T xstar x t).indicator (fun ω => radiusDirection f η T xstar (fun i => x i ω) (t+1))

def stopDirection (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → Ω → E) (t : ℕ) : Ω → E :=
  (stoppingSet η R T xstar x t).indicator (fun ω => noiseDirection η T xstar (fun i => x i ω) (t+1))

lemma stopRadius_predictable (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (stopRadius f η R T xstar x t) := by
  have hμ := (gradient_continuous L hL hlip).comp_stronglyMeasurable (hx t)
  exact (((hx t).sub stronglyMeasurable_const).sub (hμ.const_smul _)).indicator
    (stoppingSet_measurable 𝓕 xstar x hx η R T t)

lemma stopDirection_predictable (𝓕 : Filtration ℕ m₀) (η R : ℝ) (T : ℕ) (xstar : E)
    (x : ℕ → Ω → E) (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (stopDirection η R T xstar x t) := by
  have hh := (((comparator_predictable 𝓕 xstar x hx (inverseTail (step η T) T) t).sub (hx t)).const_smul
    (tailSum (step η T) T 1*step η T (t+1)*inverseTail (step η T) T t)).indicator
    (stoppingSet_measurable 𝓕 xstar x hx η R T t)
  simpa only [stopDirection, noiseDirection, Nat.add_sub_cancel] using hh

lemma stopRadius_bound {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L η R : ℝ) (hL : 0 < L) (hη : 0 < η) (hR : 0 ≤ R)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖) (hstep : η ≤ 1/(2*L))
    (T : ℕ) (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → Ω → E) (t : ℕ) (ω : Ω) :
    ‖stopRadius f η R T xstar x t ω‖ ≤ 2*R := by
  by_cases hs : ω ∈ stoppingSet η R T xstar x t
  · have ht : t<T := by by_contra h; simpa [stoppingSet,h] using hs
    have ha : active η R T xstar (fun i => x i ω) (t+1) := by simpa [stoppingSet,ht] using hs
    rw [stopRadius, Set.indicator_of_mem hs]
    have hηL : η ≤ 1/L := hstep.trans (by apply one_div_le_one_div_of_le hL; linarith)
    have hh := Radius.gradient_step_nonexpansive hconv (fun y => (hdiff y).hasGradientAt)
      L (step η T (t+1)) hL hlip (step_pos η hη T (t+1) (by omega) (by omega)).le
      ((step_le η hη.le T (t+1) (by omega) (by omega)).trans hηL) xstar hmin (x (t+1) ω)
    exact hh.trans (ha t (by omega)).1
  · simp only [stopRadius, Set.indicator_of_not_mem hs, norm_zero]
    positivity

lemma stopDirection_bound (η R : ℝ) (hη : 0 < η) (hR : 0 ≤ R)
    (T : ℕ) (xstar : E) (x : ℕ → Ω → E) (t : ℕ) (ω : Ω) :
    ‖stopDirection η R T xstar x t ω‖ ≤ 3*R*η := by
  by_cases hs : ω ∈ stoppingSet η R T xstar x t
  · have ht : t<T := by by_contra h; simpa [stoppingSet,h] using hs
    have ha : active η R T xstar (fun i => x i ω) (t+1) := by simpa [stoppingSet,ht] using hs
    rw [stopDirection, Set.indicator_of_mem hs]
    apply noiseDirection_bound η R hη hR T (t+1) (by omega) (by omega) xstar (fun i => x i ω)
    simpa only [Nat.add_sub_cancel] using (ha t (by omega)).2
  · simp only [stopDirection, Set.indicator_of_not_mem hs, norm_zero]
    positivity

def globalDirection (f : E → ℝ) (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → Ω → E) (t : ℕ) : Ω → E :=
  fun ω => (-2*step η T (t+1)) • stopRadius f η R T xstar x t ω

lemma globalDirection_predictable (𝓕 : Filtration ℕ m₀) {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (globalDirection f η R T xstar x t) :=
  (stopRadius_predictable 𝓕 L hL hlip η R T xstar x hx t).const_smul _

lemma globalDirection_bound {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L η R : ℝ) (hL : 0 < L) (hη : 0 < η) (hR : 0 ≤ R)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖) (hstep : η ≤ 1/(2*L))
    (T : ℕ) (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → Ω → E) (t : ℕ) (ω : Ω) :
    ‖globalDirection f η R T xstar x t ω‖ ≤ 4*R*η := by
  by_cases ht : t<T
  · have hs := (step_pos η hη T (t+1) (by omega) (by omega)).le
    have hsl := step_le η hη.le T (t+1) (by omega) (by omega)
    have ha := stopRadius_bound hconv hdiff L η R hL hη hR hlip hstep T xstar hmin x t ω
    rw [globalDirection, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]
    norm_num
    have hh := mul_le_mul hsl ha (norm_nonneg _) hη.le
    nlinarith only [hh]
  · simp only [globalDirection, stopRadius, stoppingSet, if_neg ht, Set.indicator_empty,
      Pi.zero_apply, smul_zero, norm_zero]
    positivity

lemma scalar_increment_properties (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    (f : E → ℝ) (η R Λ B V A : ℝ) (hA0 : 0 ≤ A) (T : ℕ)
    (xstar : E) (x g : ℕ → Ω → E) (t : ℕ)
    (he : Estimates ν (𝓕 t) (stopError f η R Λ T xstar x g t) Λ B V)
    (hu : StronglyMeasurable[𝓕 (t+1)] (centered ν 𝓕 f η R Λ T xstar x g t))
    (a : Ω → E) (ha : StronglyMeasurable[𝓕 t] a) (hA : ∀ ω, ‖a ω‖ ≤ A) :
    StronglyMeasurable[𝓕 (t+1)] (fun ω => ⟪a ω,centered ν 𝓕 f η R Λ T xstar x g t ω⟫_ℝ) ∧
    (ν[fun ω => ⟪a ω,centered ν 𝓕 f η R Λ T xstar x g t ω⟫_ℝ|𝓕 t] =ᵐ[ν] 0) ∧
    (∀ᵐ ω ∂ν, |⟪a ω,centered ν 𝓕 f η R Λ T xstar x g t ω⟫_ℝ| ≤ 2*Λ*A) ∧
    (ν[fun ω => ⟪a ω,centered ν 𝓕 f η R Λ T xstar x g t ω⟫_ℝ^2|𝓕 t] ≤ᵐ[ν] fun _ => A^2*V) := by
  have hui := centered_integrable ν 𝓕 f η R Λ T xstar x g t he.integrable
  have hui2 := centered_square_integrable ν 𝓕 f η R Λ B V T xstar x g t he
  have huma := centered_mean_zero ν 𝓕 f η R Λ T xstar x g t he.integrable
  have hAa : ∀ᵐ ω ∂ν, ‖a ω‖ ≤ A := Eventually.of_forall hA
  refine ⟨((ha.mono (𝓕.mono (by omega))).inner hu), ?_, ?_, ?_⟩
  · exact inner_condExp_zero ν (𝓕 t) (𝓕.le t) _ a hui ha A hAa huma
  · filter_upwards [he.centered_range] with ω hω
    have hh := norm_inner_le_norm (𝕜 := ℝ) (a ω) (centered ν 𝓕 f η R Λ T xstar x g t ω)
    have hm := mul_le_mul (hA ω) hω (norm_nonneg _) hA0
    change ‖a ω‖*‖centered ν 𝓕 f η R Λ T xstar x g t ω‖ ≤ A*(2*Λ) at hm
    rw [Real.norm_eq_abs] at hh
    nlinarith only [hh, hm]
  · exact (conditional_inner_variance ν (𝓕 t) (𝓕.le t) _ a hui hui2 ha A V hA0 hAa he.centered_second).2

end
end ClippedSGD.UpperNoise
