import ClippedSGD.UpperParameters
import Mathlib.Probability.Process.Adapted

open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.UpperRun
open Clipping Potential LinearSchedule FiniteHorizonPathwise Localization UpperParameters
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m₀ : MeasurableSpace Ω}

/-- The iterates of Algorithm 1 (clipped updates without projection). Index `t` is the
paper's `x_t`; index `0` repeats `x_1`. -/
def iterate (x₁ : E) (η Λ : ℝ) (T : ℕ) (g : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => fun _ => x₁
  | 1 => fun _ => x₁
  | t+2 => fun ω => iterate x₁ η Λ T g (t+1) ω-step η T (t+1) • clip Λ (g (t+1) ω)

lemma iterate_adapted (𝓕 : Filtration ℕ m₀) (x₁ : E) (η Λ : ℝ) (T : ℕ) (g : ℕ → Ω → E)
    (hg : ∀ t, @Measurable Ω E (𝓕 t) _ (g t)) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (iterate x₁ η Λ T g (t+1)) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    change StronglyMeasurable[𝓕 (t+1)] (fun ω =>
      iterate x₁ η Λ T g (t+1) ω-step η T (t+1) • clip Λ (g (t+1) ω))
    exact (ih.mono (𝓕.mono (by omega))).sub
      (((measurable_clip Λ).comp (hg (t+1))).stronglyMeasurable.const_smul _)

lemma gradient_continuous {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) : Continuous (gradient f) := by
  have hh : LipschitzWith ⟨L,hL⟩ (gradient f) := LipschitzWith.of_dist_le_mul (by
    intro x y
    simpa only [dist_eq_norm, NNReal.coe_mk] using hlip x y)
  exact hh.continuous

lemma gradient_predictable {f : E → ℝ} (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (𝓕 : Filtration ℕ m₀) (x₁ : E) (η Λ : ℝ) (T : ℕ) (g : ℕ → Ω → E)
    (hg : ∀ t, @Measurable Ω E (𝓕 t) _ (g t)) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (fun ω => gradient f (iterate x₁ η Λ T g (t+1) ω)) :=
  (gradient_continuous L hL hlip).comp_stronglyMeasurable (iterate_adapted 𝓕 x₁ η Λ T g hg t)

lemma comparator_predictable (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (w : ℕ → ℝ) (t : ℕ) :
    StronglyMeasurable[𝓕 t] (fun ω => comparator xstar (fun i => x i ω) w t) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    change StronglyMeasurable[𝓕 (t+1)] (fun ω => (1-w t/w (t+1)) • x (t+1) ω+
      (w t/w (t+1)) • comparator xstar (fun i => x i ω) w t)
    exact ((hx t).mono (𝓕.mono (by omega))).const_smul _ |>.add
      ((ih.mono (𝓕.mono (by omega))).const_smul _)

lemma energy_predictable (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (η : ℝ) (T t : ℕ) :
    StronglyMeasurable[𝓕 t] (fun ω => energy η T xstar (fun i => x i ω) t) := by
  exact ((((comparator_predictable 𝓕 xstar x hx (inverseTail (step η T) T) t).sub
    (hx t)).norm.pow 2).const_mul _).const_mul _

lemma active_measurable (𝓕 : Filtration ℕ m₀) (xstar : E) (x : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (η R : ℝ) (T t : ℕ) :
    MeasurableSet[𝓕 t] {ω | active η R T xstar (fun i => x i ω) (t+1)} := by
  simp only [active, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  apply MeasurableSet.inter
  · exact measurableSet_le (((hx j).mono (𝓕.mono (by omega))).sub stronglyMeasurable_const).norm.measurable measurable_const
  · exact measurableSet_le ((energy_predictable 𝓕 xstar x hx η T j).mono (𝓕.mono (by omega))).measurable measurable_const

lemma iterate_inexact (f : E → ℝ) (x₁ : E) (η Λ : ℝ) (T : ℕ) (g : ℕ → Ω → E) (t : ℕ) (ω : Ω) :
    iterate x₁ η Λ T g (t+2) ω=iterate x₁ η Λ T g (t+1) ω-
      step η T (t+1) • (gradient f (iterate x₁ η Λ T g (t+1) ω)+
        (clip Λ (g (t+1) ω)-gradient f (iterate x₁ η Λ T g (t+1) ω))) := by
  simp only [iterate, add_sub_cancel]

lemma iterate_radius_bound (x₁ xstar : E) (η R Λ : ℝ) (hη : 0 < η) (hΛ : 0 ≤ Λ)
    (T : ℕ) (g : ℕ → Ω → E) (hinit : ‖x₁-xstar‖ ≤ R) (t : ℕ) (ht : t ≤ T) (ω : Ω) :
    ‖iterate x₁ η Λ T g (t+1) ω-xstar‖ ≤ R+t*η*Λ := by
  induction t with
  | zero => simpa [iterate] using hinit
  | succ t ih =>
    have hp := ih (by omega)
    have hs := step_pos η hη T (t+1) (by omega) (by omega)
    have hsle := step_le η hη.le T (t+1) (by omega) (by omega)
    have hn := norm_sub_le (iterate x₁ η Λ T g (t+1) ω-xstar) (step η T (t+1) • clip Λ (g (t+1) ω))
    have heq : iterate x₁ η Λ T g (t+2) ω-xstar=
        (iterate x₁ η Λ T g (t+1) ω-xstar)-step η T (t+1) • clip Λ (g (t+1) ω) := by
      rw [iterate]; abel_nf; simp only [add_assoc]
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hn
    have hmul := mul_le_mul hsle (norm_clip Λ hΛ (g (t+1) ω)) (norm_nonneg _) hη.le
    push_cast
    nlinarith only [hn,hp,hmul]

lemma iterate_gradient_integrable (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hdiff : Differentiable ℝ f) (L η R Λ : ℝ) (hL : 0 < L) (hη : 0 < η) (hΛ : 0 ≤ Λ)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (T : ℕ) (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y) (hinit : ‖x₁-xstar‖ ≤ R)
    (g : ℕ → Ω → E) (hg : Adapted 𝓕 g) (t : ℕ) (ht : t ≤ T) :
    Integrable (fun ω => gradient f (iterate x₁ η Λ T g (t+1) ω)) ν := by
  have hm := gradient_predictable L hL.le hlip 𝓕 x₁ η Λ T g (fun i => (hg i).measurable) t
  apply Integrable.mono' (integrable_const (L*(R+t*η*Λ))) ((hm.mono (𝓕.le t)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  have hz := Radius.gradient_zero_at_minimizer (fun y => (hdiff y).hasGradientAt) xstar hmin
  have hh := hlip (iterate x₁ η Λ T g (t+1) ω) xstar
  rw [hz,sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (iterate_radius_bound x₁ xstar η R Λ hη hΛ T g hinit t ht ω) hL.le)

lemma raw_unbiased_to_centered (ν : Measure Ω) [IsProbabilityMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (g μ : Ω → E)
    (hg : @Measurable Ω E m₀ _ g) (hμ : StronglyMeasurable[m] μ) (hμi : Integrable μ ν)
    (p : ℝ) (hp : 1 ≤ p) (hpm : Integrable (fun ω => ‖g ω-μ ω‖^p) ν)
    (hmean : ν[g|m] =ᵐ[ν] μ) : ν[fun ω => g ω-μ ω|m] =ᵐ[ν] 0 := by
  letI : MeasurableSpace Ω := m₀
  have hn : Integrable (fun ω => g ω-μ ω) ν := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hpm)
      (hg.aestronglyMeasurable.sub (hμ.mono hm).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => norm_le_one_add_rpow _ p (norm_nonneg _) hp)
  have hgi : Integrable g ν := by
    convert hn.add hμi using 1
    funext ω
    simp
  have hs := condExp_sub hgi hμi m
  rw [condExp_of_stronglyMeasurable hm hμ hμi] at hs
  filter_upwards [hs,hmean] with ω hsω hmω
  change ν[fun ω => g ω-μ ω|m] ω=ν[g|m] ω-μ ω at hsω
  simpa only [hmω,sub_self,Pi.zero_apply] using hsω

end
end ClippedSGD.UpperRun
