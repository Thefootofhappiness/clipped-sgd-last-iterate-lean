import ClippedSGD.MixedNoise

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.MixedEvents
open UpperNoise UpperConcentration UpperParameters UpperRun
  Potential LinearSchedule FiniteHorizonPathwise Localization MixedNoise
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m₀ : MeasurableSpace Ω}

def shifted (q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t+1 => q t

lemma shifted_adapted (𝓕 : Filtration ℕ m₀) (q : ℕ → Ω → ℝ)
    (hq : ∀ t, StronglyMeasurable[𝓕 (t+1)] (q t)) : Adapted 𝓕 (shifted q) := by
  intro t
  cases t with
  | zero => exact stronglyMeasurable_zero
  | succ t => exact hq t

lemma threshold_comparison (A Λ V ℓ : ℝ) (hA : 0 < A) (hΛ : 0 < Λ) (T : ℕ)
    (hv : (T : ℝ)*V ≤ 2*Λ^2*ℓ) :
    (T : ℝ)*(A^2*V)/(2*Λ*A)+(2*Λ*A)*ℓ ≤ 3*Λ*A*ℓ := by
  have hh := mul_le_mul_of_nonneg_right hv (sq_nonneg A)
  have hd : (T : ℝ)*(A^2*V)/(2*Λ*A) ≤ Λ*A*ℓ := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Λ*A)).mpr
    nlinarith only [hh]
  nlinarith only [hd]

def squareMean (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ)
    (T : ℕ) (xstar : E) (x g : ℕ → Ω → E) (t : ℕ) : Ω → ℝ :=
  ν[fun ω => ‖stopError f η R Λ T xstar x g t ω‖^2|𝓕 t]

def radiusCoefficient (η : ℝ) (T t : ℕ) : ℝ := if t<T then (step η T (t+1))^2 else 0

def potentialCoefficient (η : ℝ) (T t : ℕ) : ℝ :=
  if t<T then 2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1) else 0

def mixedProcess (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ)
    (T : ℕ) (xstar : E) (x g : ℕ → Ω → E) (α : ℕ → ℝ) (a : ℕ → Ω → E) : ℕ → Ω → ℝ :=
  shifted (fun t ω => α t*(‖stopError f η R Λ T xstar x g t ω‖^2-
    squareMean ν 𝓕 f η R Λ T xstar x g t ω)+
      ⟪a t ω,centered ν 𝓕 f η R Λ T xstar x g t ω⟫_ℝ)

lemma radiusCoefficient_bounds (η : ℝ) (hη : 0 < η) (T t : ℕ) :
    0 ≤ radiusCoefficient η T t ∧ radiusCoefficient η T t ≤ η^2 := by
  by_cases ht : t<T
  · have hp := step_pos η hη T (t+1) (by omega) (by omega)
    have hl := step_le η hη.le T (t+1) (by omega) (by omega)
    simp only [radiusCoefficient,if_pos ht]
    exact ⟨sq_nonneg _, (sq_le_sq₀ hp.le hη.le).mpr hl⟩
  · simp [radiusCoefficient,ht,sq_nonneg]

lemma potentialCoefficient_bounds (η : ℝ) (hη : 0 < η) (T t : ℕ) :
    0 ≤ potentialCoefficient η T t ∧ potentialCoefficient η T t ≤ 4*η^2 := by
  by_cases ht : t<T
  · have hp := tailSum_pos (step η T) T (t+1) (by omega) (by omega)
      (fun j hj hjT => step_pos η hη T j hj hjT)
    have h1 := tailSum_pos (step η T) T 1 (by omega) (by omega)
      (fun j hj hjT => step_pos η hη T j hj hjT)
    simp only [potentialCoefficient,if_pos ht]
    exact ⟨by positivity,error_coefficient_bound η hη T (t+1) (by omega) (by omega)⟩
  · simp [potentialCoefficient,ht,sq_nonneg]

/-- A maximal inequality for the mixed martingale of the stopped oracle errors. -/
theorem mixed_tail (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hdiff : Differentiable ℝ f)
    (L R Λ σ p ℓ : ℝ) (hL : 0 < L) (hR : 0 < R) (hΛ : 0 < Λ) (hσ : 0 ≤ σ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hℓ : 1 ≤ ℓ) (hguard : 4*L*R ≤ Λ)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (T : ℕ) (hbudget : (T : ℝ)*varianceBudget Λ σ p ≤ 2*Λ^2*ℓ)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x g : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (hg : Adapted 𝓕 g)
    (hpm : ∀ t < T, Integrable (fun ω => ‖g (t+1) ω-gradient f (x (t+1) ω)‖^p) ν)
    (hmean : ∀ t < T, ν[fun ω => g (t+1) ω-gradient f (x (t+1) ω)|𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t < T, ν[fun ω => ‖g (t+1) ω-gradient f (x (t+1) ω)‖^p|𝓕 t] ≤ᵐ[ν] fun _ => σ^p)
    (α : ℕ → ℝ) (a : ℕ → Ω → E) (αmax A : ℝ) (hαmax : 0 < αmax) (hA : 0 < A)
    (hα : ∀ t, 0 ≤ α t ∧ α t ≤ αmax)
    (ha : ∀ t, StronglyMeasurable[𝓕 t] (a t)) (hab : ∀ t ω, ‖a t ω‖ ≤ A) :
    let η := R/(128*Λ*ℓ)
    ν {ω | ∃ m ≤ T, 7*Λ*(2*Λ*αmax+A)*ℓ <
      partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g α a) m ω} ≤
      ENNReal.ofReal (Real.exp (-ℓ)) := by
  let η := R/(128*Λ*ℓ)
  let V := varianceBudget Λ σ p
  let B := biasBudget Λ σ p
  have hV : 0 ≤ V := by dsimp [V,varianceBudget]; positivity
  have he := stopped_estimates ν 𝓕 hdiff L η R Λ σ p hL hΛ hσ hp hp2 hguard hlip T xstar hmin x g hx hg hpm hmean hmoment
  have heu := centered_measurable ν 𝓕 L hL.le hlip η R Λ T xstar x g hx hg
  have heY := fun t => (stopError_measurable 𝓕 L hL.le hlip η R Λ T xstar x g hx hg t).norm.pow 2
  have heH := fun t => scalar_increment_properties ν 𝓕 f η R Λ B V A hA.le T
    xstar x g t (he t) (heu t) (a t) (ha t) (hab t)
  have hmix := fun t => mixed_increment_properties ν (𝓕 t) (𝓕.le t)
    (fun ω => ‖stopError f η R Λ T xstar x g t ω‖^2)
    (fun ω => ⟪a t ω,centered ν 𝓕 f η R Λ T xstar x g t ω⟫_ℝ)
    ((heY t).mono (𝓕.le _)).measurable ((heH t).1.mono (𝓕.le _)).measurable
    Λ V (α t) αmax A hΛ hV (hα t).1 hαmax (hα t).2 hA
    (by
      filter_upwards [(he t).range_bound] with ω hω
      exact ⟨sq_nonneg _,by nlinarith [norm_nonneg (stopError f η R Λ T xstar x g t ω)]⟩)
    (he t).second_bound (heH t).2.1 (heH t).2.2.1 (heH t).2.2.2
  have hmad : Adapted 𝓕 (mixedProcess ν 𝓕 f η R Λ T xstar x g α a) :=
    shifted_adapted 𝓕 _ (fun t =>
      (((heY t).sub ((stronglyMeasurable_condExp (m := 𝓕 t)).mono (𝓕.mono (by omega)))).const_mul (α t)).add (heH t).1)
  have ht := bounded_martingale_maximal ν 𝓕 _ hmad
    (2*Λ*(2*Λ*αmax+A)) ((2*Λ*αmax+A)^2*V) ℓ (by positivity) (by positivity)
    (fun t => by simpa only [mixedProcess,shifted,squareMean] using
      (hmix t).2.1.mono (fun ω hω => hω.trans_eq (by ring)))
    (fun t => (hmix t).1) (fun t => (hmix t).2.2) T
  have hc := threshold_comparison (2*Λ*αmax+A) Λ V ℓ (by positivity) hΛ T hbudget
  have h7 : 3*Λ*(2*Λ*αmax+A)*ℓ ≤ 7*Λ*(2*Λ*αmax+A)*ℓ := by
    have hℓ0 : 0 ≤ ℓ := by linarith
    nlinarith only [mul_nonneg (mul_nonneg hΛ.le (by positivity : 0 ≤ 2*Λ*αmax+A)) hℓ0]
  exact (measure_mono (by
    rintro ω ⟨m,hm,hh⟩
    exact ⟨m,hm,(hc.trans h7).trans_lt hh⟩)).trans ht


/-- The conditional mean of the stopped square vanishes off the predictable stopping
set. -/
lemma squareMean_zero_outside (ν : Measure Ω) (𝓕 : Filtration ℕ m₀)
    (f : E → ℝ) (η R Λ : ℝ) (T : ℕ) (xstar : E) (x g : ℕ → Ω → E)
    (hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1))) (t : ℕ)
    (hi : Integrable (fun ω => ‖stopError f η R Λ T xstar x g t ω‖^2) ν) :
    ∀ᵐ ω ∂ν, ω ∉ stoppingSet η R T xstar x t →
      squareMean ν 𝓕 f η R Λ T xstar x g t ω=0 := by
  let Y : Ω → ℝ := fun ω => ‖stopError f η R Λ T xstar x g t ω‖^2
  have he : (stoppingSet η R T xstar x t).indicator Y=Y := by
    funext ω
    by_cases hs : ω ∈ stoppingSet η R T xstar x t
    · simp [hs]
    · simp [Y,stopError,hs]
  have hh := condExp_indicator hi (stoppingSet_measurable 𝓕 xstar x hx η R T t)
  change ν[(stoppingSet η R T xstar x t).indicator Y|𝓕 t] =ᵐ[ν]
    (stoppingSet η R T xstar x t).indicator (ν[Y|𝓕 t]) at hh
  rw [he] at hh
  filter_upwards [hh] with ω hω
  intro hs
  simpa only [Set.indicator_of_not_mem hs] using hω

lemma global_mixed_sum_identity (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ)
    (T m : ℕ) (hm : m ≤ T) (xstar : E) (x g : ℕ → Ω → E) (ω : Ω)
    (hz : ∀t<T, ω ∉ stoppingSet η R T xstar x t → squareMean ν 𝓕 f η R Λ T xstar x g t ω=0) :
    partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g (radiusCoefficient η T)
      (globalDirection f η R T xstar x)) m ω=
      ∑t∈Finset.range m, stopped η R T xstar (fun i => x i ω)
        (fun i => (step η T i)^2*(‖Clipping.clip Λ (g i ω)-gradient f (x i ω)‖^2-
            squareMean ν 𝓕 f η R Λ T xstar x g (i-1) ω)-
          2*step η T i*⟪Clipping.clip Λ (g i ω)-gradient f (x i ω)-bias ν 𝓕 f η R Λ T xstar x g (i-1) ω,
          radiusDirection f η T xstar (fun j => x j ω) i⟫_ℝ) (t+1) := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro t ht
  have htT : t<T := by have := Finset.mem_range.mp ht; omega
  by_cases ha : active η R T xstar (fun i => x i ω) (t+1)
  · simp only [mixedProcess,shifted,radiusCoefficient,if_pos htT,globalDirection,stopRadius,
      centered,stopError,stoppingSet,Set.indicator_apply,Set.mem_setOf_eq,if_pos ha,
      stopped,Nat.add_sub_cancel,real_inner_smul_left]
    rw [real_inner_comm]
    ring
  · have hs : ω ∉ stoppingSet η R T xstar x t := by simpa [stoppingSet,htT] using ha
    simp [mixedProcess,shifted,radiusCoefficient,globalDirection,stopRadius,centered,stopError,
      stoppingSet,htT,stopped,ha,hz t htT hs]

lemma local_mixed_sum_identity (ν : Measure Ω) (𝓕 : Filtration ℕ m₀) (f : E → ℝ) (η R Λ : ℝ)
    (T m : ℕ) (hm : m ≤ T) (xstar : E) (x g : ℕ → Ω → E) (ω : Ω)
    (hz : ∀t<T, ω ∉ stoppingSet η R T xstar x t → squareMean ν 𝓕 f η R Λ T xstar x g t ω=0) :
    partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g (potentialCoefficient η T)
      (stopDirection η R T xstar x)) m ω=
      ∑t∈Finset.range m, stopped η R T xstar (fun i => x i ω)
        (fun i => potentialCoefficient η T (i-1)*(‖Clipping.clip Λ (g i ω)-gradient f (x i ω)‖^2-
            squareMean ν 𝓕 f η R Λ T xstar x g (i-1) ω)+
          ⟪Clipping.clip Λ (g i ω)-gradient f (x i ω)-bias ν 𝓕 f η R Λ T xstar x g (i-1) ω,
          noiseDirection η T xstar (fun j => x j ω) i⟫_ℝ) (t+1) := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro t ht
  have htT : t<T := by have := Finset.mem_range.mp ht; omega
  by_cases ha : active η R T xstar (fun i => x i ω) (t+1)
  · simp only [mixedProcess,shifted,stopDirection,centered,stopError,stoppingSet,
      if_pos htT,Set.indicator_apply,Set.mem_setOf_eq,if_pos ha,stopped,Nat.add_sub_cancel]
    rw [real_inner_comm]
  · have hs : ω ∉ stoppingSet η R T xstar x t := by simpa [stoppingSet,htT] using ha
    simp [mixedProcess,shifted,stopDirection,centered,stopError,stoppingSet,htT,stopped,ha,hz t htT hs]

end
end ClippedSGD.MixedEvents
