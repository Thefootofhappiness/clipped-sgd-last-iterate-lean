import ClippedSGD.MixedLocalization

/-! The known-horizon last-iterate bound for Algorithm 1. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators InnerProductSpace ENNReal
namespace ClippedSGD.KnownHorizonMain
open Clipping UpperNoise UpperConcentration UpperParameters UpperRun Potential LinearSchedule FiniteHorizonPathwise Localization MixedEvents MixedLocalization
noncomputable section
variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m₀ : MeasurableSpace Ω}

/-- Algorithm 1 with its horizon- and confidence-dependent parameters. -/
def run (x₁ : E) (L R σ p δ : ℝ) (T : ℕ) (g : ℕ → Ω → E) : ℕ → Ω → E :=
  let ℓ := Real.log (6/δ)
  let Λ := threshold L R σ p ℓ T
  iterate x₁ (R/(128*Λ*ℓ)) Λ T g

/-- The known-horizon bound, with the oracle condition stated for the centered noise
`g (t+1) - gradient f (x (t+1))`. -/
theorem known_horizon_upper_centered (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L R σ p δ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (T : ℕ) (hT : 0 < T) (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (hinitial : ‖x₁-xstar‖ ≤ R) (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t < T, Integrable (fun ω => ‖g (t+1) ω-gradient f (run x₁ L R σ p δ T g (t+1) ω)‖^p) ν)
    (hmean : ∀ t < T, ν[fun ω => g (t+1) ω-gradient f (run x₁ L R σ p δ T g (t+1) ω)|𝓕 t] =ᵐ[ν] 0)
    (hmoment : ∀ t < T, ν[fun ω => ‖g (t+1) ω-gradient f (run x₁ L R σ p δ T g (t+1) ω)‖^p|𝓕 t] ≤ᵐ[ν] fun _ => σ^p) :
    ENNReal.ofReal (1-δ) ≤ ν {ω |
      f (run x₁ L R σ p δ T g (T+1) ω)-f xstar ≤
        min (1024*L*R^2*Real.log (6/δ)/T+256*σ*R*(Real.log (6/δ)/T)^((p-1)/p)) (13*L*R^2/20) ∧
      ∀ t, 1 ≤ t → t ≤ T+1 → ‖run x₁ L R σ p δ T g t ω-xstar‖^2 < 13/10*R^2} := by
  let ℓ := Real.log (6/δ)
  let Λ := threshold L R σ p ℓ T
  let η := R/(128*Λ*ℓ)
  let x := run x₁ L R σ p δ T g
  let B := biasBudget Λ σ p
  have hℓ : 1 ≤ ℓ := (confidence_log δ hδ hδ1).1
  have hℓ0 : 0 < ℓ := by linarith
  have hΛ : 0 < Λ := threshold_pos L R σ p ℓ hL hR T
  have hη : 0 < η := (scale_budgets R Λ ℓ hR hΛ hℓ).1
  have hguard : 4*L*R ≤ Λ := le_max_left _ _
  have hstep : η ≤ 1/(2*L) := step_valid L R σ p ℓ hL hR hℓ T
  have hbud := clipping_budgets L R σ p ℓ hL hR hσ (by linarith) hℓ0 T hT
  have hx : ∀ t, StronglyMeasurable[𝓕 t] (x (t+1)) :=
    iterate_adapted 𝓕 x₁ η Λ T g (fun t => (hg t).measurable)
  have he := stopped_estimates ν 𝓕 hdiff L η R Λ σ p hL hΛ hσ hp.le hp2 hguard hlip T xstar hmin x g hx hg hpm hmean hmoment
  have hbAll : ∀ᵐ ω ∂ν, ∀ t, ‖bias ν 𝓕 f η R Λ T xstar x g t ω‖ ≤ B :=
    ae_all_iff.mpr (fun t => (he t).bias_bound)
  let V := varianceBudget Λ σ p
  have hmAll : ∀ᵐ ω ∂ν, ∀ t, squareMean ν 𝓕 f η R Λ T xstar x g t ω ≤ V :=
    ae_all_iff.mpr (fun t => (he t).second_bound)
  have hzAll : ∀ᵐ ω ∂ν, ∀ t, ω ∉ stoppingSet η R T xstar x t →
      squareMean ν 𝓕 f η R Λ T xstar x g t ω=0 :=
    ae_all_iff.mpr (fun t => squareMean_zero_outside ν 𝓕 f η R Λ T xstar x g hx t (he t).square_integrable)
  have hg' := mixed_tail ν 𝓕 hdiff L R Λ σ p ℓ hL hR hΛ hσ hp.le hp2 hℓ hguard hlip
    T hbud.2.2.2 xstar hmin x g hx hg hpm hmean hmoment
    (radiusCoefficient η T) (globalDirection f η R T xstar x) (η^2) (4*R*η)
    (by positivity) (by positivity) (radiusCoefficient_bounds η hη T)
    (globalDirection_predictable 𝓕 L hL.le hlip η R T xstar x hx)
    (globalDirection_bound hconv hdiff L η R hL hη hR.le hlip hstep T xstar hmin x)
  have hh := mixed_tail ν 𝓕 hdiff L R Λ σ p ℓ hL hR hΛ hσ hp.le hp2 hℓ hguard hlip
    T hbud.2.2.2 xstar hmin x g hx hg hpm hmean hmoment
    (potentialCoefficient η T) (stopDirection η R T xstar x) (4*η^2) (3*R*η)
    (by positivity) (by positivity) (potentialCoefficient_bounds η hη T)
    (stopDirection_predictable 𝓕 η R T xstar x hx)
    (stopDirection_bound η R hη hR.le T xstar x)
  let G := {ω | ∃ m ≤ T, 7*Λ*(2*Λ*η^2+4*R*η)*ℓ <
    partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g (radiusCoefficient η T)
      (globalDirection f η R T xstar x)) m ω}
  let H := {ω | ∃ m ≤ T, 7*Λ*(8*Λ*η^2+3*R*η)*ℓ <
    partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g (potentialCoefficient η T)
      (stopDirection η R T xstar x)) m ω}
  let bad := G ∪ H
  have hbad : ν bad ≤ ENNReal.ofReal δ := by
    have hh' : ν H ≤ ENNReal.ofReal (Real.exp (-ℓ)) := by
      have he : 2*Λ*(4*η^2)=8*Λ*η^2 := by ring
      simpa only [H,he] using hh
    have hunion : ν bad ≤ ν G+ν H := measure_union_le G H
    have hsum := add_le_add hg' hh'
    have heq : ENNReal.ofReal (Real.exp (-ℓ))+ENNReal.ofReal (Real.exp (-ℓ))=
        ENNReal.ofReal (2*Real.exp (-ℓ)) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1
      ring
    rw [heq] at hsum
    have hprob : 2*Real.exp (-ℓ) ≤ δ := by
      have hp := (confidence_log δ hδ hδ1).2
      change 3*Real.exp (-ℓ) ≤ δ at hp
      linarith [Real.exp_nonneg (-ℓ)]
    exact (hunion.trans hsum).trans (ENNReal.ofReal_le_ofReal hprob)
  have hgood : ENNReal.ofReal (1-δ) ≤ ν badᶜ := by
    rw [ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
    apply tsub_le_iff_right.mpr
    have hh : (1 : ℝ≥0∞) ≤ ν bad+ν badᶜ := by
      simpa only [union_compl_self, measure_univ] using (measure_union_le bad badᶜ : ν (bad∪badᶜ) ≤ ν bad+ν badᶜ)
    exact hh.trans ((add_le_add_right hbad (ν badᶜ)).trans_eq (add_comm _ _))
  apply hgood.trans
  apply measure_mono_ae
  filter_upwards [hbAll,hmAll,hzAll] with ω hbω hmω hzω
  intro hω
  have hG : ∀ m ≤ T, partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g
      (radiusCoefficient η T) (globalDirection f η R T xstar x)) m ω ≤
      7*Λ*(2*Λ*η^2+4*R*η)*ℓ := by
    intro m hm
    exact le_of_not_gt (fun h => hω (Or.inl ⟨m,hm,h⟩))
  have hH : ∀ m ≤ T, partialSum (mixedProcess ν 𝓕 f η R Λ T xstar x g
      (potentialCoefficient η T) (stopDirection η R T xstar x)) m ω ≤
      7*Λ*(8*Λ*η^2+3*R*η)*ℓ := by
    intro m hm
    exact le_of_not_gt (fun h => hω (Or.inr ⟨m,hm,h⟩))
  let e : ℕ → E := fun i => clip Λ (g i ω)-gradient f (x i ω)
  let b : ℕ → E := fun i => bias ν 𝓕 f η R Λ T xstar x g (i-1) ω
  have hinit : ‖x 1 ω-xstar‖ ≤ R := hinitial
  have hupdate : ∀ t < T, x (t+2) ω=x (t+1) ω-step η T (t+1) • (gradient f (x (t+1) ω)+e (t+1)) :=
    fun t _ => iterate_inexact f x₁ η Λ T g t ω
  let M : ℕ → ℝ := fun i => squareMean ν 𝓕 f η R Λ T xstar x g (i-1) ω
  have hgsum : ∀ m ≤ T, (∑t∈Finset.range m, stopped η R T xstar (fun i => x i ω)
      (fun i => (step η T i)^2*(‖e i‖^2-M i)-
        2*step η T i*⟪e i-b i,radiusDirection f η T xstar (fun j => x j ω) i⟫_ℝ) (t+1)) ≤
      7*Λ*(2*Λ*η^2+4*R*η)*ℓ := by
    intro m hm
    simpa only [global_mixed_sum_identity ν 𝓕 f η R Λ T m hm xstar x g ω
      (fun t _ => hzω t)] using hG m hm
  have hhsum : ∀ m ≤ T, (∑t∈Finset.range m, stopped η R T xstar (fun i => x i ω)
      (fun i => potentialCoefficient η T (i-1)*(‖e i‖^2-M i)+
        ⟪e i-b i,noiseDirection η T xstar (fun j => x j ω) i⟫_ℝ) (t+1)) ≤
      7*Λ*(8*Λ*η^2+3*R*η)*ℓ := by
    intro m hm
    simpa only [local_mixed_sum_identity ν 𝓕 f η R Λ T m hm xstar x g ω
      (fun t _ => hzω t)] using hH m hm
  have hclosed := closure_from_mixed_events hconv hdiff L R Λ ℓ B V hL hR hΛ hℓ
    hbud.1 hbud.2.1 hlip hstep T hT hbud.2.2.1 hbud.2.2.2
    xstar hmin (fun i => x i ω) e b M hinit hupdate
    (fun t _ _ => by simpa only [b, Nat.add_sub_cancel] using hbω t)
    (fun t _ => by simpa only [M,Nat.add_sub_cancel] using hmω t) hgsum hhsum
  have hterminal := hclosed T le_rfl
  refine ⟨terminal_rate_of_localized hdiff L R σ p ℓ hL hR hσ (by linarith) hℓ hlip T hT xstar hmin
    (fun i => x i ω) hterminal.2 hterminal.1, ?_⟩
  intro t ht htT
  have hidx : t-1+1=t := by omega
  simpa only [hidx] using (hclosed (t-1) (by omega)).1

/-- The known-horizon bound: with probability at least `1 - δ`, the last iterate satisfies
the rate bound, and every iterate satisfies `‖x t - xstar‖² < 13 R²/10`. -/
theorem known_horizon_upper (ν : Measure Ω) [IsProbabilityMeasure ν] (𝓕 : Filtration ℕ m₀)
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L R σ p δ : ℝ) (hL : 0 < L) (hR : 0 < R) (hσ : 0 ≤ σ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlip : ∀ y z, ‖gradient f y-gradient f z‖ ≤ L*‖y-z‖)
    (T : ℕ) (hT : 0 < T) (x₁ xstar : E) (hmin : ∀ y, f xstar ≤ f y)
    (hinitial : ‖x₁-xstar‖ ≤ R) (g : ℕ → Ω → E) (hg : Adapted 𝓕 g)
    (hpm : ∀ t < T, Integrable (fun ω => ‖g (t+1) ω-gradient f (run x₁ L R σ p δ T g (t+1) ω)‖^p) ν)
    (hmean : ∀ t < T, ν[g (t+1)|𝓕 t] =ᵐ[ν] fun ω => gradient f (run x₁ L R σ p δ T g (t+1) ω))
    (hmoment : ∀ t < T, ν[fun ω => ‖g (t+1) ω-gradient f (run x₁ L R σ p δ T g (t+1) ω)‖^p|𝓕 t] ≤ᵐ[ν] fun _ => σ^p) :
    ENNReal.ofReal (1-δ) ≤ ν {ω |
      f (run x₁ L R σ p δ T g (T+1) ω)-f xstar ≤
        min (1024*L*R^2*Real.log (6/δ)/T+256*σ*R*(Real.log (6/δ)/T)^((p-1)/p)) (13*L*R^2/20) ∧
      ∀ t, 1 ≤ t → t ≤ T+1 → ‖run x₁ L R σ p δ T g t ω-xstar‖^2 < 13/10*R^2} := by
  apply known_horizon_upper_centered ν 𝓕 hconv hdiff L R σ p δ hL hR hσ hp hp2 hδ hδ1
    hlip T hT x₁ xstar hmin hinitial g hg hpm _ hmoment
  intro t ht
  let ℓ := Real.log (6/δ)
  let Λ := threshold L R σ p ℓ T
  let η := R/(128*Λ*ℓ)
  have hℓ : 1 ≤ ℓ := (confidence_log δ hδ hδ1).1
  have hΛ : 0 < Λ := threshold_pos L R σ p ℓ hL hR T
  have hη : 0 < η := (scale_budgets R Λ ℓ hR hΛ hℓ).1
  have hμ := gradient_predictable L hL.le hlip 𝓕 x₁ η Λ T g (fun i => (hg i).measurable) t
  have hμi := iterate_gradient_integrable ν 𝓕 hdiff L η R Λ hL hη hΛ.le hlip T x₁ xstar hmin
    hinitial g hg t ht.le
  exact raw_unbiased_to_centered ν (𝓕 t) (𝓕.le t) (g (t+1))
    (fun ω => gradient f (run x₁ L R σ p δ T g (t+1) ω))
    (((hg (t+1)).mono (𝓕.le (t+1))).measurable) hμ hμi p hp.le (hpm t ht) (hmean t ht)

end
end ClippedSGD.KnownHorizonMain
