import ClippedSGD.ContinuousCrossing
import ClippedSGD.AnytimeLowerEvents

/-! The progress budget: if every target in `[μ, 1]` fails with probability at most `δ`,
then `1 - 2δ ≤ 2π ∑_{t<N} (μ + √(2 b t))`. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower
open HingeGeometry
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

theorem progress_budget (ν : Measure Ω) [IsProbabilityMeasure ν]
    (R : Rule S) (hR : Nonnegative R) (hRm : ∀t, Measurable (R t))
    {μ A π δ : ℝ} (hμ : 0≤μ) (hμhalf : μ≤1/2) (hA : 0≤A)
    (bits : Ω → ℕ → Bool) (hbits : Measurable bits)
    (seed : Ω → S) (hseed : Measurable seed) (b : ℕ → ℝ)
    {N : ℕ} (hN : 0<N) (hb : ∀t<N, 0≤b t) (hend : b (N-1)<μ/4)
    (hmass : ∀t<N, ν.real {ω | bits ω t=true}=π)
    (hfail : ∀y, μ≤y → y≤1 → ν.real (failure R μ y A bits seed b N)≤δ) :
    1-2*δ ≤ 2*π*(∑t∈Finset.range N,(μ+Real.sqrt (2*b t))) := by
  let X : ℕ → Ω → ℝ := fun t ω => frozenReference R μ A (bits ω) (seed ω) t
  let tol : ℕ → ℝ := fun t => μ+Real.sqrt (2*b t)
  have hX : ∀t,Measurable (X t) :=
    frozenReference_measurable R hRm μ A bits hbits seed hseed
  have hflat (ω : Ω) : frozenReference R μ A (bits ω) (seed ω)=
      freezePath (position R (referenceOracle A (bits ω)) (seed ω)) (1/2) :=
    frozenReference_eq_flat R hR μ A hμhalf hA (bits ω) (seed ω)
  have hmono (ω : Ω) := reference_monotone hR hA (bits ω) (seed ω)
  have hstill : ∀ω t, t<N → bits ω t=false → X (t+1) ω=X t ω := by
    intro ω t _ ht
    dsimp only [X]
    rw [hflat]
    exact freezePath_no_move _ _ (hmono ω) t (reference_no_arrival R A (bits ω) (seed ω) t ht)
  have hEnd : ν.real {ω | X N ω≤1/2}≤δ := by
    apply (measureReal_mono (s₂ := failure R μ 1 A bits seed b N) ?_).trans
      (hfail 1 (by linarith) le_rfl)
    intro ω hω
    change frozenReference R μ A (bits ω) (seed ω) N≤1/2 at hω
    rw [hflat] at hω
    have horig := (freezePath_le_boundary_iff _ _ (hmono ω) N).mp hω
    refine ⟨N-1,by omega,?_⟩
    simpa only [Nat.sub_add_cancel hN] using endpoint_failure hR hμ hμhalf hA hend
      (bits ω) (seed ω) N horig
  have hBad : ∀z∈Ico 0 (1/2:ℝ), ν.real (badCrossing X tol N z)≤δ := by
    intro z hz
    apply (measureReal_mono (s₂ := failure R μ (z+μ) A bits seed b N) ?_).trans
      (hfail (z+μ) (by linarith [hz.1]) (by linarith [hz.2]))
    rintro ω ⟨t,ht,hbefore,hafter⟩
    change frozenReference R μ A (bits ω) (seed ω) t≤z at hbefore
    change z+tol t<frozenReference R μ A (bits ω) (seed ω) (t+1) at hafter
    rw [hflat] at hbefore hafter
    obtain ⟨he,he'⟩ := freezePath_crossing _ (1/2) z (hmono ω) t hz.2 hbefore
    rw [he] at hbefore
    rw [he'] at hafter
    refine ⟨t,ht,overshoot_failure hR hμ hA (hb t ht) (bits ω) (seed ω) t hbefore ?_⟩
    simpa only [tol,add_assoc] using hafter
  have h := continuous_crossing_budget ν X hX bits hbits tol (1/2) δ π (by norm_num) N
    (by intro t ht; dsimp [tol]; positivity) (fun _ => rfl) hstill hmass hEnd hBad
  dsimp only [tol] at h
  linarith

theorem exists_fixed_target_failure (ν : Measure Ω) [IsProbabilityMeasure ν]
    (R : Rule S) (hR : Nonnegative R) (hRm : ∀t, Measurable (R t))
    {μ A π δ : ℝ} (hμ : 0≤μ) (hμhalf : μ≤1/2) (hA : 0≤A)
    (bits : Ω → ℕ → Bool) (hbits : Measurable bits)
    (seed : Ω → S) (hseed : Measurable seed) (b : ℕ → ℝ)
    {N : ℕ} (hN : 0<N) (hb : ∀t<N, 0≤b t) (hend : b (N-1)<μ/4)
    (hmass : ∀t<N, ν.real {ω | bits ω t=true}=π)
    (hbudget : 2*π*(∑t∈Finset.range N, (μ+Real.sqrt (2*b t)))<1-2*δ) :
    ∃y, μ≤y ∧ y≤1 ∧ δ<ν.real (failure R μ y A bits seed b N) := by
  classical
  by_contra h
  push_neg at h
  have hb' := progress_budget ν R hR hRm hμ hμhalf hA bits hbits seed hseed b
    hN hb hend hmass h
  exact (not_lt_of_ge hb') hbudget

end ClippedSGD.AnytimeLower
