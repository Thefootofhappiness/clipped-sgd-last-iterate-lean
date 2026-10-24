import ClippedSGD.AnytimeLowerTransfer
import ClippedSGD.AnytimeLowerParameters

/-! The time-uniform lower bound for gradient-only rules. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ClippedSGD.AnytimeLower
open AnytimeLowerParameters

variable {S : Type*} [MeasurableSpace S]

/-- For every rule there are a horizon `N` and an instance on which, with probability
greater than `δ`, the gap at `x_{t+1}` exceeds `C t^(-r) (log(et))^m` for some
`1 ≤ t ≤ N`. -/
theorem time_uniform_finite_prefix (σ : Measure S) [IsProbabilityMeasure σ]
    (R : Rule S) (hR : Nonnegative R) (hRm : ∀t,Measurable (R t))
    (p δ C r m : ℝ) (hp : 1<p) (_hp2 : p≤2) (_hδ0 : 0<δ) (hδ : δ<1/2)
    (hC : 0<C) (hm : 0≤m) (hr : beta p<r) :
    ∃(N : ℕ) (μ y : ℝ) (hπ : rareProb p μ≤1), 0<N ∧
      InstanceProperties μ y (rareA p μ) (rareProb p μ) p hπ ∧
      δ<((Lower.iidBits N (rareProb p μ) hπ).prod σ).real
        (failure R μ y (rareA p μ) (fun ω => prefixBits ω.1) Prod.snd (rate C r m) N) := by
  obtain ⟨u,hβu,hur,_⟩ := select_exponent p r hp hr
  obtain ⟨N,μ,hN,hμ,hμhalf,hA,hμA,hπ0,hπ1,hmean,hnorm,hend,hbudget⟩ :=
    exists_log_parameters C m p u δ hC hm hp hδ hβu
  have hD : 0<logCoefficient C m N := logCoefficient_pos C m hC hN
  obtain ⟨y,hP,hfail⟩ := certified_finite_failure σ R hR hRm hμ hμhalf
    (show 0<rareA p μ by linarith) hμA hp hπ0.le hπ1 hmean hnorm.le
    (envelope (logCoefficient C m N) u) hN
    (by intro t _; unfold envelope; positivity) hend hbudget
  refine ⟨N,μ,y,hπ1,hN,hP,hfail.trans_le ?_⟩
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro ω ⟨t,ht,hgap⟩
  refine ⟨t,ht,?_⟩
  exact (log_envelope_dominates_prefix C m r u hC hm hur ht).trans_lt hgap

/-- The time-uniform lower bound: for every gradient-only rule and every exponent
`r > 2(p-1)/(3p-1)`, some i.i.d. instance has failure probability greater than `δ`. -/
theorem time_uniform_obstruction (σ : Measure S) [IsProbabilityMeasure σ]
    (R : Rule S) (hR : Nonnegative R) (hRm : ∀t,Measurable (R t))
    (p δ C r m : ℝ) (hp : 1<p) (hp2 : p≤2) (hδ0 : 0<δ) (hδ : δ<1/2)
    (hC : 0<C) (hm : 0≤m) (hr : 2*(p-1)/(3*p-1)<r) :
    ∃(μ y : ℝ) (hπ : rareProb p μ≤1),
      InstanceProperties μ y (rareA p μ) (rareProb p μ) p hπ ∧
      MeasurableSet (paperFailure R μ y (rareA p μ) C r m) ∧
      δ<((MomentumInfiniteIID.infiniteIID (Lower.bernoulliLaw (rareProb p μ) hπ)).prod σ).real
        (paperFailure R μ y (rareA p μ) C r m) := by
  obtain ⟨N,μ,y,hπ,_,hP,hfail⟩ := time_uniform_finite_prefix σ R hR hRm
    p δ C r m hp hp2 hδ0 hδ hC hm hr
  refine ⟨μ,y,hπ,hP,paperFailure_measurable R hRm μ y _ C r m,?_⟩
  rw [paperFailure_eq]
  exact hfail.trans_le (finite_to_infinite σ R hRm μ y _ _ hπ (rate C r m) N)

end ClippedSGD.AnytimeLower
