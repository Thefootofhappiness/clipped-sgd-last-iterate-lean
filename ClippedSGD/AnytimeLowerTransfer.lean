import ClippedSGD.AnytimeLowerIID
import ClippedSGD.AnytimeLowerFresh
import ClippedSGD.MomentumParameters

/-! The failure event in the paper's time indexing, and a failure on a finite prefix for
an instance with the required properties. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower

variable {S : Type*} [MeasurableSpace S]

def rate (C r m : ℝ) (t : ℕ) : ℝ :=
  C*((t+1:ℕ):ℝ)^(-r)*(Real.log (Real.exp 1*((t+1:ℕ):ℝ)))^m

/-- The failure event of the paper: `f(x_{t+1}) - f^⋆ > C t^(-r) (log(et))^m` for some
`t ≥ 1`. Here `position R _ _ t` is the paper's `x_{t+1}`. -/
def paperFailure (R : Rule S) (μ y A C r m : ℝ) : Set ((ℕ → Bool) × S) :=
  {ω | ∃t : ℕ, 1≤t ∧ C*(t:ℝ)^(-r)*(Real.log (Real.exp 1*(t:ℝ)))^m <
    HingeGeometry.populationLoss μ y (position R (actualOracle μ y A ω.1) ω.2 t) -
      HingeGeometry.populationLoss μ y y}

lemma paperFailure_eq (R : Rule S) (μ y A C r m : ℝ) :
    paperFailure R μ y A C r m=infiniteFailure R μ y A (rate C r m) := by
  ext ω
  constructor
  · rintro ⟨t,ht,hgap⟩
    refine ⟨t-1,?_⟩
    simpa only [rate,Nat.sub_add_cancel ht] using hgap
  · rintro ⟨t,hgap⟩
    exact ⟨t+1,by omega,hgap⟩

lemma paperFailure_measurable (R : Rule S) (hRm : ∀t,Measurable (R t))
    (μ y A C r m : ℝ) : MeasurableSet (paperFailure R μ y A C r m) := by
  rw [paperFailure_eq]
  exact infiniteFailure_measurable R hRm μ y A _

/-- `finite_iid_failure` combined with `instance_properties`: one target gives an instance
with the required properties that fails with probability greater than `δ`. -/
theorem certified_finite_failure (σ : Measure S) [IsProbabilityMeasure σ]
    (R : Rule S) (hR : Nonnegative R) (hRm : ∀t, Measurable (R t))
    {μ A π p δ : ℝ} (hμ : 0<μ) (hμhalf : μ≤1/2) (hA : 0<A) (hμA : μ≤A)
    (hp : 1<p) (hπ0 : 0≤π) (hπ1 : π≤1) (hmean : π*A=μ)
    (hnorm : 2*μ*A^(p-1)≤1) (b : ℕ → ℝ)
    {N : ℕ} (hN : 0<N) (hb : ∀t<N, 0≤b t) (hend : b (N-1)<μ/4)
    (hbudget : 2*π*(∑t∈Finset.range N, (μ+Real.sqrt (2*b t)))<1-2*δ) :
    ∃y, InstanceProperties μ y A π p hπ1 ∧
      δ<((Lower.iidBits N π hπ1).prod σ).real
        (failure R μ y A (fun ω => prefixBits ω.1) Prod.snd b N) := by
  obtain ⟨y,hy0,hy1,hfail⟩ := finite_iid_failure σ R hR hRm hμ.le hμhalf hA.le hπ0 hπ1
    b hN hb hend hbudget
  exact ⟨y,instance_properties hμ hμhalf hy0 hy1 hA hμA hp hπ0 hπ1 hmean hnorm,hfail⟩

end ClippedSGD.AnytimeLower
