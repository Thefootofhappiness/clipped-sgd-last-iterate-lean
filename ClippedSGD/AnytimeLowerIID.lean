import ClippedSGD.ContinuousLower
import ClippedSGD.MomentumInfiniteIID

/-! The product law of the samples and the seed, and the transfer of a failure on a
finite prefix to the infinite i.i.d. run on the same instance. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower

variable {S : Type*} [MeasurableSpace S]

def prefixBits {N : ℕ} (b : Fin N → Bool) (t : ℕ) : Bool :=
  if ht : t<N then b ⟨t,ht⟩ else false

lemma prefixBits_at {N : ℕ} (b : Fin N → Bool) (t : ℕ) (ht : t<N) :
    prefixBits b t=b ⟨t,ht⟩ := by simp [prefixBits,ht]

lemma prefixBits_measurable (N : ℕ) : Measurable (prefixBits (N:=N)) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t<N
  · simpa only [prefixBits, dif_pos ht] using measurable_pi_apply (⟨t,ht⟩:Fin N)
  · simp only [prefixBits,dif_neg ht]
    exact measurable_const

lemma bernoulli_true_mass {π : ℝ} (hπ0 : 0≤π) (hπ1 : π≤1) :
    (Lower.bernoulliLaw π hπ1).real {true}=π := by
  simp [Lower.bernoulliLaw,measureReal_def,PMF.toMeasure_apply_singleton,
    PMF.bernoulli_apply,ENNReal.toReal_ofReal hπ0]

lemma finite_bit_mass (σ : Measure S) [IsProbabilityMeasure σ]
    {N : ℕ} {π : ℝ} (hπ0 : 0≤π) (hπ1 : π≤1) (t : ℕ) (ht : t<N) :
    ((Lower.iidBits N π hπ1).prod σ).real
      {ω : (Fin N → Bool) × S | prefixBits ω.1 t=true}=π := by
  have he : {ω : (Fin N → Bool) × S | prefixBits ω.1 t=true} =
      {ω : Fin N → Bool | ω ⟨t,ht⟩=true} ×ˢ univ := by
    ext ω
    simp [prefixBits_at _ _ ht]
  rw [he,measureReal_prod_prod,measureReal_univ_eq_one,mul_one]
  change (MomentumProbability.iid N (Lower.bernoulliLaw π hπ1)
    {ω | ω ⟨t,ht⟩ ∈ ({true}:Set Bool)}).toReal=π
  rw [MomentumProbability.cylinder]
  exact bernoulli_true_mass hπ0 hπ1

/-- Some target `y ∈ [μ, 1]` fails within `N` steps with probability greater than `δ`. -/
theorem finite_iid_failure (σ : Measure S) [IsProbabilityMeasure σ]
    (R : Rule S) (hR : Nonnegative R) (hRm : ∀t, Measurable (R t))
    {μ A π δ : ℝ} (hμ : 0≤μ) (hμhalf : μ≤1/2) (hA : 0≤A)
    (hπ0 : 0≤π) (hπ1 : π≤1) (b : ℕ → ℝ)
    {N : ℕ} (hN : 0<N) (hb : ∀t<N, 0≤b t) (hend : b (N-1)<μ/4)
    (hbudget : 2*π*(∑t∈Finset.range N, (μ+Real.sqrt (2*b t)))<1-2*δ) :
    ∃y, μ≤y ∧ y≤1 ∧ δ<((Lower.iidBits N π hπ1).prod σ).real
      (failure R μ y A (fun ω => prefixBits ω.1) Prod.snd b N) :=
  exists_fixed_target_failure _ R hR hRm hμ hμhalf hA _
    ((prefixBits_measurable N).comp measurable_fst) _ measurable_snd b hN hb hend
    (finite_bit_mass σ hπ0 hπ1) hbudget

lemma actual_prefix_position (R : Rule S) (μ y A : ℝ)
    (ω : ℕ → Bool) (seed : S) (N t : ℕ) (ht : t≤N) :
    position R (actualOracle μ y A (prefixBits (MomentumInfiniteIID.takePrefix N ω))) seed t =
      position R (actualOracle μ y A ω) seed t := by
  apply congrArg Prod.fst (MomentumRun.coupled_trajectory (asMomentum R)
    (actualOracle μ y A (prefixBits (MomentumInfiniteIID.takePrefix N ω)))
    (actualOracle μ y A ω) seed N ?_ t ht)
  intro j hj
  simp only [actualOracle,prefixBits_at _ j hj,MomentumInfiniteIID.takePrefix]

def infiniteFailure (R : Rule S) (μ y A : ℝ) (b : ℕ → ℝ) : Set ((ℕ → Bool) × S) :=
  {ω | ∃t : ℕ, b t < HingeGeometry.populationLoss μ y
    (position R (actualOracle μ y A ω.1) ω.2 (t+1)) - HingeGeometry.populationLoss μ y y}

lemma infiniteFailure_measurable (R : Rule S) (hRm : ∀t, Measurable (R t))
    (μ y A : ℝ) (b : ℕ → ℝ) : MeasurableSet (infiniteFailure R μ y A b) := by
  have he : infiniteFailure R μ y A b =
      ⋃N : ℕ, failure R μ y A Prod.fst Prod.snd b N := by
    ext ω
    simp only [infiniteFailure,failure,mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t+1,t,by omega,ht⟩
    · rintro ⟨N,t,_,ht⟩
      exact ⟨t,ht⟩
  rw [he]
  exact MeasurableSet.iUnion (fun N => failure_measurable R hRm μ y A _ measurable_fst
    _ measurable_snd b N)

/-- The probability of a failure within the first `N` steps is at most that of a failure
of the infinite run. -/
theorem finite_to_infinite (σ : Measure S) [IsProbabilityMeasure σ]
    (R : Rule S) (hRm : ∀t, Measurable (R t))
    (μ y A π : ℝ) (hπ1 : π≤1) (b : ℕ → ℝ) (N : ℕ) :
    ((Lower.iidBits N π hπ1).prod σ).real
      (failure R μ y A (fun ω => prefixBits ω.1) Prod.snd b N) ≤
    ((MomentumInfiniteIID.infiniteIID (Lower.bernoulliLaw π hπ1)).prod σ).real
      (infiniteFailure R μ y A b) := by
  let P := fun ω : (ℕ → Bool) × S => (MomentumInfiniteIID.takePrefix N ω.1,ω.2)
  let E := failure R μ y A (fun ω : (Fin N → Bool) × S => prefixBits ω.1) Prod.snd b N
  have hE : MeasurableSet E := failure_measurable R hRm μ y A _
    ((prefixBits_measurable N).comp measurable_fst) _ measurable_snd b N
  have hp := MomentumInfiniteIID.seedPrefix_preserving (Lower.bernoulliLaw π hπ1) σ N
  have he : ((MomentumInfiniteIID.infiniteIID (Lower.bernoulliLaw π hπ1)).prod σ).real
      (P ⁻¹' E) = ((Lower.iidBits N π hπ1).prod σ).real E := by
    exact congrArg ENNReal.toReal (hp.measure_preimage hE.nullMeasurableSet)
  rw [←he]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨t,ht,hgap⟩ := hω
  refine ⟨t,?_⟩
  dsimp only [P] at hgap
  simpa only [actual_prefix_position R μ y A ω.1 ω.2 N (t+1) (by omega)] using hgap

end ClippedSGD.AnytimeLower
