import ClippedSGD.AnytimeLowerInstance

/-! The oracle condition in conditional form for the time-uniform instance: at a query
point that depends on the history, including the seed, the noise of a fresh sample has
conditional mean zero and conditional `p`th absolute moment at most one. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ClippedSGD.AnytimeLower
open HingeGeometry

variable {H : Type*} [MeasurableSpace H]

def freshNoise (μ y A : ℝ) (Q : H → ℝ) (z : H × Bool) : ℝ :=
  sampleGrad μ y (if z.2 then A else 0) (Q z.1)-populationGrad μ y (Q z.1)

lemma freshNoise_eq (μ y A : ℝ) (Q : H → ℝ) (z : H × Bool) :
    freshNoise μ y A Q z=noise μ A z.2 := by
  exact HingeGeometry.centered_noise μ y _ (Q z.1)

lemma freshNoise_integrable (ν : Measure H) [IsProbabilityMeasure ν]
    (μ y A π : ℝ) (hπ1 : π≤1) (Q : H → ℝ) :
    Integrable (freshNoise μ y A Q) (ν.prod (Lower.bernoulliLaw π hπ1)) := by
  change Integrable (fun z => freshNoise μ y A Q z) _
  have hi : Integrable (noise μ A) (Lower.bernoulliLaw π hπ1) := Integrable.of_finite
  have hh := (integrable_const (1:ℝ) (μ:=ν)).mul_prod hi
  simpa only [one_mul,freshNoise_eq] using hh

lemma freshNoise_moment_integrable (ν : Measure H) [IsProbabilityMeasure ν]
    (μ y A π p : ℝ) (hπ1 : π≤1) (Q : H → ℝ) :
    Integrable (fun z => |freshNoise μ y A Q z|^p) (ν.prod (Lower.bernoulliLaw π hπ1)) := by
  have hi : Integrable (fun b => |noise μ A b|^p) (Lower.bernoulliLaw π hπ1) := Integrable.of_finite
  have hh := (integrable_const (1:ℝ) (μ:=ν)).mul_prod hi
  simpa only [one_mul,freshNoise_eq] using hh

/-- Over every history event `E`, the noise at a history-dependent query point `Q`
integrates to zero, and its `p`th absolute moment integrates to at most `ν.real E`. -/
theorem InstanceProperties.fresh_oracle {μ y A π p : ℝ} {hπ1 : π≤1}
    (P : InstanceProperties μ y A π p hπ1)
    (ν : Measure H) [IsProbabilityMeasure ν] (Q : H → ℝ) :
    Integrable (freshNoise μ y A Q) (ν.prod (Lower.bernoulliLaw π hπ1)) ∧
    Integrable (fun z => |freshNoise μ y A Q z|^p) (ν.prod (Lower.bernoulliLaw π hπ1)) ∧
    ∀E : Set H,
      (∫z in E ×ˢ univ, freshNoise μ y A Q z ∂ν.prod (Lower.bernoulliLaw π hπ1))=0 ∧
      (∫z in E ×ˢ univ, |freshNoise μ y A Q z|^p ∂ν.prod (Lower.bernoulliLaw π hπ1))≤ν.real E := by
  refine ⟨freshNoise_integrable ν μ y A π hπ1 Q,
    freshNoise_moment_integrable ν μ y A π p hπ1 Q,?_⟩
  intro E
  simp_rw [freshNoise_eq,Lower.history_event_integral]
  constructor
  · rw [P.centered_noise,mul_zero]
  · calc
      _ = ν.real E*(∫b, |noise μ A b|^p ∂Lower.bernoulliLaw π hπ1) :=
        Lower.history_event_integral ν π hπ1 E (fun b => |noise μ A b|^p)
      _ ≤ ν.real E*1 := mul_le_mul_of_nonneg_left P.central_moment measureReal_nonneg
      _ = ν.real E := mul_one _

end ClippedSGD.AnytimeLower
