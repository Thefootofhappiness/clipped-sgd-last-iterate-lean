import ClippedSGD.MomentumRun
import Mathlib.Probability.ProductMeasure

open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.MomentumInfiniteIID
open MomentumGeometry MomentumProbability MomentumRun
noncomputable section

variable {α : Type*} [MeasurableSpace α]

def infiniteIID (ν : Measure α) [IsProbabilityMeasure ν] : Measure (ℕ → α) :=
  Measure.infinitePi (fun _ => ν)

instance (ν : Measure α) [IsProbabilityMeasure ν] : IsProbabilityMeasure (infiniteIID ν) := by
  unfold infiniteIID
  infer_instance

def takePrefix (N : ℕ) (ω : ℕ → α) : Fin N → α := fun i => ω i.val

lemma takePrefix_measurable (N : ℕ) : Measurable (takePrefix (α := α) N) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

lemma takePrefix_preserving (ν : Measure α) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (takePrefix N) (infiniteIID ν) (iid N ν) := by
  let e : (Finset.range N) ≃ Fin N :=
    ⟨(fun i => ⟨i.val, Finset.mem_range.mp i.property⟩),
      (fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩), (by intro i; rfl), (by intro i; rfl)⟩
  have he : takePrefix (α := α) N =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => α) e) ∘ (Finset.range N).restrict := rfl
  refine ⟨takePrefix_measurable N, ?_⟩
  have hre : Measurable ((Finset.range N).restrict : (ℕ → α) → ((Finset.range N) → α)) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  rw [he, ← Measure.map_map (MeasurableEquiv.piCongrLeft (fun _ : Fin N => α) e).measurable hre]
  rw [infiniteIID, Measure.infinitePi_map_restrict]
  exact Measure.pi_map_piCongrLeft e (fun _ => ν)

variable {S : Type*} [MeasurableSpace S]

lemma seedPrefix_preserving (ν : Measure α) [IsProbabilityMeasure ν]
    (σ : Measure S) [IsProbabilityMeasure σ] (N : ℕ) :
    MeasurePreserving (fun q : (ℕ → α) × S => (takePrefix N q.1, q.2))
      ((infiniteIID ν).prod σ) ((iid N ν).prod σ) :=
  (takePrefix_preserving ν N).prod (MeasurePreserving.id σ)

lemma legal_prefix_position (R : Rule (Space d) S) (μ A B : ℝ)
    (ω : ℕ → Sample d) (seed : S) (N t : ℕ) (ht : t ≤ N) :
    position R (legalOracle μ A B (prefixSamples (takePrefix N ω))) seed t =
      position R (legalOracle μ A B ω) seed t := by
  apply congrArg (fun q => q.1) (coupled_trajectory R
    (legalOracle μ A B (prefixSamples (takePrefix N ω))) (legalOracle μ A B ω) seed N ?_ t ht)
  intro i hi
  simp only [legalOracle, prefixSamples_at _ i hi, takePrefix]

end
end ClippedSGD.MomentumInfiniteIID
