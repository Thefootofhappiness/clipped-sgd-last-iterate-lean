import ClippedSGD.AnytimeLowerRule
import Mathlib.Order.Interval.Finset.Fin

/-! The failure event on a finite prefix of a run. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower
open HingeGeometry

variable {S Ω : Type*}

def failure (R : Rule S) (μ y A : ℝ) (bits : Ω → ℕ → Bool)
    (seed : Ω → S) (b : ℕ → ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃t<N, b t < populationLoss μ y
    (position R (actualOracle μ y A (bits ω)) (seed ω) (t+1)) - populationLoss μ y y}

lemma failure_measurable [MeasurableSpace Ω] [MeasurableSpace S]
    (R : Rule S) (hR : ∀t, Measurable (R t)) (μ y A : ℝ)
    (bits : Ω → ℕ → Bool) (hbits : Measurable bits)
    (seed : Ω → S) (hseed : Measurable seed) (b : ℕ → ℝ) (N : ℕ) :
    MeasurableSet (failure R μ y A bits seed b N) := by
  have he : failure R μ y A bits seed b N =
      ⋃ t : ℕ, ⋃ (_ : t<N), {ω | b t < populationLoss μ y
        (position R (actualOracle μ y A (bits ω)) (seed ω) (t+1)) - populationLoss μ y y} := by
    ext ω
    simp [failure]
  rw [he]
  apply MeasurableSet.iUnion
  intro t
  apply MeasurableSet.iUnion
  intro _
  apply measurableSet_lt measurable_const
  exact ((populationLoss_continuous μ y).measurable.comp
    (position_measurable R hR _ (actualOracle_measurable μ y A bits hbits) seed hseed (t+1))).sub_const _

end ClippedSGD.AnytimeLower
