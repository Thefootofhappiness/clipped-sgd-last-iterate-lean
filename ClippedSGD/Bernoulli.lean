import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real

/-! Bernoulli sample laws for the lower-bound constructions. -/

open Set MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace ClippedSGD.Lower

noncomputable def bernoulliLaw (q : ℝ) (hq : q ≤ 1) : Measure Bool :=
  (PMF.bernoulli (ENNReal.ofReal q) (ENNReal.ofReal_le_one.mpr hq)).toMeasure

instance bernoulliLaw_isProbabilityMeasure (q : ℝ) (hq : q ≤ 1) :
    IsProbabilityMeasure (bernoulliLaw q hq) := by
  unfold bernoulliLaw
  infer_instance

lemma integral_bernoulliLaw {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Bool → ℝ) :
    (∫ b, f b ∂bernoulliLaw q hq1) = (1 - q) * f false + q * f true := by
  unfold bernoulliLaw
  rw [PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply, ENNReal.toReal_sub_of_le
    (ENNReal.ofReal_le_one.mpr hq1) ENNReal.one_ne_top, ENNReal.toReal_ofReal hq0,
    add_comm]

/-- The law of `T` independent Bernoulli samples. -/
noncomputable def iidBits (T : ℕ) (q : ℝ) (hq : q ≤ 1) :
    Measure (Fin T → Bool) := Measure.pi (fun _ => bernoulliLaw q hq)

instance iidBits_isProbabilityMeasure (T : ℕ) (q : ℝ) (hq : q ≤ 1) :
    IsProbabilityMeasure (iidBits T q hq) := by
  unfold iidBits
  infer_instance

section History

variable {H : Type*} [MeasurableSpace H] (ν : Measure H) [IsProbabilityMeasure ν]

/-- The integral of a function of a fresh sample over a history event factors. -/
lemma history_event_integral (q : ℝ) (hq1 : q ≤ 1) (S : Set H) (f : Bool → ℝ) :
    (∫ z in S ×ˢ univ, f z.2 ∂ν.prod (bernoulliLaw q hq1)) =
      ν.real S * (∫ b, f b ∂bernoulliLaw q hq1) := by
  simpa only [one_mul, setIntegral_const, smul_eq_mul, mul_one, Measure.restrict_univ]
    using setIntegral_prod_mul (μ := ν) (ν := bernoulliLaw q hq1)
    (fun _ : H => (1 : ℝ)) f S univ

end History

end ClippedSGD.Lower
