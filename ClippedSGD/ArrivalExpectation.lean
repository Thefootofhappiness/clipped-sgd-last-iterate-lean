import ClippedSGD.FrozenReference
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower
variable {Ω : Type*} [MeasurableSpace Ω]

lemma arrival_measurableSet (bits : Ω → ℕ → Bool) (hbits : Measurable bits) (t : ℕ) :
    MeasurableSet {ω | bits ω t=true} :=
  (measurableSet_singleton true).preimage ((measurable_pi_apply t).comp hbits)

lemma arrivals_integrable (ν : Measure Ω) [IsProbabilityMeasure ν]
    (bits : Ω → ℕ → Bool) (hbits : Measurable bits) (w : ℕ → ℝ) (N : ℕ) :
    Integrable (fun ω => ∑t∈Finset.range N, if bits ω t then w t else 0) ν := by
  classical
  apply integrable_finset_sum
  intro t _
  have he : (fun ω => if bits ω t then w t else 0) =
      {ω | bits ω t=true}.indicator (fun _ => w t) := by
    funext ω
    simp [Set.indicator_apply]
  rw [he]
  apply (integrable_const _).indicator
  exact arrival_measurableSet bits hbits t

lemma arrivals_expectation (ν : Measure Ω) [IsProbabilityMeasure ν]
    (bits : Ω → ℕ → Bool) (hbits : Measurable bits) {π : ℝ} (w : ℕ → ℝ) (N : ℕ)
    (hmass : ∀t<N, ν.real {ω | bits ω t=true}=π) :
    (∫ω, ∑t∈Finset.range N, if bits ω t then w t else 0 ∂ν) =
      π*(∑t∈Finset.range N, w t) := by
  classical
  have he (t : ℕ) : (fun ω => if bits ω t then w t else 0) =
      {ω | bits ω t=true}.indicator (fun _ => w t) := by
    funext ω
    simp [Set.indicator_apply]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [he,integral_indicator_const _
      (arrival_measurableSet bits hbits t),
      smul_eq_mul,hmass t (Finset.mem_range.mp ht)]
  · intro t _
    rw [he]
    exact (integrable_const _).indicator
      (arrival_measurableSet bits hbits t)


end ClippedSGD.AnytimeLower
