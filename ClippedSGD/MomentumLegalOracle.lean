import ClippedSGD.MomentumOracle
import Mathlib.MeasureTheory.Function.L2Space

open Set MeasureTheory
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.MomentumLegalOracle
open MomentumGeometry MomentumProbability MomentumOracle
noncomputable section

lemma loss_additive (μ A B : ℝ) (a : Sample d) (x : Space d) :
    loss μ A B a x = populationLoss μ x + ⟪x, noise μ A B a⟫_ℝ := by
  have hi : ⟪x, noise μ A B a⟫_ℝ =
      (μ-(if a.1 then A else 0))*x 0 + ∑j : Fin (d+1), pulse A B a j*x j.succ := by
    rw [PiLp.inner_apply, Fin.sum_univ_succ]
    simp [noise, liftNuisance, coordinateVector, EuclideanSpace.single_apply,
      RCLike.inner_apply]
  rw [hi, loss, populationLoss, loss_split, loss_split]
  simp only [HingeGeometry.sampleLoss, PiLp.zero_apply, zero_mul, add_zero,
    Finset.sum_add_distrib]
  ring

/-- The population loss is the expectation of the sample loss. -/
theorem population_is_expectation (μ A B π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hm : π*A=μ) (x : Space d) :
    (∫ a : Sample d, loss μ A B a x ∂sampleLaw d π hπ1) = populationLoss μ x := by
  simp_rw [loss_additive]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const,
    integral_inner (Integrable.of_finite), mean_zero μ A B π hπ0 hπ1 hm]
  simp

/-- Properties of the momentum instance: convex, 1-smooth losses attaining their minima,
a minimizer at distance one from the origin, and additive centered noise with `p`th norm
moment at most one. -/
structure LegalInstance (d : ℕ) (μ A B π p : ℝ) (hπ1 : π ≤ 1) : Prop where
  population_expectation : ∀ x : Space d,
    (∫ a : Sample d, loss μ A B a x ∂sampleLaw d π hπ1) = populationLoss μ x
  population_gradient : ∀ x : Space d, HasGradientAt (populationLoss μ) (populationGrad μ x) x
  population_convex : ConvexOn ℝ univ (populationLoss μ : Space d → ℝ)
  population_smooth : ∀ x y : Space d, ‖populationGrad μ x-populationGrad μ y‖ ≤ ‖x-y‖
  population_minimum : ∀ x : Space d, populationLoss μ (target d) ≤ populationLoss μ x
  initial_distance : ‖(0 : Space d)-target d‖ = 1
  sample_gradient : ∀ a (x : Space d), HasGradientAt (loss μ A B a) (grad μ A B a x) x
  sample_convex : ∀ a : Sample d, ConvexOn ℝ univ (loss μ A B a)
  sample_smooth : ∀ a (x y : Space d), ‖grad μ A B a x-grad μ A B a y‖ ≤ ‖x-y‖
  sample_minimum : ∀ a : Sample d, ∃ z : Space d, ∀ x, loss μ A B a z ≤ loss μ A B a x
  additive : ∀ a (x : Space d), grad μ A B a x-populationGrad μ x = noise μ A B a
  centered : (∫ a : Sample d, noise μ A B a ∂sampleLaw d π hπ1) = 0
  moment : (∫ a : Sample d, ‖noise μ A B a‖^p ∂sampleLaw d π hπ1) ≤ 1

theorem fixed_legal_instance (d : ℕ) {μ p : ℝ} (hμ : 0 < μ) (hμsmall : μ ≤ 1/128)
    (hp : 1 < p) (hp2 : p ≤ 2) :
    LegalInstance d μ (rareAmplitude μ p) (1/16) (rareProbability μ p) p
      (rareProbability_le_one hμ hμsmall hp) := by
  have hm := fixed_oracle_moments d hμ hμsmall hp hp2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm.1, hm.2⟩
  · exact population_is_expectation μ _ _ _ (rareProbability_pos hμ).le _ (rare_centering hμ)
  · exact sampleLoss_hasGradientAt μ μ 0
  · exact sampleLoss_convex μ μ 0
  · exact sampleGrad_lipschitz μ μ 0
  · exact population_minimizer μ hμ.le
  · simpa using target_norm d
  · intro a x
    exact sampleLoss_hasGradientAt μ _ _ x
  · intro a
    exact sampleLoss_convex μ _ _
  · intro a x y
    exact sampleGrad_lipschitz μ _ _ x y
  · intro a
    refine ⟨minimizer μ (if a.1 then rareAmplitude μ p else 0) (pulse (rareAmplitude μ p) (1/16) a), ?_⟩
    intro x
    exact sample_minimizer μ _ (by split_ifs; exact (rareAmplitude_pos hμ).le; exact le_rfl) _ x
  · exact additive_noise μ _ _

end
end ClippedSGD.MomentumLegalOracle
