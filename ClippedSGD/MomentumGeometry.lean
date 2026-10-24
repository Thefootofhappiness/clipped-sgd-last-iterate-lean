import ClippedSGD.HingeGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Population and sample losses of the momentum instance, on the Euclidean space of
dimension `d + 2`. -/

open Set
open scoped BigOperators InnerProductSpace

namespace ClippedSGD.MomentumGeometry
noncomputable section

section Separable
variable {ι : Type*} [Fintype ι]

def separable (f : ι → ℝ → ℝ) (x : EuclideanSpace ℝ ι) : ℝ := ∑ i, f i (x i)
def coordinateVector (g : ι → ℝ) : EuclideanSpace ℝ ι := (WithLp.equiv 2 _).symm g

omit [Fintype ι] in
lemma coordinateVector_apply (g : ι → ℝ) (i : ι) : coordinateVector g i = g i := rfl

theorem separable_hasGradientAt (f g : ι → ℝ → ℝ)
    (hder : ∀ i x, HasDerivAt (f i) (g i x) x) (x : EuclideanSpace ℝ ι) :
    HasGradientAt (separable f) (coordinateVector (fun i => g i (x i))) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd : HasFDerivAt (separable f)
      (∑ i, g i (x i) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    exact HasFDerivAt.sum (fun i _ =>
      (hder i (x i)).comp_hasFDerivAt x (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt)
  convert hd using 1
  ext y
  simp [InnerProductSpace.toDual_apply, PiLp.inner_apply, coordinateVector,
    real_inner_comm, real_inner_self_eq_norm_sq, mul_comm]

theorem separable_convex (f : ι → ℝ → ℝ)
    (hc : ∀ i, ConvexOn ℝ univ (f i)) : ConvexOn ℝ univ (separable f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [separable, Finset.mul_sum, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (hc i).2 (mem_univ _) (mem_univ _) ha hb hab

theorem separable_grad_lipschitz (g : ι → ℝ → ℝ)
    (hlip : ∀ i x y, |g i x - g i y| ≤ |x - y|)
    (x y : EuclideanSpace ℝ ι) :
    ‖coordinateVector (fun i => g i (x i)) - coordinateVector (fun i => g i (y i))‖ ≤
      ‖x - y‖ := by
  have hs : ‖coordinateVector (fun i => g i (x i)) - coordinateVector (fun i => g i (y i))‖ ^ 2 ≤
      ‖x - y‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    simpa only [PiLp.sub_apply, coordinateVector_apply, Real.norm_eq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (hlip i (x i) (y i)) 2
  nlinarith [norm_nonneg (coordinateVector (fun i => g i (x i)) -
    coordinateVector (fun i => g i (y i))), norm_nonneg (x - y)]

end Separable

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin (d + 2))
abbrev Nuisance (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def scalarLoss (μ b : ℝ) (z : Nuisance d) : Fin (d + 2) → ℝ → ℝ :=
  Fin.cases (HingeGeometry.sampleLoss μ 1 b) (fun i x => x ^ 2 / 2 + z i * x)

def scalarGrad (μ b : ℝ) (z : Nuisance d) : Fin (d + 2) → ℝ → ℝ :=
  Fin.cases (HingeGeometry.sampleGrad μ 1 b) (fun i x => x + z i)

def sampleLoss (μ b : ℝ) (z : Nuisance d) : Space d → ℝ := separable (scalarLoss μ b z)
def sampleGrad (μ b : ℝ) (z : Nuisance d) (x : Space d) : Space d :=
  coordinateVector (fun i => scalarGrad μ b z i (x i))
def populationLoss (μ : ℝ) : Space d → ℝ := sampleLoss μ μ 0
def populationGrad (μ : ℝ) : Space d → Space d := sampleGrad μ μ 0

def minimizer (μ b : ℝ) (z : Nuisance d) : Space d :=
  coordinateVector (Fin.cases (1 - μ + b) (fun i => -z i))

def target (d : ℕ) : Space d := EuclideanSpace.single 0 1

def nuisance (x : Space d) : Nuisance d := coordinateVector (fun i => x i.succ)

lemma scalarLoss_hasDerivAt (μ b : ℝ) (z : Nuisance d) (i : Fin (d + 2)) (x : ℝ) :
    HasDerivAt (scalarLoss μ b z i) (scalarGrad μ b z i x) x := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact HingeGeometry.sampleLoss_hasDerivAt μ 1 b x
  · dsimp [scalarLoss, scalarGrad]
    convert (((hasDerivAt_id x).pow 2).div_const 2).add
      ((hasDerivAt_id x).const_mul (z j)) using 1
    dsimp
    ring

theorem sampleLoss_hasGradientAt (μ b : ℝ) (z : Nuisance d) (x : Space d) :
    HasGradientAt (sampleLoss μ b z) (sampleGrad μ b z x) x :=
  separable_hasGradientAt _ _ (scalarLoss_hasDerivAt μ b z) x

theorem sampleLoss_convex (μ b : ℝ) (z : Nuisance d) :
    ConvexOn ℝ univ (sampleLoss μ b z) := by
  apply separable_convex
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact HingeGeometry.sampleLoss_convex μ 1 b
  · apply Monotone.convexOn_univ_of_deriv
      (fun x => (scalarLoss_hasDerivAt μ b z j.succ x).differentiableAt)
    intro x y hxy
    rw [(scalarLoss_hasDerivAt μ b z j.succ x).deriv,
      (scalarLoss_hasDerivAt μ b z j.succ y).deriv]
    exact add_le_add_right hxy (z j)

theorem sampleGrad_lipschitz (μ b : ℝ) (z : Nuisance d) (x y : Space d) :
    ‖sampleGrad μ b z x - sampleGrad μ b z y‖ ≤ ‖x - y‖ := by
  apply separable_grad_lipschitz
  intro i a c
  refine Fin.cases ?_ (fun j => ?_) i
  · exact HingeGeometry.sampleGrad_lipschitz μ 1 b a c
  · simp [scalarGrad]

theorem sample_minimizer (μ b : ℝ) (hb : 0 ≤ b) (z : Nuisance d) (x : Space d) :
    sampleLoss μ b z (minimizer μ b z) ≤ sampleLoss μ b z x := by
  unfold sampleLoss separable
  apply Finset.sum_le_sum
  intro i _
  refine Fin.cases ?_ (fun j => ?_) i
  · exact HingeGeometry.sample_minimizer μ 1 b hb (x 0)
  · change (-z j) ^ 2 / 2 + z j * (-z j) ≤ (x j.succ) ^ 2 / 2 + z j * x j.succ
    nlinarith [sq_nonneg (x j.succ + z j)]

theorem population_minimizer (μ : ℝ) (hμ : 0 ≤ μ) (x : Space d) :
    populationLoss μ (target d) ≤ populationLoss μ x := by
  have he : minimizer (d := d) μ μ 0 = target d := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [minimizer, target, coordinateVector, EuclideanSpace.single_apply]
  rw [populationLoss, ← he]
  exact sample_minimizer μ μ hμ 0 x

theorem target_norm (d : ℕ) : ‖target d‖ = 1 := by
  simp [target, EuclideanSpace.norm_single]

lemma loss_split (μ b : ℝ) (z : Nuisance d) (x : Space d) :
    sampleLoss μ b z x = HingeGeometry.sampleLoss μ 1 b (x 0) +
      ∑ j : Fin (d + 1), ((x j.succ) ^ 2 / 2 + z j * x j.succ) := by
  exact Fin.sum_univ_succ _

theorem population_gap (μ : ℝ) (x : Space d) :
    populationLoss μ x - populationLoss μ (target d) =
      HingeGeometry.populationLoss μ 1 (x 0) - HingeGeometry.populationLoss μ 1 1 +
      ‖nuisance x‖ ^ 2 / 2 := by
  rw [populationLoss, loss_split, loss_split, PiLp.norm_sq_eq_of_L2]
  simp only [target, EuclideanSpace.single_apply, ite_true, Fin.succ_ne_zero, ite_false,
    PiLp.zero_apply, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div,
    Finset.sum_const_zero, nuisance, coordinateVector_apply, Real.norm_eq_abs,
    sq_abs, HingeGeometry.populationLoss]
  rw [Finset.sum_div]
  ring

theorem nuisance_gap_lower (μ : ℝ) (hμ : 0 ≤ μ) (x : Space d) :
    ‖nuisance x‖ ^ 2 / 2 ≤ populationLoss μ x - populationLoss μ (target d) := by
  rw [population_gap]
  have := HingeGeometry.population_minimizer μ 1 hμ (x 0)
  linarith

theorem gap_before_half (μ : ℝ) (hμ : 0 ≤ μ) (hμhalf : μ ≤ 1/2)
    (x : Space d) (hx : x 0 ≤ 1/2) :
    μ / 4 ≤ populationLoss μ x - populationLoss μ (target d) := by
  rw [population_gap]
  have := HingeGeometry.gap_before_half μ (x 0) hμ hμhalf hx
  linarith [sq_nonneg ‖nuisance x‖]

/-- Embed a nuisance vector without changing its Euclidean norm. -/
def liftNuisance (z : Nuisance d) : Space d := coordinateVector (Fin.cases 0 (fun i => z i))

/-- The additive noise is independent of the query point. -/
theorem sampleGrad_sub_population (μ b : ℝ) (z : Nuisance d) (x : Space d) :
    sampleGrad μ b z x - populationGrad μ x =
      EuclideanSpace.single 0 (μ - b) + liftNuisance z := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [sampleGrad, populationGrad, coordinateVector, scalarGrad, liftNuisance,
      EuclideanSpace.single_apply] using HingeGeometry.centered_noise μ 1 b (x 0)
  · simp [sampleGrad, populationGrad, coordinateVector, scalarGrad, liftNuisance,
      EuclideanSpace.single_apply]

theorem flat_gradient (μ b : ℝ) (z : Nuisance d) (x : Space d)
    (hx : x 0 ≤ 1 - μ) :
    sampleGrad μ b z x =
      coordinateVector (Fin.cases (-b) (fun i => x i.succ + z i)) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact HingeGeometry.sample_flat_gradient μ 1 b (x 0) hx
  · rfl

lemma noise_norm_sq (μ b : ℝ) (z : Nuisance d) :
    ‖EuclideanSpace.single 0 (μ-b) + liftNuisance z‖ ^ 2 = (μ-b)^2 + ‖z‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  simp [EuclideanSpace.single_apply, liftNuisance, coordinateVector]

end
end ClippedSGD.MomentumGeometry
