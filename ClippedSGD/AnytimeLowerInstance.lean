import ClippedSGD.AnytimeLowerRule
import ClippedSGD.Bernoulli

/-! Properties of the instance of the time-uniform lower bound under the Bernoulli sample
law: convex, 1-smooth losses attaining their minima, and additive centered noise with
`p`th absolute moment at most one. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ClippedSGD.AnytimeLower
open HingeGeometry

def sampleFunction (μ y A : ℝ) (b : Bool) : ℝ → ℝ :=
  sampleLoss μ y (if b then A else 0)

def noise (μ A : ℝ) (b : Bool) : ℝ := μ-(if b then A else 0)

lemma noise_additive (μ y A x : ℝ) (b : Bool) :
    sampleGrad μ y (if b then A else 0) x = populationGrad μ y x+noise μ A b := by
  have hh := centered_noise μ y (if b then A else 0) x
  dsimp [noise]
  linarith

lemma expected_sampleFunction {μ A π : ℝ} (hπ0 : 0≤π) (hπ1 : π≤1)
    (hmean : π*A=μ) (y x : ℝ) :
    (∫b, sampleFunction μ y A b x ∂Lower.bernoulliLaw π hπ1)=populationLoss μ y x := by
  rw [Lower.integral_bernoulliLaw hπ0 hπ1]
  simp only [sampleFunction,Bool.false_eq_true,if_false,if_true,sampleLoss,populationLoss]
  rw [←hmean]
  ring

lemma expected_sampleGrad {μ A π : ℝ} (hπ0 : 0≤π) (hπ1 : π≤1)
    (hmean : π*A=μ) (y x : ℝ) :
    (∫b, sampleGrad μ y (if b then A else 0) x ∂Lower.bernoulliLaw π hπ1)=populationGrad μ y x := by
  rw [Lower.integral_bernoulliLaw hπ0 hπ1]
  simp only [Bool.false_eq_true,if_false,if_true,sampleGrad,populationGrad]
  nlinarith [hmean]

lemma noise_mean {μ A π : ℝ} (hπ0 : 0≤π) (hπ1 : π≤1) (hmean : π*A=μ) :
    (∫b, noise μ A b ∂Lower.bernoulliLaw π hπ1)=0 := by
  rw [Lower.integral_bernoulliLaw hπ0 hπ1]
  simp only [noise,Bool.false_eq_true,if_false,if_true]
  nlinarith [hmean]

/-- Under the normalization `2 μ A^(p-1) ≤ 1`, the `p`th absolute moment of the noise is
at most one. -/
theorem noise_moment {μ A π p : ℝ} (hμ : 0<μ) (hA : 0<A) (hμA : μ≤A)
    (hp : 1<p) (hπ0 : 0≤π) (hπ1 : π≤1) (hmean : π*A=μ)
    (hnorm : 2*μ*A^(p-1)≤1) :
    (∫b, |noise μ A b|^p ∂Lower.bernoulliLaw π hπ1)≤1 := by
  rw [Lower.integral_bernoulliLaw hπ0 hπ1]
  have hfalse : |noise μ A false|=μ := by simp [noise,abs_of_pos hμ]
  have htrue : |noise μ A true|=A-μ := by
    simp only [noise,if_true]
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [hfalse,htrue]
  have htail : (A-μ)^p≤A^p := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have hpowμ : μ^p=μ*μ^(p-1) := by
    have he : p=1+(p-1) := by ring
    conv_lhs => rw [he]
    rw [Real.rpow_add hμ,Real.rpow_one]
  have hpowA : A^p=A*A^(p-1) := by
    have he : p=1+(p-1) := by ring
    conv_lhs => rw [he]
    rw [Real.rpow_add hA,Real.rpow_one]
  have hμpow : μ^p≤μ*A^(p-1) := by
    rw [hpowμ]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hμ.le hμA (by linarith)) hμ.le
  have hπpow : π*A^p=μ*A^(p-1) := by rw [hpowA,←mul_assoc,hmean]
  have hfirst : (1-π)*μ^p≤μ^p := by
    have hn := Real.rpow_nonneg hμ.le p
    nlinarith
  have hsecond := mul_le_mul_of_nonneg_left htail hπ0
  nlinarith

structure InstanceProperties (μ y A π p : ℝ) (hπ1 : π≤1) : Prop where
  mu_positive : 0<μ
  mu_half : μ≤1/2
  target_lower : μ≤y
  target_upper : y≤1
  probability_nonnegative : 0≤π
  population_derivative : ∀x, HasDerivAt (populationLoss μ y) (populationGrad μ y x) x
  population_convex : ConvexOn ℝ univ (populationLoss μ y)
  population_smooth : ∀x z, |populationGrad μ y x-populationGrad μ y z|≤|x-z|
  population_minimum : ∀x, populationLoss μ y y≤populationLoss μ y x
  initial_distance : |y-(0:ℝ)|≤1
  sample_derivative : ∀b x, HasDerivAt (sampleFunction μ y A b)
    (sampleGrad μ y (if b then A else 0) x) x
  sample_convex : ∀b, ConvexOn ℝ univ (sampleFunction μ y A b)
  sample_smooth : ∀(b : Bool) x z, |sampleGrad μ y (if b then A else 0) x-
    sampleGrad μ y (if b then A else 0) z|≤|x-z|
  sample_minimum : ∀b, ∃v, ∀x, sampleFunction μ y A b v≤sampleFunction μ y A b x
  mean_loss : ∀x, (∫b, sampleFunction μ y A b x ∂Lower.bernoulliLaw π hπ1)=populationLoss μ y x
  mean_gradient : ∀x, (∫b, sampleGrad μ y (if b then A else 0) x
    ∂Lower.bernoulliLaw π hπ1)=populationGrad μ y x
  additive_noise : ∀b x, sampleGrad μ y (if b then A else 0) x=populationGrad μ y x+noise μ A b
  centered_noise : (∫b, noise μ A b ∂Lower.bernoulliLaw π hπ1)=0
  central_moment : (∫b, |noise μ A b|^p ∂Lower.bernoulliLaw π hπ1)≤1

theorem instance_properties {μ y A π p : ℝ} (hμ : 0<μ) (hμhalf : μ≤1/2)
    (hy0 : μ≤y) (hy1 : y≤1) (hA : 0<A) (hμA : μ≤A)
    (hp : 1<p) (hπ0 : 0≤π) (hπ1 : π≤1) (hmean : π*A=μ)
    (hnorm : 2*μ*A^(p-1)≤1) : InstanceProperties μ y A π p hπ1 := by
  refine ⟨hμ,hμhalf,hy0,hy1,hπ0,populationLoss_hasDerivAt μ y,
    sampleLoss_convex μ y μ,sampleGrad_lipschitz μ y μ,
    population_minimizer μ y hμ.le,?_,?_,?_,?_,?_,
    expected_sampleFunction hπ0 hπ1 hmean y,expected_sampleGrad hπ0 hπ1 hmean y,
    (fun b x => noise_additive μ y A x b),noise_mean hπ0 hπ1 hmean,
    noise_moment hμ hA hμA hp hπ0 hπ1 hmean hnorm⟩
  · rw [sub_zero,abs_of_nonneg (by linarith)]
    exact hy1
  · intro b x
    exact sampleLoss_hasDerivAt μ y _ x
  · intro b
    exact sampleLoss_convex μ y _
  · intro b x z
    exact sampleGrad_lipschitz μ y _ x z
  · intro b
    exact sample_attains_minimum μ y _ (by split_ifs <;> positivity)

end ClippedSGD.AnytimeLower
