import ClippedSGD
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.MetricSpace.Lipschitz

/-! The one-dimensional squared-hinge losses of the lower-bound instances, with their
derivatives, convexity, smoothness, and minimizers. -/

noncomputable section
open Set Filter
open scoped Topology
namespace ClippedSGD.HingeGeometry

def hinge (x : ℝ) : ℝ := (max x 0)^2 / 2

lemma hinge_of_nonpos {x : ℝ} (hx : x ≤ 0) : hinge x = 0 := by
  simp [hinge, max_eq_right hx]

lemma hinge_of_nonneg {x : ℝ} (hx : 0 ≤ x) : hinge x = x^2/2 := by
  simp [hinge, max_eq_left hx]

lemma hinge_continuous : Continuous hinge := by
  exact ((continuous_id.max continuous_const).pow 2).div_const 2

theorem hinge_hasDerivAt (x : ℝ) : HasDerivAt hinge (max x 0) x := by
  refine hasDerivAt_of_hasDerivAt_of_ne' (f := hinge) (g := fun y : ℝ => max y 0)
    (x := (0 : ℝ)) ?_ ?_ ?_ x
  · intro y hy
    change HasDerivAt hinge (max y 0) y
    rcases lt_or_gt_of_ne hy with hn | hp
    · rw [max_eq_right hn.le]
      apply (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hn] with z hz
      exact hinge_of_nonpos hz.le
    · rw [max_eq_left hp.le]
      have hd : HasDerivAt (fun z : ℝ => z^2/2) y y := by
        convert ((hasDerivAt_id y).pow 2).div_const 2 using 1 <;> dsimp <;> ring
      apply hd.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hp] with z hz
      exact hinge_of_nonneg hz.le
  · exact hinge_continuous.continuousAt
  · exact (continuous_id.max continuous_const).continuousAt

lemma positive_part_lipschitz (x y : ℝ) : |max x 0-max y 0| ≤ |x-y| := by
  simpa using abs_max_sub_max_le_max x 0 y 0

def sampleLoss (μ y b x : ℝ) : ℝ := hinge (x-y+μ)-b*x
def sampleGrad (μ y b x : ℝ) : ℝ := max (x-y+μ) 0-b
def populationLoss (μ y x : ℝ) : ℝ := sampleLoss μ y μ x
def populationGrad (μ y x : ℝ) : ℝ := sampleGrad μ y μ x

theorem sampleLoss_hasDerivAt (μ y b x : ℝ) :
    HasDerivAt (sampleLoss μ y b) (sampleGrad μ y b x) x := by
  have hd := (hinge_hasDerivAt (x-y+μ)).comp x
    (((hasDerivAt_id x).sub_const y).add_const μ)
  convert hd.sub ((hasDerivAt_id x).const_mul b) using 1 <;>
    simp [sampleLoss,sampleGrad,Function.comp_def]

theorem sampleLoss_deriv (μ y b x : ℝ) :
    deriv (sampleLoss μ y b) x = sampleGrad μ y b x :=
  (sampleLoss_hasDerivAt μ y b x).deriv

theorem sampleLoss_convex (μ y b : ℝ) : ConvexOn ℝ univ (sampleLoss μ y b) := by
  apply Monotone.convexOn_univ_of_deriv
    (fun x => (sampleLoss_hasDerivAt μ y b x).differentiableAt)
  intro x z hxz
  simp only [sampleLoss_deriv,sampleGrad]
  exact sub_le_sub_right (max_le_max (by linarith) le_rfl) b

theorem sampleGrad_lipschitz (μ y b x z : ℝ) :
    |sampleGrad μ y b x-sampleGrad μ y b z| ≤ |x-z| := by
  have h := positive_part_lipschitz (x-y+μ) (z-y+μ)
  have he : (x-y+μ)-(z-y+μ)=x-z := by ring
  simpa only [sampleGrad,sub_sub_sub_cancel_right,he] using h

lemma sample_gap_nonneg_branch (μ y b x : ℝ) (hb : 0 ≤ b) (hx : y-μ ≤ x) :
    sampleLoss μ y b x-sampleLoss μ y b (y-μ+b) = (x-(y-μ+b))^2/2 := by
  have hxb : 0 ≤ x-y+μ := by linarith
  have he : (y-μ+b)-y+μ=b := by ring
  simp only [sampleLoss,he,hinge_of_nonneg hxb,hinge_of_nonneg hb]
  ring

lemma sample_gap_flat_branch (μ y b x : ℝ) (hb : 0 ≤ b) (hx : x ≤ y-μ) :
    sampleLoss μ y b x-sampleLoss μ y b (y-μ+b) = b*(y-μ-x)+b^2/2 := by
  have hxb : x-y+μ ≤ 0 := by linarith
  have he : (y-μ+b)-y+μ=b := by ring
  simp only [sampleLoss,he,hinge_of_nonpos hxb,hinge_of_nonneg hb]
  ring

theorem sample_minimizer (μ y b : ℝ) (hb : 0 ≤ b) (x : ℝ) :
    sampleLoss μ y b (y-μ+b) ≤ sampleLoss μ y b x := by
  apply sub_nonneg.mp
  by_cases hx : y-μ ≤ x
  · rw [sample_gap_nonneg_branch μ y b x hb hx]
    positivity
  · rw [sample_gap_flat_branch μ y b x hb (le_of_not_ge hx)]
    have hs : 0 ≤ y-μ-x := by linarith
    positivity

theorem sample_attains_minimum (μ y b : ℝ) (hb : 0 ≤ b) :
    ∃ z, ∀ x, sampleLoss μ y b z ≤ sampleLoss μ y b x :=
  ⟨y-μ+b,sample_minimizer μ y b hb⟩

theorem populationLoss_hasDerivAt (μ y x : ℝ) :
    HasDerivAt (populationLoss μ y) (populationGrad μ y x) x :=
  sampleLoss_hasDerivAt μ y μ x

theorem population_minimizer (μ y : ℝ) (hμ : 0 ≤ μ) (x : ℝ) :
    populationLoss μ y y ≤ populationLoss μ y x := by
  simpa [populationLoss] using sample_minimizer μ y μ hμ x

theorem population_gap_quadratic (μ y x : ℝ) (hμ : 0 ≤ μ) (hx : y-μ ≤ x) :
    populationLoss μ y x-populationLoss μ y y=(x-y)^2/2 := by
  simpa [populationLoss] using sample_gap_nonneg_branch μ y μ x hμ hx

theorem population_gap_flat (μ y x : ℝ) (hμ : 0 ≤ μ) (hx : x ≤ y-μ) :
    populationLoss μ y x-populationLoss μ y y=μ*(y-x)-μ^2/2 := by
  have h := sample_gap_flat_branch μ y μ x hμ hx
  simp only [sub_add_cancel,populationLoss] at h ⊢
  linarith

theorem gap_before_half (μ x : ℝ) (hμ : 0 ≤ μ) (hμhalf : μ ≤ 1/2) (hx : x ≤ 1/2) :
    μ/4 ≤ populationLoss μ 1 x-populationLoss μ 1 1 := by
  rw [population_gap_flat μ 1 x hμ (by linarith)]
  nlinarith [mul_nonneg hμ (show 0 ≤ 1/2-x by linarith),
    mul_nonneg hμ (show 0 ≤ 1/2-μ by linarith)]

theorem sample_flat_gradient (μ y b x : ℝ) (hx : x ≤ y-μ) :
    sampleGrad μ y b x = -b := by
  simp [sampleGrad,max_eq_right (show x-y+μ ≤ 0 by linarith)]

theorem centered_noise (μ y b x : ℝ) :
    sampleGrad μ y b x-populationGrad μ y x=μ-b := by
  simp only [sampleGrad,populationGrad]
  ring

end ClippedSGD.HingeGeometry
