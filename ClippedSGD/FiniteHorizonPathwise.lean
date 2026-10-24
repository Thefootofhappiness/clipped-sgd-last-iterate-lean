import ClippedSGD.LinearSchedule
import ClippedSGD.Radius

open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.FiniteHorizonPathwise
open Potential LinearSchedule
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def energy (η : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (m : ℕ) : ℝ :=
  tailSum (step η T) T 1*distanceEnergy xstar x (inverseTail (step η T) T) m

def objective (f : E → ℝ) (η : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (m : ℕ) : ℝ :=
  tailSum (step η T) T 1*objectivePotential (fun t => f (x t)-f xstar)
    (inverseTail (step η T) T) (step η T) (tailSum (step η T) T) m

lemma energy_nonneg (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 0 < T)
    (xstar : E) (x : ℕ → E) (m : ℕ) (hm : m ≤ T) : 0 ≤ energy η T xstar x m := by
  have hpos := fun i hi => tailSum_pos (step η T) T i hT hi
    (fun j hj hjT => step_pos η hη T j hj hjT)
  have hs := hpos 1 (by omega)
  have hm' := hpos m hm
  dsimp [energy, distanceEnergy, inverseTail]
  positivity

lemma objective_nonneg (f : E → ℝ) (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 0 < T)
    (xstar : E) (hmin : ∀ y, f xstar ≤ f y) (x : ℕ → E) (m : ℕ) (hm : m ≤ T) :
    0 ≤ objective f η T xstar x m := by
  have hsteps := fun j hj hjT => step_pos η hη T j hj hjT
  have hs1 := tailSum_pos (step η T) T 1 hT (by omega) hsteps
  apply mul_nonneg hs1.le
  apply objectivePotential_nonneg _ _ _ _ m (fun t => sub_nonneg.mpr (hmin _))
    (inverseTail_pos _ T m hT hm hsteps).le
  · rcases Nat.eq_zero_or_pos m with rfl | hmp
    · rw [step_zero]
    · exact (hsteps m hmp hm).le
  · exact tailSum_nonneg _ T _ (fun j hj hjT => (hsteps j hj hjT).le)
  · exact fun t ht => inverseTail_mono _ T t hT (by omega) (step_zero η T) hsteps

lemma initial_energy (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 0 < T)
    (xstar : E) (x : ℕ → E) : energy η T xstar x 0=‖x 1-xstar‖^2/2 := by
  have hs := tailSum_pos (step η T) T 1 hT (by omega)
    (fun j hj hjT => step_pos η hη T j hj hjT)
  simp only [energy, distanceEnergy, comparator, inverseTail, tailSum_zero, zero_add,
    norm_sub_rev xstar (x 1)]
  field_simp
  <;> ring

/-- The pathwise potential bound for the linearly decaying step sizes, with the comparator
direction `noiseDirection`. -/
theorem scaled_potential {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L η : ℝ) (hL : 0 < L) (hη : 0 < η)
    (hlip : ∀ u v, ‖gradient f u-gradient f v‖ ≤ L*‖u-v‖)
    (hstep : η ≤ 1/(2*L)) (T m : ℕ) (hT : 0 < T) (hm : m ≤ T)
    (xstar : E) (x e : ℕ → E)
    (hupdate : ∀ t < T, x (t+2)=x (t+1)-step η T (t+1) • (gradient f (x (t+1))+e (t+1))) :
    objective f η T xstar x m+energy η T xstar x m ≤
      ‖x 1-xstar‖^2/2+∑t∈Finset.range m,
        (2*tailSum (step η T) T 1*(step η T (t+1))^2/tailSum (step η T) T (t+1)*‖e (t+1)‖^2+
          ⟪e (t+1),noiseDirection η T xstar x (t+1)⟫_ℝ) := by
  have hsteps := fun j hj hjT => step_pos η hη T j hj hjT
  have hs1 := tailSum_pos (step η T) T 1 hT (by omega) hsteps
  have hh := stepsize_partial_sum_potential hconv hdiff L hL hlip xstar x e (step η T) T m hT hm
    (step_zero η T) hsteps (fun j hj hjT => (step_le η hη.le T j hj hjT).trans hstep) hupdate
  have hh' := mul_le_mul_of_nonneg_left hh hs1.le
  rw [mul_add, mul_add, Finset.mul_sum] at hh'
  have hz := initial_energy η hη T hT xstar x
  change tailSum (step η T) T 1*distanceEnergy xstar x (inverseTail (step η T) T) 0=_ at hz
  rw [hz] at hh'
  change objective f η T xstar x m+energy η T xstar x m ≤ _ at hh'
  convert hh' using 1
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp only [noiseDirection, Nat.add_sub_cancel, real_inner_smul_right, inverseTail]
  ring

lemma terminal_objective (f : E → ℝ) (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 0 < T)
    (xstar : E) (x : ℕ → E) :
    objective f η T xstar x T=η*(T+1 : ℝ)/2*(f (x (T+1))-f xstar) := by
  unfold objective
  rw [stepsize_terminal_output _ _ T hT (step_zero η T)
    (fun j hj hjT => step_pos η hη T j hj hjT), initial_tail η T hT]

def radiusDirection (f : E → ℝ) (η : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (t : ℕ) : E :=
  x t-xstar-step η T t • gradient f (x t)

end
end ClippedSGD.FiniteHorizonPathwise
