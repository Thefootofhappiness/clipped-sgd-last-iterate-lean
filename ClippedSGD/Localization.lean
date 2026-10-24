import ClippedSGD.FiniteHorizonPathwise

open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.Localization
open Potential LinearSchedule FiniteHorizonPathwise
noncomputable section

lemma scale_budgets (R Λ ℓ : ℝ) (hR : 0 < R) (hΛ : 0 < Λ) (hℓ : 1 ≤ ℓ) :
    let η := R/(128*Λ*ℓ)
    0 < η ∧ η*Λ*ℓ=R/128 ∧ η^2*(8*Λ^2*ℓ) ≤ R^2/2048 := by
  have hl : 0 < ℓ := by linarith
  dsimp only
  refine ⟨by positivity, ?_, ?_⟩
  · field_simp
    <;> ring
  · have hh : R^2/(2048*ℓ) ≤ R^2/2048 := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num : (0 : ℝ)<2048)
      nlinarith
    convert hh using 1
    field_simp
    <;> ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The localization condition at time `t`, which involves only the states before
time `t`. -/
def active (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (t : ℕ) : Prop :=
  ∀ j < t, ‖x (j+1)-xstar‖ ≤ 2*R ∧ energy η T xstar x j ≤ 2*R^2

instance active_decidable (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (t : ℕ) :
    Decidable (active η R T xstar x t) := Classical.propDecidable _

def stopped {F : Type*} [Zero F] (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (v : ℕ → F) (t : ℕ) : F :=
  if active η R T xstar x t then v t else 0

lemma stopped_prefix_eq {F : Type*} [Zero F] (η R : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E)
    (v : ℕ → F) (m : ℕ) (ha : active η R T xstar x m) (t : ℕ) (ht : t ≤ m) :
    stopped η R T xstar x v t=v t := by
  apply if_pos
  exact fun j hj => ha j (by omega)

end
end ClippedSGD.Localization
