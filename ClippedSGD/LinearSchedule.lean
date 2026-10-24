import ClippedSGD.Potential
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.LinearSchedule
open Potential
noncomputable section

def step (η : ℝ) (T t : ℕ) : ℝ := if t=0 then 0 else η*(T+1-t : ℕ)/T

lemma step_zero (η : ℝ) (T : ℕ) : step η T 0=0 := by simp [step]

lemma step_pos (η : ℝ) (hη : 0 < η) (T t : ℕ) (ht0 : 1 ≤ t) (ht : t ≤ T) :
    0 < step η T t := by
  have hT : 0 < T := by omega
  have hk : 0 < T+1-t := by omega
  simp only [step, if_neg (by omega : t ≠ 0)]
  positivity

lemma step_le (η : ℝ) (hη : 0 ≤ η) (T t : ℕ) (ht0 : 1 ≤ t) (ht : t ≤ T) :
    step η T t ≤ η := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  simp only [step, if_neg (by omega : t ≠ 0)]
  apply (div_le_iff₀ hT).mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show T+1-t ≤ T by omega)) hη

lemma linear_tail_by_length (η : ℝ) (T k : ℕ) (hT : 0 < T) (hk : k ≤ T) :
    tailSum (step η T) T (T+1-k) = η*(k : ℝ)*(k+1 : ℝ)/(2*T) := by
  induction k with
  | zero => simp [tailSum_terminal]
  | succ k ih =>
    have hk' : k ≤ T := by omega
    have ht : T+1-(k+1) ≤ T := by omega
    have hpos : T+1-(k+1) ≠ 0 := by omega
    rw [tailSum_rec _ T _ (step_zero η T) ht]
    have hnext : T+1-(k+1)+1=T+1-k := by omega
    rw [hnext, ih hk']
    simp only [step, if_neg hpos]
    have hlen : T+1-(T+1-(k+1))=k+1 := by omega
    rw [hlen]
    push_cast
    field_simp
    <;> ring

lemma linear_tail (η : ℝ) (T t : ℕ) (hT : 0 < T) (ht0 : 1 ≤ t) (ht : t ≤ T+1) :
    tailSum (step η T) T t = η*(T+1-t : ℕ)*(T+2-t : ℕ)/(2*T) := by
  have hk : T+1-t ≤ T := by omega
  have h := linear_tail_by_length η T (T+1-t) hT hk
  have hidx : T+1-(T+1-t)=t := by omega
  have hlen : T+1-t+1=T+2-t := by omega
  rw [hidx] at h
  convert h using 1
  rw [← hlen]
  push_cast
  ring

lemma initial_tail (η : ℝ) (T : ℕ) (hT : 0 < T) :
    tailSum (step η T) T 1=η*(T+1 : ℝ)/2 := by
  rw [linear_tail η T 1 hT le_rfl (by omega)]
  simp only [Nat.add_sub_cancel]
  have he : T+2-1=T+1 := by omega
  rw [he]
  push_cast
  field_simp
  <;> ring

lemma error_coefficient_exact (η : ℝ) (hη : 0 < η) (T t : ℕ)
    (ht0 : 1 ≤ t) (ht : t ≤ T) :
    2*tailSum (step η T) T 1*(step η T t)^2/tailSum (step η T) T t =
      2*η^2*((T+1 : ℝ)/T)*((T+1-t : ℕ)/(T+2-t : ℕ) : ℝ) := by
  have hT : 0 < T := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hk : (0 : ℝ) < (T+1-t : ℕ) := by exact_mod_cast (show 0 < T+1-t by omega)
  have hk1 : (0 : ℝ) < (T+2-t : ℕ) := by exact_mod_cast (show 0 < T+2-t by omega)
  rw [initial_tail η T hT, linear_tail η T t hT ht0 (by omega)]
  simp only [step, if_neg (by omega : t ≠ 0)]
  field_simp
  <;> ring

lemma error_coefficient_bound (η : ℝ) (hη : 0 < η) (T t : ℕ)
    (ht0 : 1 ≤ t) (ht : t ≤ T) :
    2*tailSum (step η T) T 1*(step η T t)^2/tailSum (step η T) T t ≤ 4*η^2 := by
  rw [error_coefficient_exact η hη T t ht0 ht]
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hrT : (T+1 : ℝ)/T ≤ 2 := (div_le_iff₀ hTr).mpr (by linarith)
  have hk1 : (0 : ℝ) < (T+2-t : ℕ) := by exact_mod_cast (show 0 < T+2-t by omega)
  have hrk : ((T+1-t : ℕ)/(T+2-t : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_one hk1).mpr
    exact_mod_cast (show T+1-t ≤ T+2-t by omega)
  calc
    _ ≤ 2*η^2*2*1 := mul_le_mul
      (mul_le_mul_of_nonneg_left hrT (by positivity)) hrk (by positivity) (by positivity)
    _ = _ := by ring

lemma distance_coefficient_exact (η : ℝ) (hη : 0 < η) (T t : ℕ)
    (ht0 : 2 ≤ t) (ht : t ≤ T) :
    tailSum (step η T) T 1*(step η T t)^2/tailSum (step η T) T (t-1) =
      η^2*((T+1 : ℝ)/T)*((T+1-t : ℕ) : ℝ)^2/
        (((T+2-t : ℕ) : ℝ)*((T+3-t : ℕ) : ℝ)) := by
  have hT : 0 < T := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hk1 : (0 : ℝ) < (T+2-t : ℕ) := by exact_mod_cast (show 0 < T+2-t by omega)
  have hk2 : (0 : ℝ) < (T+3-t : ℕ) := by exact_mod_cast (show 0 < T+3-t by omega)
  rw [initial_tail η T hT, linear_tail η T (t-1) hT (by omega) (by omega)]
  simp only [step, if_neg (by omega : t ≠ 0)]
  rw [show T+1-(t-1)=T+2-t by omega, show T+2-(t-1)=T+3-t by omega]
  field_simp
  <;> ring

lemma distance_coefficient_bound (η : ℝ) (hη : 0 < η) (T t : ℕ)
    (ht0 : 1 ≤ t) (ht : t ≤ T) :
    tailSum (step η T) T 1*(step η T t)^2/tailSum (step η T) T (t-1) ≤ 2*η^2 := by
  have hT : 0 < T := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rcases eq_or_lt_of_le ht0 with ht1 | ht2
  · have hteq : t=1 := ht1.symm
    subst t
    rw [Nat.sub_self, tailSum_zero, initial_tail η T hT]
    have hs : step η T 1=η := by simp [step, hTr.ne']
    rw [hs]
    have he : η*(T+1 : ℝ)/2*η^2/(η*(T+1 : ℝ)/2)=η^2 := by field_simp
    rw [he]
    nlinarith [sq_nonneg η]
  · rw [distance_coefficient_exact η hη T t ht2 ht]
    have hrT : (T+1 : ℝ)/T ≤ 2 := (div_le_iff₀ hTr).mpr (by linarith)
    have hk1 : (0 : ℝ) < (T+2-t : ℕ) := by exact_mod_cast (show 0 < T+2-t by omega)
    have hk2 : (0 : ℝ) < (T+3-t : ℕ) := by exact_mod_cast (show 0 < T+3-t by omega)
    have hk : ((T+1-t : ℕ) : ℝ)^2 ≤ ((T+2-t : ℕ) : ℝ)*((T+3-t : ℕ) : ℝ) := by
      have h1 : ((T+1-t : ℕ) : ℝ) ≤ (T+2-t : ℕ) := by exact_mod_cast (show T+1-t ≤ T+2-t by omega)
      have h2 : ((T+1-t : ℕ) : ℝ) ≤ (T+3-t : ℕ) := by exact_mod_cast (show T+1-t ≤ T+3-t by omega)
      nlinarith [(show (0 : ℝ) ≤ (T+1-t : ℕ) from Nat.cast_nonneg _)]
    apply (div_le_iff₀ (mul_pos hk1 hk2)).mpr
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrT (sq_nonneg η))
      (sq_nonneg (((T+1-t : ℕ) : ℝ)))
    have hh2 := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*η^2 by positivity)
    nlinarith only [hh, hh2]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def noiseDirection (η : ℝ) (T : ℕ) (xstar : E) (x : ℕ → E) (t : ℕ) : E :=
  (tailSum (step η T) T 1*step η T t*inverseTail (step η T) T (t-1)) •
    (comparator xstar x (inverseTail (step η T) T) (t-1)-x t)

/-- The comparator direction has norm at most `3Rη` when the energy at the preceding
state is bounded. -/
theorem noiseDirection_bound (η R : ℝ) (hη : 0 < η) (hR : 0 ≤ R) (T t : ℕ)
    (ht0 : 1 ≤ t) (ht : t ≤ T) (xstar : E) (x : ℕ → E)
    (henergy : tailSum (step η T) T 1*
      distanceEnergy xstar x (inverseTail (step η T) T) (t-1) ≤ 2*R^2) :
    ‖noiseDirection η T xstar x t‖ ≤ 3*R*η := by
  have hT : 0 < T := by omega
  have hs := fun i hi => tailSum_pos (step η T) T i hT hi
    (fun j hj hjT => step_pos η hη T j hj hjT)
  have hs1 := hs 1 (by omega)
  have hsp := hs (t-1) (by omega)
  have hcoef := distance_coefficient_bound η hη T t ht0 ht
  have he0 : 0 ≤ tailSum (step η T) T 1*
      distanceEnergy xstar x (inverseTail (step η T) T) (t-1) := by
    dsimp [distanceEnergy, inverseTail]
    positivity
  have hnormsq : ‖noiseDirection η T xstar x t‖^2 =
      2*(tailSum (step η T) T 1*(step η T t)^2/tailSum (step η T) T (t-1))*
        (tailSum (step η T) T 1*
          distanceEnergy xstar x (inverseTail (step η T) T) (t-1)) := by
    have hidx : t-1+1=t := by omega
    simp only [noiseDirection, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      distanceEnergy, inverseTail, hidx]
    field_simp
    <;> ring
  have hmul := mul_le_mul hcoef henergy he0 (by positivity : 0 ≤ 2*η^2)
  have hfinal : ‖noiseDirection η T xstar x t‖^2 ≤ 8*R^2*η^2 := by
    rw [hnormsq]
    nlinarith only [hmul]
  have hp : 0 ≤ R*η := mul_nonneg hR hη.le
  nlinarith [norm_nonneg (noiseDirection η T xstar x t), sq_nonneg (R*η)]

end
end ClippedSGD.LinearSchedule
