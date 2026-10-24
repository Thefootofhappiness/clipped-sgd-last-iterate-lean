import ClippedSGD.MomentumFiniteLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Parameters and elementary inequalities for the momentum lower bound. -/

open Set Filter
open scoped BigOperators Topology
namespace ClippedSGD.MomentumParameters
open MomentumFiniteLower MomentumOracle
noncomputable section

def envelope (D u : ℝ) (t : ℕ) : ℝ := D * (max 1 (t : ℝ)) ^ (-u)
def earlyCutoff (θ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ θ⌋₊
def windowGap (ρ a : ℝ) (j : ℕ) : ℝ := ρ * (3 * (j+1 : ℝ)) ^ (-a)

lemma envelope_antitone (D u : ℝ) (hD : 0 ≤ D) (hu : 0 ≤ u) : Antitone (envelope D u) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left _ hD
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (max_le_max le_rfl (by exact_mod_cast hij)) (neg_nonpos.mpr hu)

lemma envelope_of_pos (D u : ℝ) (t : ℕ) (ht : 0 < t) :
    envelope D u t = D * (t : ℝ) ^ (-u) := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  simp [envelope, max_eq_right ht1]

lemma earlyCutoff_le (θ : ℝ) (hθ : θ ≤ 1) (N : ℕ) (hN : 0 < N) : earlyCutoff θ N ≤ N := by
  apply Nat.floor_le_of_le
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  simpa using Real.rpow_le_rpow_of_exponent_le hn hθ

lemma late_time_lower (θ : ℝ) (N j : ℕ) (hj : earlyCutoff θ N ≤ j) :
    (N : ℝ)^θ < j+1 := by
  have hf : (N : ℝ)^θ < (earlyCutoff θ N : ℝ)+1 := Nat.lt_floor_add_one _
  have hj' : (earlyCutoff θ N : ℝ) ≤ j := by exact_mod_cast hj
  linarith

/-- For `u < r` there is `D > 0` with `C t^(-r) (log(et))^k ≤ D t^(-u)` for all `t ≥ 1`. -/
theorem logarithmic_envelope_dominated (C r u k : ℝ) (hC : 0 < C)
    (hru : u < r) (hk : 0 ≤ k) :
    ∃ D > 0, ∀ t : ℝ, 1 ≤ t →
      C * t^(-r) * (Real.log (Real.exp 1 * t))^k ≤ D * t^(-u) := by
  let ε := (r-u)/(k+1)
  let M := 1+1/ε
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hM : 0 < M := by dsimp [M]; positivity
  have hεk : ε*k ≤ r-u := by
    dsimp [ε]
    apply (div_mul_eq_mul_div _ _ _).trans_le
    apply (div_le_iff₀ (by linarith : 0 < k+1)).mpr
    nlinarith
  refine ⟨C*M^k, mul_pos hC (Real.rpow_pos_of_pos hM k), ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hp : 1 ≤ t^ε := Real.one_le_rpow ht hε.le
  have helog : Real.log (Real.exp 1*t) = 1+Real.log t := by
    rw [Real.log_mul (Real.exp_pos _).ne' ht0.ne', Real.log_exp]
  have hlog : Real.log t ≤ t^ε/ε := by
    apply (le_div_iff₀ hε).mpr
    have he := Real.add_one_le_exp (Real.log t * ε)
    rw [← Real.rpow_def_of_pos ht0] at he
    linarith
  have hlog0 : 0 ≤ 1+Real.log t := by linarith [Real.log_nonneg ht]
  have hlogM : 1+Real.log t ≤ M*t^ε := by
    dsimp [M]
    have hεinv : 0 ≤ 1/ε := by positivity
    rw [div_eq_mul_inv] at hlog
    simp only [one_div]
    nlinarith [hlog]
  calc
    _ = C*t^(-r)*(1+Real.log t)^k := by rw [helog]
    _ ≤ C*t^(-r)*(M*t^ε)^k :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog0 hlogM hk) (by positivity)
    _ = C*M^k*t^(-r+ε*k) := by
      rw [Real.mul_rpow hM.le (Real.rpow_nonneg ht0.le ε),
        ← Real.rpow_mul ht0.le, Real.rpow_add ht0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) (by positivity)

def qExponent (p : ℝ) : ℝ := p/(p-1)
def probabilityConstant (D p : ℝ) : ℝ :=
  (128 : ℝ)^(1/(p-1)) * (8*D)^(qExponent p)

lemma qExponent_eq (p : ℝ) (hp : 1 < p) : qExponent p = 1+1/(p-1) := by
  unfold qExponent
  have hp0 : p-1 ≠ 0 := by linarith
  field_simp

lemma rareProbability_power {μ p : ℝ} (hμ : 0 < μ) (hp : 1 < p) :
    rareProbability μ p = (128 : ℝ)^(1/(p-1)) * μ^(qExponent p) := by
  have hk : (0 : ℝ) < (128 : ℝ)^(1/(p-1)) := Real.rpow_pos_of_pos (by norm_num) _
  have hm : (0 : ℝ) < μ^(1/(p-1)) := Real.rpow_pos_of_pos hμ _
  unfold rareProbability rareAmplitude
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1/128) hμ.le,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 128),
    Real.one_rpow, qExponent_eq p hp, Real.rpow_add hμ, Real.rpow_one]
  field_simp
  ring

lemma rareProbability_horizon (D p u : ℝ) (hD : 0 < D) (hp : 1 < p)
    (N : ℕ) (hN : 0 < N) :
    rareProbability (8*D*(N : ℝ)^(-u)) p =
      probabilityConstant D p * (N : ℝ)^(-u*qExponent p) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [rareProbability_power (by positivity) hp,
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ 8*D) (Real.rpow_nonneg hn.le (-u)),
    ← Real.rpow_mul hn.le]
  unfold probabilityConstant
  ring

lemma envelope_sqrt (D u : ℝ) (hD : 0 ≤ D) (j : ℕ) :
    Real.sqrt (2*envelope D u (j+1)) = Real.sqrt (2*D)*(j+1 : ℝ)^(-u/2) := by
  have hj : (0 : ℝ) < j+1 := by positivity
  rw [envelope_of_pos D u (j+1) (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hj.le]
  congr 1
  ring

lemma gain_horizon_bound (H h : ℝ) (hH : 0 ≤ H) (hh : 0 ≤ h)
    (N : ℕ) (hN : 0 < N) :
    H*(N+1 : ℝ)^h ≤ H*(2 : ℝ)^h*(N : ℝ)^h := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ N)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith) hh) hH

end
end ClippedSGD.MomentumParameters
