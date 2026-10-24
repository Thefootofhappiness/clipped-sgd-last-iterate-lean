import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Asymptotics of power sums at the exponent threshold of the momentum lower bound. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ClippedSGD.MomentumAsymptotics

lemma shifted_power_summable {s r : ℝ} (h : 1-s<r) :
    Summable (fun j : ℕ => ((j+1:ℕ):ℝ)^(-s-r)) := by
  have hh : Summable (fun j : ℕ => (j:ℝ)^(-s-r)) := Real.summable_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff 1).mpr hh

lemma weighted_power_sum_bound {s r : ℝ} (hr : 0≤r) (hs : 1-s<r)
    (N : ℕ) (hN : 0<N) :
    (∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-s))≤
      (N:ℝ)^r*(∑'j : ℕ,((j+1:ℕ):ℝ)^(-s-r)) := by
  have hsum := shifted_power_summable hs
  calc
    _ = ∑j∈Finset.range N,((j+1:ℕ):ℝ)^r*((j+1:ℕ):ℝ)^(-s-r) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [←Real.rpow_add (by positivity)]
      congr 1
      ring
    _ ≤ ∑j∈Finset.range N,(N:ℝ)^r*((j+1:ℕ):ℝ)^(-s-r) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply Real.rpow_le_rpow (by positivity) _ hr
      exact_mod_cast (show j+1≤N from Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    _ = (N:ℝ)^r*(∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-s-r)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum (Finset.range N) (fun j _=>Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `N^(-b) ∑_{j<N} (j+1)^(-s) → 0` when `b > 0` and `b > 1 - s`. -/
theorem weighted_power_sum_tendsto {s b : ℝ} (hb : 0<b) (hs : 1-s<b) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-b)*(∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-s)))
      atTop (𝓝 0) := by
  let r := (max 0 (1-s)+b)/2
  have hmax : max 0 (1-s)<b := max_lt hb hs
  have hr : 0≤r := by dsimp [r];linarith [le_max_left (0:ℝ) (1-s)]
  have hrs : 1-s<r := by dsimp [r];linarith [le_max_right (0:ℝ) (1-s)]
  have hrb : r<b := by dsimp [r];linarith
  let C := ∑'j : ℕ,((j+1:ℕ):ℝ)^(-s-r)
  have ht : Tendsto (fun N : ℕ => (N:ℝ)^(r-b)*C) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show 0<b-r by linarith)).comp
      tendsto_natCast_atTop_atTop
    have he : -(b-r)=r-b := by ring
    rw [he] at hh
    simpa using hh.mul_const C
  apply squeeze_zero' ?_ ?_ ht
  · exact Filter.Eventually.of_forall (fun N=>mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Finset.sum_nonneg (fun j _=>Real.rpow_nonneg (by positivity) _)))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hh := mul_le_mul_of_nonneg_left (weighted_power_sum_bound hr hrs N hN)
      (Real.rpow_nonneg (Nat.cast_nonneg N) (-b))
    have he : (N:ℝ)^(-b)*((N:ℝ)^r*C)=(N:ℝ)^(r-b)*C := by
      rw [←mul_assoc,←Real.rpow_add (by positivity)]
      congr 2
      ring
    rwa [he] at hh

/-- `N^(-uQ) ∑_{j<N} (j+1)^(-u/2) → 0` when `u > 1/(Q + 1/2)`. -/
theorem momentum_power_sum_tendsto {u Q : ℝ} (hu : 0<u) (hQ : 0<Q)
    (hthreshold : 1/(Q+1/2)<u) :
    Tendsto (fun N : ℕ => (N:ℝ)^(-u*Q)*
      (∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-u/2))) atTop (𝓝 0) := by
  have ht : 1<u*(Q+1/2) := (div_lt_iff₀ (by linarith)).mp hthreshold
  have hh := weighted_power_sum_tendsto (s:=u/2) (b:=u*Q) (mul_pos hu hQ) (by nlinarith)
  simpa only [neg_mul,neg_div] using hh

lemma power_decay (c e : ℝ) (he : e < 0) :
    Tendsto (fun N : ℕ => c*(N : ℝ)^e) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by linarith : 0 < -e)).comp
    tendsto_natCast_atTop_atTop
  simpa using h.const_mul c

end ClippedSGD.MomentumAsymptotics
