import ClippedSGD.MomentumLogWindow

/-! The choice of the horizon, the dimension, and the signal in the momentum lower bound. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace ClippedSGD.MomentumHorizon
open MomentumParameters MomentumOracle MomentumFiniteLower

def tailPower (p u h : ℝ) : ℝ := h+u/(p-1)+5
def windowScale (ρ a P : ℝ) : ℝ := (3:ℝ)^a*P/ρ

lemma early_probability_bound (D p u θ : ℝ) (hD : 0 < D) (hp : 1 < p)
    (N : ℕ) (hN : 0 < N) :
    (earlyCutoff θ N : ℝ) * rareProbability (8*D*(N : ℝ)^(-u)) p ≤
      probabilityConstant D p * (N : ℝ)^(θ-u*qExponent p) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [rareProbability_horizon D p u hD hp N hN]
  calc
    _ ≤ (N : ℝ)^θ * (probabilityConstant D p * (N : ℝ)^(-u*qExponent p)) := by
      apply mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg hn.le θ))
      unfold probabilityConstant
      positivity
    _ = _ := by
      rw [show θ-u*qExponent p = θ+(-u*qExponent p) by ring, Real.rpow_add hn]
      ring

lemma eventually_large_cutoff (θ : ℝ) (hθ : 0 < θ) (t₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, t₀ ≤ earlyCutoff θ N := by
  have h := ((tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (t₀ : ℝ))
  filter_upwards [h] with N hN
  exact Nat.le_floor hN

lemma exists_collision_dimension (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℕ, (N : ℝ)^2/(d+1 : ℝ) < ε := by
  obtain ⟨d, hd⟩ := exists_nat_gt ((N : ℝ)^2/ε)
  refine ⟨d, ?_⟩
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < d+1)).mpr
  have h := (div_lt_iff₀ hε).mp hd
  nlinarith

lemma arrival_expectation_bound (D u θ ρ a P H h A μ π : ℝ)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hμ : μ ≤ 1) (hπ : 0 ≤ π)
    (hH : 0 ≤ H) (hh : 0 ≤ h) (hρ : 0 < ρ) (hP : 0 ≤ P)
    (hm : π*A=μ) (N : ℕ) (hN : 0 < N) :
    π * ∑ i : Fin N,
      arrivalWeight A (H*(N+1 : ℝ)^h) N (earlyCutoff θ N) (envelope D u)
        (windowGap ρ a) (MomentumLogWindow.window (windowScale ρ a P) a N) i ≤
      (2*Real.sqrt (2*D))*π * (∑ i : Fin N, (i.val+1 : ℝ)^(-u/2)) +
      H*(2 : ℝ)^h * (N : ℝ)^(h+2-P) := by
  have hpoint (i : Fin N) :
      arrivalWeight A (H*(N+1 : ℝ)^h) N (earlyCutoff θ N) (envelope D u)
        (windowGap ρ a) (MomentumLogWindow.window (windowScale ρ a P) a N) i ≤
      2*Real.sqrt (2*D)*(i.val+1 : ℝ)^(-u/2) +
        A*(H*(N+1 : ℝ)^h)*N*(N:ℝ)^(-P) := by
    unfold arrivalWeight
    split_ifs
    · rw [envelope_sqrt D u hD]
      apply add_le_add
      · ring_nf; exact le_rfl
      · exact mul_le_mul_of_nonneg_left
          (MomentumLogWindow.exponential_tail ρ P a hρ hP N i.val hN) (by positivity)
    · positivity
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)) hπ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have htail : π * ((N:ℝ)*(A*(H*(N+1:ℝ)^h)*N*(N:ℝ)^(-P))) ≤
      H*(2:ℝ)^h*(N:ℝ)^(h+2-P) := by
    calc
      _ = μ*(H*(N+1:ℝ)^h)*(N:ℝ)^2*(N:ℝ)^(-P) := by rw [←hm]; ring
      _ ≤ 1*(H*(N+1:ℝ)^h)*(N:ℝ)^2*(N:ℝ)^(-P) := by gcongr
      _ ≤ 1*(H*(2:ℝ)^h*(N:ℝ)^h)*(N:ℝ)^2*(N:ℝ)^(-P) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (gain_horizon_bound H h hH hh N hN) zero_le_one)
          (sq_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := by
        rw [show h+2-P = (h+2)+(-P) by ring,
          Real.rpow_add (by exact_mod_cast hN : (0:ℝ)<N),
          Real.rpow_add (by exact_mod_cast hN : (0:ℝ)<N), Real.rpow_two]
        ring
  nlinarith

lemma budget_tendsto (D p u P H h : ℝ)
    (hp : 1 < p) (hu : 0 < u) (hP : h+2 < P)
    (hthreshold : 1/(qExponent p+1/2) < u) :
    Tendsto (fun N : ℕ =>
      (2*Real.sqrt (2*D))*probabilityConstant D p *
        ((N:ℝ)^(-u*qExponent p)*(∑ i : Fin N, (i.val+1:ℝ)^(-u/2))) +
      H*(2:ℝ)^h*(N:ℝ)^(h+2-P)) atTop (𝓝 0) := by
  have hQ : 0 < qExponent p := div_pos (by linarith) (by linarith)
  have hs := (MomentumAsymptotics.momentum_power_sum_tendsto hu hQ hthreshold).const_mul
    ((2*Real.sqrt (2*D))*probabilityConstant D p)
  have ht := MomentumAsymptotics.power_decay (H*(2:ℝ)^h) (h+2-P) (by linarith)
  simpa only [Finset.sum_range, Nat.cast_add, Nat.cast_one, mul_assoc, mul_zero, add_zero] using hs.add ht

structure HorizonData (D p u θ ρ a P H h δ : ℝ) (t₀ : ℕ) where
  N : ℕ
  d : ℕ
  positive : 0 < N
  cutoff_le : earlyCutoff θ N ≤ N
  cutoff_large : t₀ ≤ earlyCutoff θ N
  signal_small : 8*D*(N:ℝ)^(-u) ≤ 1/128
  short : ∀ j, earlyCutoff θ N ≤ j → MomentumLogWindow.window (windowScale ρ a P) a N j ≤ j+1
  small : ∀ j, earlyCutoff θ N ≤ j →
    Real.sqrt (2*envelope D u (j+1))*
      Real.sqrt (MomentumLogWindow.window (windowScale ρ a P) a N j:ℝ) ≤ (1/16:ℝ)/2
  numeric :
    rareProbability (8*D*(N:ℝ)^(-u)) p *
      ∑ i : Fin N, arrivalWeight (rareAmplitude (8*D*(N:ℝ)^(-u)) p)
        (H*(N+1:ℝ)^h) N (earlyCutoff θ N) (envelope D u)
        (windowGap ρ a) (MomentumLogWindow.window (windowScale ρ a P) a N) i <
      (1-δ-(N:ℝ)^2/(d+1:ℝ)-
        (earlyCutoff θ N:ℝ)*rareProbability (8*D*(N:ℝ)^(-u)) p)/2

theorem select_horizon (D p u θ ρ a H h δ : ℝ) (t₀ : ℕ)
    (hD : 0 < D) (hp : 1 < p) (hu : 0 < u) (ha : a < 1)
    (hau : a < u) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθQ : θ < u*qExponent p)
    (hρ : 0 < ρ) (hH : 0 ≤ H) (hh : 0 ≤ h)
    (hδ : δ < 1) (hthreshold : 1/(qExponent p+1/2) < u) :
    Nonempty (HorizonData D p u θ ρ a (tailPower p u h) H h δ t₀) := by
  let P := tailPower p u h
  let Λ := windowScale ρ a P
  have hP : h+2 < P := by
    have := div_pos hu (by linarith : 0 < p-1)
    dsimp [P,tailPower]; linarith
  have hP0 : 0 ≤ P := by linarith
  have hΛ : 0 ≤ Λ := by unfold Λ windowScale; positivity
  let ε := (1-δ)/8
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hμ := (MomentumAsymptotics.power_decay (8*D) (-u) (by linarith)).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/128))
  have hearly := (MomentumAsymptotics.power_decay (probabilityConstant D p) (θ-u*qExponent p)
    (by linarith)).eventually (gt_mem_nhds hε)
  have hbudget := (budget_tendsto D p u P H h hp hu hP hthreshold).eventually
    (gt_mem_nhds hε)
  have hsmall := MomentumLogWindow.eventually_small_windows D Λ u a θ (1/16)
    hD.le hΛ hau hu hθ (by norm_num)
  have hshort := MomentumLogWindow.eventually_short_windows Λ a θ hΛ ha hθ
  have hlarge := eventually_large_cutoff θ hθ t₀
  obtain ⟨N,hN,hμN,hearlyN,hbudgetN,hsmallN,hshortN,hlargeN⟩ :=
    (eventually_gt_atTop (0:ℕ) |>.and (hμ.and (hearly.and
      (hbudget.and (hsmall.and (hshort.and hlarge)))))).exists
  obtain ⟨d,hd⟩ := exists_collision_dimension N ε hε
  have hm0 : 0 < 8*D*(N:ℝ)^(-u) := by positivity
  have hA : 0 < rareAmplitude (8*D*(N:ℝ)^(-u)) p := rareAmplitude_pos hm0
  have hπ : 0 < rareProbability (8*D*(N:ℝ)^(-u)) p := rareProbability_pos hm0
  have hex := arrival_expectation_bound D u θ ρ a P H h
    (rareAmplitude (8*D*(N:ℝ)^(-u)) p) (8*D*(N:ℝ)^(-u))
    (rareProbability (8*D*(N:ℝ)^(-u)) p) hD.le hA.le
    (by linarith) hπ.le hH hh hρ hP0 (rare_centering hm0) N hN
  rw [rareProbability_horizon D p u hD hp N hN] at hex
  have heq : (2*Real.sqrt (2*D))*(probabilityConstant D p*(N:ℝ)^(-u*qExponent p))*
      (∑ i : Fin N, (i.val+1:ℝ)^(-u/2)) =
      (2*Real.sqrt (2*D))*probabilityConstant D p*((N:ℝ)^(-u*qExponent p)*
      (∑ i : Fin N, (i.val+1:ℝ)^(-u/2))) := by ring
  rw [heq] at hex
  rw [←rareProbability_horizon D p u hD hp N hN] at hex
  have hearly' := (early_probability_bound D p u θ hD hp N hN).trans_lt hearlyN
  refine ⟨⟨N,d,hN,earlyCutoff_le θ hθ1 N hN,hlargeN,hμN.le,hshortN,hsmallN,?_⟩⟩
  have he := hex.trans_lt hbudgetN
  dsimp [ε] at hd hearly' he
  linarith

end ClippedSGD.MomentumHorizon
