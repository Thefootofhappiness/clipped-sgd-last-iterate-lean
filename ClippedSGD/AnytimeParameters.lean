import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import ClippedSGD.EnergyBudget
import ClippedSGD.SuffixPotential

/-!
# Explicit Constants and Deterministic Budgets for Horizon-Free Clipped SGD

This module formalizes the exponents and the schedule of the time-uniform upper bound
(`eq:anytime-exponents`, `eq:anytime-upper-schedule`) and its explicit constants and deterministic
budgets (`app:anytime-upper-constants`, `lem:anytime-budgets`).
-/

open Set Finset
open scoped BigOperators

set_option autoImplicit false

namespace ClippedSGD.AnytimeParameters

noncomputable section

/-! ## 1. Exponents, Explicit Constants, and Schedules -/

/-- Rate exponent `β = β_p = 2(p - 1) / (3p - 1)` (`eq:anytime-exponents`). -/
def betaExp (p : ℝ) : ℝ := 2 * (p - 1) / (3 * p - 1)

/-- Step-size decay exponent `a = (p + 1) / (3p - 1) = 1 - β` (`eq:anytime-exponents`). -/
def aExp (p : ℝ) : ℝ := (p + 1) / (3 * p - 1)

/-- Clipping threshold growth exponent `b = 2 / (3p - 1)` (`eq:anytime-exponents`). -/
def bExp (p : ℝ) : ℝ := 2 / (3 * p - 1)

/-- Variance growth exponent `v = (2 - p) b`. -/
def vExp (p : ℝ) : ℝ := (2 - p) * bExp p

/-- Dyadic ratio `q = 2 ^ (-β)`. -/
def qBase (p : ℝ) : ℝ := (2 : ℝ) ^ (-betaExp p)

/-- Closed-form dyadic series constant
`J_β = q(1 + q)/(1 - q)³ + 4q/(1 - q)² + 4/(1 - q)` (`eq:anytime-constants`). -/
def J_beta (p : ℝ) : ℝ :=
  let q := qBase p
  q * (1 + q) / (1 - q) ^ 3 + 4 * q / (1 - q) ^ 2 + 4 / (1 - q)

/-- Step-sum constant `H_β = 64 (1 + β⁻¹ + J_β)` (`eq:anytime-constants`). -/
def H_beta (p : ℝ) : ℝ := 64 * (1 + (betaExp p)⁻¹ + J_beta p)

/-- Budget constant `K = 2 ^ 20 * H_β ^ 4` (`eq:anytime-constants`). -/
def K_const (p : ℝ) : ℝ := (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (4 : ℕ)

/-- Schedule constant `c_p = 1 / (1000 K)` (`eq:anytime-constants`). -/
def c_p (p : ℝ) : ℝ := 1 / (1000 * K_const p)

/-- Rate prefactor `D_p = 4 / c_p` (`eq:anytime-constants`). -/
def D_p (p : ℝ) : ℝ := 4 / c_p p

/-- Problem scale `Q = max(L R, σ)`. -/
def scaleQ (L R σ : ℝ) : ℝ := max (L * R) σ

/-- Logarithmic factor `ℓ_t = log(100 t²)` for `t ≥ 1`. -/
def ell (t : ℕ) : ℝ := Real.log (100 * (t : ℝ) ^ (2 : ℕ))

/-- Confidence-dependent logarithmic factor `ι_t(δ) = log(100 t² / δ)`. -/
def iota (δ : ℝ) (t : ℕ) : ℝ := Real.log (100 * (t : ℝ) ^ (2 : ℕ) / δ)

/-- Global radius confidence parameter `h = log(100 / δ)`. -/
def confH (δ : ℝ) : ℝ := Real.log (100 / δ)

/-- Normalized step size `η_t = c t ^ (-a) / ℓ_t²` for `t ≥ 1`, and `0` at `t = 0`. -/
def normStep (p c : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 0 else c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ)

lemma normStep_zero (p c : ℝ) : normStep p c 0 = 0 := rfl

lemma normStep_of_pos (p c : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    normStep p c t = c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ) :=
  if_neg (by omega)

/-- Normalized clipping threshold `λ_t = 4 t ^ b`. -/
def normLambda (p : ℝ) (t : ℕ) : ℝ := 4 * (t : ℝ) ^ (bExp p)

/-- Normalized deterministic bias bound `B_t = 2 λ_t ^ (1 - p)` (`eq:anytime-clipping`). -/
def normB (p : ℝ) (t : ℕ) : ℝ := 2 * (normLambda p t) ^ (1 - p)

/-- Normalized deterministic variance bound `V_t = 2 λ_t ^ (2 - p)` (`eq:anytime-clipping`). -/
def normV (p : ℝ) (t : ℕ) : ℝ := 2 * (normLambda p t) ^ (2 - p)

/-- Unnormalized step size `η_t = (R / Q) c_p t ^ (-a) / ℓ_t²` (`eq:anytime-upper-schedule`). -/
def anytimeStep (L R σ p : ℝ) (t : ℕ) : ℝ :=
  (R / scaleQ L R σ) * normStep p (c_p p) t

/-- Unnormalized clipping threshold `λ_t = 4 Q t ^ b` (`eq:anytime-upper-schedule`). -/
def anytimeLambda (L R σ p : ℝ) (t : ℕ) : ℝ :=
  scaleQ L R σ * normLambda p t

lemma scaleQ_pos {L R σ : ℝ} (hL : 0 < L) (hR : 0 < R) : 0 < scaleQ L R σ := by
  unfold scaleQ
  have : 0 < L * R := mul_pos hL hR
  exact lt_of_lt_of_le this (le_max_left (L * R) σ)

lemma anytimeStep_eq (L R σ p : ℝ) (t : ℕ) :
    anytimeStep L R σ p t = (R / scaleQ L R σ) * normStep p (c_p p) t := rfl

lemma anytimeLambda_eq (L R σ p : ℝ) (t : ℕ) :
    anytimeLambda L R σ p t = scaleQ L R σ * normLambda p t := rfl

lemma normLambda_nonneg (p : ℝ) (t : ℕ) : 0 ≤ normLambda p t := by
  unfold normLambda; positivity

/-! ## 2. Exponent Identities and Constant Positivity -/

lemma three_p_sub_one_pos {p : ℝ} (hp : 1 < p) : 0 < 3 * p - 1 := by linarith

lemma betaExp_pos {p : ℝ} (hp : 1 < p) : 0 < betaExp p := by
  unfold betaExp
  have : 0 < p - 1 := by linarith
  have : 0 < 3 * p - 1 := by linarith
  positivity

lemma betaExp_le_two_fifths {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    betaExp p ≤ 2 / 5 := by
  unfold betaExp
  rw [div_le_div_iff₀ (three_p_sub_one_pos hp) (by norm_num)]
  linarith

lemma aExp_pos {p : ℝ} (hp : 1 < p) : 0 < aExp p := by
  unfold aExp
  have : 0 < p + 1 := by linarith
  have : 0 < 3 * p - 1 := by linarith
  positivity

lemma bExp_pos {p : ℝ} (hp : 1 < p) : 0 < bExp p := by
  unfold bExp
  have : 0 < 3 * p - 1 := by linarith
  positivity

lemma bExp_le_one {p : ℝ} (hp : 1 < p) : bExp p ≤ 1 := by
  unfold bExp
  rw [div_le_iff₀ (three_p_sub_one_pos hp)]
  linarith

lemma vExp_nonneg {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) : 0 ≤ vExp p := by
  unfold vExp
  exact mul_nonneg (by linarith) (bExp_pos hp).le

/-- Exponent identities (`eq:anytime-identities`). -/
lemma bExp_mul_sub_one {p : ℝ} : bExp p * (p - 1) = betaExp p := by
  unfold bExp betaExp; ring

lemma aExp_add_betaExp {p : ℝ} (hp : 1 < p) : aExp p + betaExp p = 1 := by
  unfold aExp betaExp
  have hne : (3 * p - 1 : ℝ) ≠ 0 := (three_p_sub_one_pos hp).ne'
  field_simp; ring

lemma two_mul_aExp_sub_bExp {p : ℝ} : 2 * (aExp p - bExp p) = betaExp p := by
  unfold aExp bExp betaExp; ring

lemma aExp_sub_vExp {p : ℝ} : aExp p - vExp p = (3 / 2 : ℝ) * betaExp p := by
  unfold aExp vExp bExp betaExp; ring

lemma two_aExp_sub_vExp {p : ℝ} (hp : 1 < p) :
    2 * aExp p - vExp p = 1 + (1 / 2 : ℝ) * betaExp p := by
  unfold aExp vExp bExp betaExp
  have hne : (3 * p - 1 : ℝ) ≠ 0 := (three_p_sub_one_pos hp).ne'
  field_simp; ring

lemma qBase_pos (p : ℝ) : 0 < qBase p := by
  unfold qBase; positivity

lemma qBase_lt_one {p : ℝ} (hp : 1 < p) : qBase p < 1 := by
  unfold qBase
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr (betaExp_pos hp))

lemma one_sub_qBase_pos {p : ℝ} (hp : 1 < p) : 0 < 1 - qBase p :=
  sub_pos.mpr (qBase_lt_one hp)

lemma J_beta_ge_four {p : ℝ} (hp : 1 < p) : 4 ≤ J_beta p := by
  unfold J_beta
  have hq : 0 < qBase p := qBase_pos p
  have h1q : 0 < 1 - qBase p := one_sub_qBase_pos hp
  have h1q_le : 1 - qBase p ≤ 1 := by linarith
  have hdiv : 4 ≤ 4 / (1 - qBase p) := by
    rw [le_div_iff₀ h1q]
    linarith
  have hpos1 : 0 ≤ qBase p * (1 + qBase p) / (1 - qBase p) ^ 3 := by positivity
  have hpos2 : 0 ≤ 4 * qBase p / (1 - qBase p) ^ 2 := by positivity
  linarith

lemma J_beta_pos {p : ℝ} (hp : 1 < p) : 0 < J_beta p :=
  lt_of_lt_of_le (by norm_num) (J_beta_ge_four hp)

lemma eight_J_beta_le_H_beta {p : ℝ} (hp : 1 < p) :
    8 * J_beta p ≤ H_beta p := by
  unfold H_beta
  have hb : 0 < (betaExp p)⁻¹ := inv_pos.mpr (betaExp_pos hp)
  have hJ : 0 < J_beta p := J_beta_pos hp
  linarith

lemma eight_one_add_two_div_beta_le_H_beta {p : ℝ} (hp : 1 < p) :
    8 * (1 + 2 / betaExp p) ≤ H_beta p := by
  unfold H_beta
  have hb : 0 < (betaExp p)⁻¹ := inv_pos.mpr (betaExp_pos hp)
  have hJ : 0 < J_beta p := J_beta_pos hp
  have hdiv : 2 / betaExp p = 2 * (betaExp p)⁻¹ := div_eq_mul_inv 2 (betaExp p)
  linarith

lemma H_beta_ge_64 {p : ℝ} (hp : 1 < p) : 64 ≤ H_beta p := by
  unfold H_beta
  have hb : 0 < (betaExp p)⁻¹ := inv_pos.mpr (betaExp_pos hp)
  have hJ : 4 ≤ J_beta p := J_beta_ge_four hp
  linarith

lemma H_beta_pos {p : ℝ} (hp : 1 < p) : 0 < H_beta p :=
  lt_of_lt_of_le (by norm_num) (H_beta_ge_64 hp)

lemma K_const_ge_one {p : ℝ} (hp : 1 < p) : 1 ≤ K_const p := by
  unfold K_const
  have hH : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
  have hH4 : 1 ≤ (H_beta p) ^ (4 : ℕ) := one_le_pow₀ hH
  nlinarith

lemma K_const_pos {p : ℝ} (hp : 1 < p) : 0 < K_const p :=
  lt_of_lt_of_le zero_lt_one (K_const_ge_one hp)

lemma c_p_pos {p : ℝ} (hp : 1 < p) : 0 < c_p p := by
  unfold c_p
  have := K_const_pos hp
  positivity

lemma K_mul_c_p {p : ℝ} (hp : 1 < p) : K_const p * c_p p = 1 / 1000 := by
  unfold c_p
  have hK : K_const p ≠ 0 := (K_const_pos hp).ne'
  field_simp; ring

lemma c_p_le_inv_1000 {p : ℝ} (hp : 1 < p) : c_p p ≤ 1 / 1000 := by
  have h1 := K_const_ge_one hp
  have hc := (c_p_pos hp).le
  nlinarith [K_mul_c_p hp]

lemma c_p_le_one {p : ℝ} (hp : 1 < p) : c_p p ≤ 1 :=
  (c_p_le_inv_1000 hp).trans (by norm_num)

lemma D_p_ge_4000 {p : ℝ} (hp : 1 < p) : 4000 ≤ D_p p := by
  unfold D_p
  rw [le_div_iff₀ (c_p_pos hp)]
  linarith [c_p_le_inv_1000 hp]

lemma D_p_ge_one {p : ℝ} (hp : 1 < p) : 1 ≤ D_p p :=
  (by norm_num : (1 : ℝ) ≤ 4000).trans (D_p_ge_4000 hp)

/-! ## 3. Logarithmic Factor Bounds -/

lemma four_lt_log_100 : (4 : ℝ) < Real.log 100 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he1 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have he4 : Real.exp 4 = (Real.exp 1) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he4]
  calc
    (Real.exp 1) ^ (4 : ℕ) < 3 ^ (4 : ℕ) :=
      pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by decide)
    _ < 100 := by norm_num

lemma ell_one_eq : ell 1 = Real.log 100 := by
  unfold ell; norm_num

lemma four_lt_ell_one : 4 < ell 1 := by
  rw [ell_one_eq]; exact four_lt_log_100

lemma one_lt_ell_one : 1 < ell 1 := by linarith [four_lt_ell_one]

lemma ell_mono {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) : ell s ≤ ell t := by
  unfold ell
  apply Real.log_le_log
  · have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    positivity
  · have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    nlinarith

lemma four_lt_ell {t : ℕ} (ht : 1 ≤ t) : 4 < ell t :=
  lt_of_lt_of_le four_lt_ell_one (ell_mono le_rfl ht)

lemma ell_pos {t : ℕ} (ht : 1 ≤ t) : 0 < ell t := by
  linarith [four_lt_ell ht]

lemma four_lt_confH {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 4 < confH δ := by
  unfold confH
  have hlt : 100 < 100 / δ := by
    rw [lt_div_iff₀ hδ]
    linarith
  exact lt_trans four_lt_log_100 (Real.log_lt_log (by norm_num) hlt)

lemma confH_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < confH δ := by
  linarith [four_lt_confH hδ hδ1]

lemma confH_le_iota {δ : ℝ} (hδ : 0 < δ) {t : ℕ} (ht : 1 ≤ t) :
    confH δ ≤ iota δ t := by
  unfold confH iota
  apply Real.log_le_log (by positivity)
  apply div_le_div_of_nonneg_right _ hδ.le
  have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  nlinarith

lemma ell_le_iota {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℕ} (ht : 1 ≤ t) :
    ell t ≤ iota δ t := by
  unfold ell iota
  have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  apply Real.log_le_log (by positivity)
  rw [le_div_iff₀ hδ]
  nlinarith

lemma four_lt_iota {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℕ} (ht : 1 ≤ t) :
    4 < iota δ t :=
  lt_of_lt_of_le (four_lt_confH hδ hδ1) (confH_le_iota hδ ht)

/-! ## 4. Pointwise Bounds on Schedule and Clipping Quantities -/

lemma normStep_pos {p c : ℝ} (hc : 0 < c) {t : ℕ} (ht : 1 ≤ t) :
    0 < normStep p c t := by
  rw [normStep_of_pos p c ht]
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hell : 0 < ell t := ell_pos ht
  positivity

lemma normStep_nonneg {p c : ℝ} (hc : 0 ≤ c) (t : ℕ) :
    0 ≤ normStep p c t := by
  unfold normStep
  split_ifs with h0
  · exact le_rfl
  · have ht : 1 ≤ t := by omega
    have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hell : 0 < ell t := ell_pos ht
    positivity

lemma normStep_le_c {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {t : ℕ} (ht : 1 ≤ t) :
    normStep p c t ≤ c := by
  rw [normStep_of_pos p c ht]
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hrpow : (t : ℝ) ^ (-aExp p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht1 (neg_nonpos.mpr (aExp_pos hp).le)
  have hell : 1 ≤ (ell t) ^ (2 : ℕ) := by
    have := four_lt_ell ht
    nlinarith
  calc
    c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ)
      ≤ c * 1 / 1 := div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hrpow hc) zero_lt_one hell
    _ = c := by ring

lemma normLambda_ge_four {p : ℝ} (hp : 1 < p) {t : ℕ} (ht : 1 ≤ t) :
    4 ≤ normLambda p t := by
  unfold normLambda
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hrpow : 1 ≤ (t : ℝ) ^ (bExp p) := Real.one_le_rpow ht1 (bExp_pos hp).le
  linarith

lemma normLambda_pos {p : ℝ} (hp : 1 < p) {t : ℕ} (ht : 1 ≤ t) :
    0 < normLambda p t :=
  lt_of_lt_of_le (by norm_num) (normLambda_ge_four hp ht)

lemma normB_nonneg (p : ℝ) (t : ℕ) : 0 ≤ normB p t := by
  unfold normB normLambda
  positivity

lemma normV_nonneg (p : ℝ) (t : ℕ) : 0 ≤ normV p t := by
  unfold normV normLambda
  positivity

/-- From `B_t = 2 λ_t ^ (1 - p)` and `λ_t = 4 t ^ b`, we have `B_t ≤ 2 t ^ (-β)`
. -/
lemma normB_le {p : ℝ} (hp : 1 < p) {t : ℕ} (ht : 1 ≤ t) :
    normB p t ≤ 2 * (t : ℝ) ^ (-betaExp p) := by
  unfold normB normLambda
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht0.le _),
    ← Real.rpow_mul ht0.le]
  have hmul : bExp p * (1 - p) = -betaExp p := by
    rw [← bExp_mul_sub_one]; ring
  rw [hmul]
  have h4 : (4 : ℝ) ^ (1 - p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have htr : 0 ≤ (t : ℝ) ^ (-betaExp p) := Real.rpow_nonneg ht0.le _
  nlinarith

/-- From `V_t = 2 λ_t ^ (2 - p)` and `λ_t = 4 t ^ b`, we have `V_t ≤ 8 t ^ v`
. -/
lemma normV_le {p : ℝ} (hp : 1 < p) {t : ℕ} (ht : 1 ≤ t) :
    normV p t ≤ 8 * (t : ℝ) ^ (vExp p) := by
  unfold normV normLambda
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ht0.le _),
    ← Real.rpow_mul ht0.le]
  have hmul : bExp p * (2 - p) = vExp p := by
    unfold vExp; ring
  rw [hmul]
  have h4 : (4 : ℝ) ^ (2 - p) ≤ (4 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_one] at h4
  have htr : 0 ≤ (t : ℝ) ^ (vExp p) := Real.rpow_nonneg ht0.le _
  nlinarith

/-- Pointwise bound `η_t B_t ≤ 2 c / (t ℓ_t²)`. -/
lemma normStep_mul_normB_le {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {t : ℕ} (ht : 1 ≤ t) :
    normStep p c t * normB p t ≤ 2 * c / ((t : ℝ) * (ell t) ^ (2 : ℕ)) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hstep_nn : 0 ≤ normStep p c t := normStep_nonneg hc t
  have h1 := mul_le_mul_of_nonneg_left (normB_le hp ht) hstep_nn
  refine h1.trans_eq ?_
  rw [normStep_of_pos p c ht]
  have hrpow : (t : ℝ) ^ (-aExp p) * (t : ℝ) ^ (-betaExp p) = (t : ℝ)⁻¹ := by
    rw [← Real.rpow_add ht0, show -aExp p + -betaExp p = -(aExp p + betaExp p) by ring,
      aExp_add_betaExp hp, Real.rpow_neg_one]
  calc
    c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ) * (2 * (t : ℝ) ^ (-betaExp p))
      = 2 * c * ((t : ℝ) ^ (-aExp p) * (t : ℝ) ^ (-betaExp p)) / (ell t) ^ (2 : ℕ) := by ring
    _ = 2 * c * (t : ℝ)⁻¹ / (ell t) ^ (2 : ℕ) := by rw [hrpow]
    _ = 2 * c / ((t : ℝ) * (ell t) ^ (2 : ℕ)) := by ring

/-- Pointwise bound `η_t² V_t ≤ 8 c² t ^ (-1 - β/2) / ℓ_t⁴`. -/
lemma normStep_sq_mul_normV_le {p c : ℝ} (hp : 1 < p) {t : ℕ} (ht : 1 ≤ t) :
    (normStep p c t) ^ (2 : ℕ) * normV p t ≤
      8 * c ^ (2 : ℕ) * (t : ℝ) ^ (-1 - betaExp p / 2) / (ell t) ^ (4 : ℕ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have h1 := mul_le_mul_of_nonneg_left (normV_le hp ht) (sq_nonneg (normStep p c t))
  refine h1.trans_eq ?_
  rw [normStep_of_pos p c ht]
  have hrpow : ((t : ℝ) ^ (-aExp p)) ^ (2 : ℕ) * (t : ℝ) ^ (vExp p) =
      (t : ℝ) ^ (-1 - betaExp p / 2) := by
    rw [← Real.rpow_natCast ((t : ℝ) ^ (-aExp p)) 2, ← Real.rpow_mul ht0.le,
      ← Real.rpow_add ht0]
    congr 1
    have h2a := two_aExp_sub_vExp hp
    push_cast
    linarith
  calc
    (c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ)) ^ (2 : ℕ) * (8 * (t : ℝ) ^ (vExp p))
      = 8 * c ^ (2 : ℕ) * (((t : ℝ) ^ (-aExp p)) ^ (2 : ℕ) * (t : ℝ) ^ (vExp p)) /
          (ell t) ^ (4 : ℕ) := by ring
    _ = 8 * c ^ (2 : ℕ) * (t : ℝ) ^ (-1 - betaExp p / 2) / (ell t) ^ (4 : ℕ) := by rw [hrpow]

/-- Pointwise identity `η_t² λ_t² = 16 c² t ^ (-β) / ℓ_t⁴`. -/
lemma normStep_sq_mul_normLambda_sq {p c : ℝ} {t : ℕ} (ht : 1 ≤ t) :
    (normStep p c t) ^ (2 : ℕ) * (normLambda p t) ^ (2 : ℕ) =
      16 * c ^ (2 : ℕ) * (t : ℝ) ^ (-betaExp p) / (ell t) ^ (4 : ℕ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [normStep_of_pos p c ht]
  unfold normLambda
  have hrpow : ((t : ℝ) ^ (-aExp p)) ^ (2 : ℕ) * ((t : ℝ) ^ (bExp p)) ^ (2 : ℕ) =
      (t : ℝ) ^ (-betaExp p) := by
    rw [← Real.rpow_natCast ((t : ℝ) ^ (-aExp p)) 2, ← Real.rpow_mul ht0.le,
      ← Real.rpow_natCast ((t : ℝ) ^ (bExp p)) 2, ← Real.rpow_mul ht0.le,
      ← Real.rpow_add ht0]
    congr 1
    have h2ab := two_mul_aExp_sub_bExp (p := p)
    push_cast
    linarith
  calc
    (c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ)) ^ (2 : ℕ) *
        (4 * (t : ℝ) ^ (bExp p)) ^ (2 : ℕ)
      = 16 * c ^ (2 : ℕ) * (((t : ℝ) ^ (-aExp p)) ^ (2 : ℕ) * ((t : ℝ) ^ (bExp p)) ^ (2 : ℕ)) /
          (ell t) ^ (4 : ℕ) := by ring
    _ = 16 * c ^ (2 : ℕ) * (t : ℝ) ^ (-betaExp p) / (ell t) ^ (4 : ℕ) := by rw [hrpow]

/-- Pointwise bound `η_t λ_t ≤ 4 c / ℓ_1²` (`eq:global-anytime-budgets`). -/
lemma normStep_mul_normLambda_le {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {t : ℕ} (ht : 1 ≤ t) :
    normStep p c t * normLambda p t ≤ 4 * c / (ell 1) ^ (2 : ℕ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  rw [normStep_of_pos p c ht]
  unfold normLambda
  have hrpow : (t : ℝ) ^ (-aExp p) * (t : ℝ) ^ (bExp p) ≤ 1 := by
    rw [← Real.rpow_add ht0]
    apply Real.rpow_le_one_of_one_le_of_nonpos ht1
    have h2ab := two_mul_aExp_sub_bExp (p := p)
    have hb := betaExp_pos hp
    linarith
  have hell : (ell 1) ^ (2 : ℕ) ≤ (ell t) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (ell_pos le_rfl).le (ell_mono le_rfl ht) 2
  have hell1_pos : 0 < (ell 1) ^ (2 : ℕ) := by have := ell_pos le_rfl; positivity
  calc
    c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ) * (4 * (t : ℝ) ^ (bExp p))
      = 4 * c * ((t : ℝ) ^ (-aExp p) * (t : ℝ) ^ (bExp p)) / (ell t) ^ (2 : ℕ) := by ring
    _ ≤ 4 * c * 1 / (ell 1) ^ (2 : ℕ) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left hrpow (by positivity)
      · exact hell1_pos
      · exact hell
    _ = 4 * c / (ell 1) ^ (2 : ℕ) := by ring

/-! ## 5. Algebraic Telescoping and Global Anytime Budgets -/

/-- For `t ≥ 2`, `1 / t ≤ log t - log (t - 1)`. -/
lemma inv_le_log_sub_log {t : ℕ} (ht : 2 ≤ t) :
    1 / (t : ℝ) ≤ Real.log (t : ℝ) - Real.log ((t - 1 : ℕ) : ℝ) := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := by positivity
  have htm1_pos : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by
    have : 1 ≤ t - 1 := by omega
    exact_mod_cast this
  have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hexp := Real.add_one_le_exp (-(1 / (t : ℝ)))
  have hdiv : ((t - 1 : ℕ) : ℝ) / (t : ℝ) = -(1 / (t : ℝ)) + 1 := by
    rw [hcast]; field_simp; ring
  rw [← hdiv] at hexp
  have hlog := Real.log_le_log (div_pos htm1_pos ht_pos) hexp
  rw [Real.log_exp, Real.log_div htm1_pos.ne' ht_pos.ne'] at hlog
  linarith

/-- For `t ≥ 2`, `2 / t ≤ ℓ_t - ℓ_{t - 1}`. -/
lemma two_div_le_ell_sub_ell {t : ℕ} (ht : 2 ≤ t) :
    2 / (t : ℝ) ≤ ell t - ell (t - 1) := by
  unfold ell
  have ht_pos : (0 : ℝ) < (t : ℝ) := by positivity
  have htm1_pos : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by
    have : 1 ≤ t - 1 := by omega
    exact_mod_cast this
  have hlog1 : Real.log (100 * (t : ℝ) ^ (2 : ℕ)) = Real.log 100 + 2 * Real.log (t : ℝ) := by
    rw [Real.log_mul (by norm_num) (pow_pos ht_pos 2).ne', Real.log_pow]
    push_cast; ring
  have hlog2 : Real.log (100 * ((t - 1 : ℕ) : ℝ) ^ (2 : ℕ)) =
      Real.log 100 + 2 * Real.log ((t - 1 : ℕ) : ℝ) := by
    rw [Real.log_mul (by norm_num) (pow_pos htm1_pos 2).ne', Real.log_pow]
    push_cast; ring
  rw [hlog1, hlog2, show (2 : ℝ) / (t : ℝ) = 2 * (1 / (t : ℝ)) by ring]
  have h := inv_le_log_sub_log ht
  linarith

/-- For `t ≥ 2`, `1 / (t ℓ_t²) ≤ (1 / 2) * (1 / ℓ_{t - 1} - 1 / ℓ_t)`. -/
lemma inv_t_ell_sq_le_sub {t : ℕ} (ht : 2 ≤ t) :
    1 / ((t : ℝ) * (ell t) ^ (2 : ℕ)) ≤ (1 / 2 : ℝ) * (1 / ell (t - 1) - 1 / ell t) := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := by positivity
  have hell_t : 0 < ell t := ell_pos (by omega)
  have hell_tm1 : 0 < ell (t - 1) := ell_pos (by omega)
  have hmono : ell (t - 1) ≤ ell t := ell_mono (by omega) (by omega)
  have hdiff := two_div_le_ell_sub_ell ht
  calc
    1 / ((t : ℝ) * (ell t) ^ (2 : ℕ))
      = (1 / 2 : ℝ) * (2 / (t : ℝ)) / (ell t * ell t) := by ring
    _ ≤ (1 / 2 : ℝ) * (ell t - ell (t - 1)) / (ell (t - 1) * ell t) := by
      apply div_le_div₀ (by linarith [hmono])
      · linarith
      · positivity
      · exact mul_le_mul_of_nonneg_right hmono hell_t.le
    _ = (1 / 2 : ℝ) * (1 / ell (t - 1) - 1 / ell t) := by
      field_simp

/-- Telescoping bound `∑_{t=0}^{N-1} 1 / ((t + 1) ℓ_{t+1}²) ≤ 1 / ℓ_1`
. -/
lemma sum_inv_t_ell_sq_le (N : ℕ) :
    (∑ t ∈ Finset.range N, 1 / (((t + 1 : ℕ) : ℝ) * (ell (t + 1)) ^ (2 : ℕ))) ≤ 1 / ell 1 := by
  have hell1 : 4 < ell 1 := four_lt_ell_one
  have hell1_pos : 0 < ell 1 := by linarith
  suffices h : ∀ n : ℕ,
      (∑ t ∈ Finset.range n, 1 / (((t + 1 : ℕ) : ℝ) * (ell (t + 1)) ^ (2 : ℕ))) ≤
        1 / (ell 1) ^ (2 : ℕ) + (1 / 2 : ℝ) * (1 / ell 1 - 1 / ell (max 1 n)) by
    have hn := h N
    have hpos : 0 ≤ 1 / ell (max 1 N) := by
      have : 0 < ell (max 1 N) := ell_pos (le_max_left 1 N)
      positivity
    have h1 : 1 / (ell 1) ^ (2 : ℕ) + (1 / 2 : ℝ) * (1 / ell 1) ≤ 1 / ell 1 := by
      rw [← sub_nonneg]
      have hsub : 1 / ell 1 - (1 / (ell 1) ^ (2 : ℕ) + (1 / 2 : ℝ) * (1 / ell 1)) =
          (ell 1 - 2) / (2 * (ell 1) ^ (2 : ℕ)) := by
        field_simp; ring
      rw [hsub]
      exact div_nonneg (by linarith) (by positivity)
    linarith
  intro n
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.max_zero, sub_self, mul_zero, add_zero]
    positivity
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases m with _ | m
    · simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_one, one_mul,
        Nat.max_self, sub_self, mul_zero, add_zero, le_rfl]
    · have hm_max : max 1 (m + 1) = m + 1 := Nat.max_eq_right (by omega)
      have hm_max2 : max 1 (m + 2) = m + 2 := Nat.max_eq_right (by omega)
      rw [hm_max] at ih
      rw [hm_max2]
      have hstep : 1 / (((m + 1 + 1 : ℕ) : ℝ) * (ell (m + 1 + 1)) ^ (2 : ℕ)) ≤
          (1 / 2 : ℝ) * (1 / ell (m + 1) - 1 / ell (m + 2)) :=
        inv_t_ell_sq_le_sub (t := m + 2) (by omega)
      linarith

/-- For `t ≥ 2` and `s > 0`, `t ^ (-1 - s) ≤ (1 / s) * ((t - 1) ^ (-s) - t ^ (-s))`. -/
lemma rpow_neg_one_sub_le_sub {s : ℝ} (hs : 0 < s) {t : ℕ} (ht : 2 ≤ t) :
    (t : ℝ) ^ (-1 - s) ≤ (1 / s) * (((t - 1 : ℕ) : ℝ) ^ (-s) - (t : ℝ) ^ (-s)) := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := by positivity
  have htm1_pos : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by
    have : 1 ≤ t - 1 := by omega
    exact_mod_cast this
  have hlog := inv_le_log_sub_log ht
  have hexp_id : ((t - 1 : ℕ) : ℝ) ^ (-s) =
      (t : ℝ) ^ (-s) * Real.exp (s * (Real.log (t : ℝ) - Real.log ((t - 1 : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos htm1_pos, Real.rpow_def_of_pos ht_pos, ← Real.exp_add]
    congr 1; ring
  have h1 : s / (t : ℝ) + 1 ≤
      Real.exp (s * (Real.log (t : ℝ) - Real.log ((t - 1 : ℕ) : ℝ))) := by
    calc
      s / (t : ℝ) + 1 = s * (1 / (t : ℝ)) + 1 := by ring
      _ ≤ s * (Real.log (t : ℝ) - Real.log ((t - 1 : ℕ) : ℝ)) + 1 := by
        nlinarith
      _ ≤ Real.exp (s * (Real.log (t : ℝ) - Real.log ((t - 1 : ℕ) : ℝ))) :=
        Real.add_one_le_exp _
  have h2 : (t : ℝ) ^ (-s) * (s / (t : ℝ)) ≤ ((t - 1 : ℕ) : ℝ) ^ (-s) - (t : ℝ) ^ (-s) := by
    rw [hexp_id]
    have htr : 0 ≤ (t : ℝ) ^ (-s) := Real.rpow_nonneg ht_pos.le _
    nlinarith
  have h3 : (t : ℝ) ^ (-s) * (1 / (t : ℝ)) = (t : ℝ) ^ (-1 - s) := by
    rw [one_div, ← Real.rpow_neg_one (t : ℝ), ← Real.rpow_add ht_pos]
    congr 1; ring
  have h4 : s * (t : ℝ) ^ (-1 - s) ≤ ((t - 1 : ℕ) : ℝ) ^ (-s) - (t : ℝ) ^ (-s) := by
    calc
      s * (t : ℝ) ^ (-1 - s) = (t : ℝ) ^ (-s) * (s / (t : ℝ)) := by
        rw [← h3]; ring
      _ ≤ ((t - 1 : ℕ) : ℝ) ^ (-s) - (t : ℝ) ^ (-s) := h2
  rw [ one_div, le_inv_mul_iff₀ hs ]
  exact h4

/-- Telescoping bound `∑_{t=0}^{N-1} (t + 1) ^ (-1 - s) ≤ 1 + 1 / s`
. -/
lemma sum_rpow_neg_one_sub_le {s : ℝ} (hs : 0 < s) (N : ℕ) :
    (∑ t ∈ Finset.range N, ((t + 1 : ℕ) : ℝ) ^ (-1 - s)) ≤ 1 + 1 / s := by
  suffices h : ∀ n : ℕ,
      (∑ t ∈ Finset.range n, ((t + 1 : ℕ) : ℝ) ^ (-1 - s)) ≤
        1 + (1 / s) * (1 - ((max 1 n : ℕ) : ℝ) ^ (-s)) by
    have hn := h N
    have hpos : 0 ≤ (1 / s) * ((max 1 N : ℕ) : ℝ) ^ (-s) := by
      have : (0 : ℝ) ≤ ((max 1 N : ℕ) : ℝ) := by positivity
      positivity
    linarith [show 1 + (1 / s) * (1 - ((max 1 N : ℕ) : ℝ) ^ (-s)) =
      1 + 1 / s - (1 / s) * ((max 1 N : ℕ) : ℝ) ^ (-s) by ring]
  intro n
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.max_zero, Nat.cast_one,
      Real.one_rpow, sub_self, mul_zero, add_zero, zero_le_one]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases m with _ | m
    · simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_one,
        Real.one_rpow, Nat.max_self, sub_self, mul_zero, add_zero, le_rfl]
    · have hm_max : max 1 (m + 1) = m + 1 := Nat.max_eq_right (by omega)
      have hm_max2 : max 1 (m + 2) = m + 2 := Nat.max_eq_right (by omega)
      rw [hm_max] at ih
      rw [hm_max2]
      have hstep : ((m + 1 + 1 : ℕ) : ℝ) ^ (-1 - s) ≤
          (1 / s) * (((m + 1 : ℕ) : ℝ) ^ (-s) - ((m + 2 : ℕ) : ℝ) ^ (-s)) :=
        rpow_neg_one_sub_le_sub hs (t := m + 2) (by omega)
      have hcomb : (1 + (1 / s) * (1 - ((m + 1 : ℕ) : ℝ) ^ (-s))) +
          (1 / s) * (((m + 1 : ℕ) : ℝ) ^ (-s) - ((m + 2 : ℕ) : ℝ) ^ (-s)) =
          1 + (1 / s) * (1 - ((m + 2 : ℕ) : ℝ) ^ (-s)) := by ring
      linarith

/-- Global anytime bias budget `∑_{t=1}^N η_t B_t ≤ K c / ℓ_1`
 (`eq:global-anytime-budgets`). -/
lemma global_bias_sum_le {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) (N : ℕ) :
    (∑ t ∈ Finset.range N, normStep p c (t + 1) * normB p (t + 1)) ≤
      K_const p * c / ell 1 := by
  have hell1 : 0 < ell 1 := ell_pos le_rfl
  calc
    (∑ t ∈ Finset.range N, normStep p c (t + 1) * normB p (t + 1))
      ≤ ∑ t ∈ Finset.range N, 2 * c / (((t + 1 : ℕ) : ℝ) * (ell (t + 1)) ^ (2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro t _
        exact normStep_mul_normB_le hp hc (by omega)
    _ = 2 * c * ∑ t ∈ Finset.range N,
          1 / (((t + 1 : ℕ) : ℝ) * (ell (t + 1)) ^ (2 : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _; ring
    _ ≤ 2 * c * (1 / ell 1) :=
        mul_le_mul_of_nonneg_left (sum_inv_t_ell_sq_le N) (by positivity)
    _ = 2 * c / ell 1 := by ring
    _ ≤ K_const p * c / ell 1 := by
        apply div_le_div_of_nonneg_right _ hell1.le
        have hK : 2 ≤ K_const p := by
          unfold K_const
          have hH : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
          have hH4 : 1 ≤ (H_beta p) ^ (4 : ℕ) := one_le_pow₀ hH
          nlinarith
        nlinarith

/-- Sharper intermediate global variance bound
`∑_{t=1}^N η_t² V_t ≤ 8(1 + 2/β) c² / ℓ_1⁴ ≤ H_β c² / ℓ_1⁴`. -/
lemma global_variance_sum_le_H_beta {p c : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑ t ∈ Finset.range N, (normStep p c (t + 1)) ^ (2 : ℕ) * normV p (t + 1)) ≤
      H_beta p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  have hell1 : 0 < ell 1 := ell_pos le_rfl
  have hb2 : 0 < betaExp p / 2 := half_pos (betaExp_pos hp)
  calc
    (∑ t ∈ Finset.range N, (normStep p c (t + 1)) ^ (2 : ℕ) * normV p (t + 1))
      ≤ ∑ t ∈ Finset.range N,
          8 * c ^ (2 : ℕ) * ((t + 1 : ℕ) : ℝ) ^ (-1 - betaExp p / 2) / (ell 1) ^ (4 : ℕ) := by
        apply Finset.sum_le_sum
        intro t _
        have hstep := normStep_sq_mul_normV_le hp (c := c) (t := t + 1) (by omega)
        have hell_mono : (ell 1) ^ (4 : ℕ) ≤ (ell (t + 1)) ^ (4 : ℕ) :=
          pow_le_pow_left₀ hell1.le (ell_mono le_rfl (by omega)) 4
        have hnum_nn : 0 ≤ 8 * c ^ (2 : ℕ) * ((t + 1 : ℕ) : ℝ) ^ (-1 - betaExp p / 2) := by
          have : (0 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by positivity
          positivity
        exact hstep.trans (div_le_div_of_nonneg_left hnum_nn (by positivity) hell_mono)
    _ = (8 * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) *
          ∑ t ∈ Finset.range N, ((t + 1 : ℕ) : ℝ) ^ (-1 - betaExp p / 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _; ring
    _ ≤ (8 * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) * (1 + 1 / (betaExp p / 2)) :=
        mul_le_mul_of_nonneg_left (sum_rpow_neg_one_sub_le hb2 N) (by positivity)
    _ = 8 * (1 + 2 / betaExp p) * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring
    _ ≤ H_beta p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (eight_one_add_two_div_beta_le_H_beta hp) (sq_nonneg c)

/-- Global anytime variance budget `∑_{t=1}^N η_t² V_t ≤ K c² / ℓ_1⁴`
 (`eq:global-anytime-budgets`). -/
lemma global_variance_sum_le {p c : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑ t ∈ Finset.range N, (normStep p c (t + 1)) ^ (2 : ℕ) * normV p (t + 1)) ≤
      K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  refine (global_variance_sum_le_H_beta hp N).trans ?_
  apply div_le_div_of_nonneg_right _ (by have := ell_pos le_rfl; positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg c)
  unfold K_const
  have hH : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
  have hH3 : 1 ≤ (H_beta p) ^ (3 : ℕ) := one_le_pow₀ hH
  calc
    H_beta p = 1 * H_beta p := (one_mul _).symm
    _ ≤ (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (3 : ℕ) * H_beta p := by nlinarith
    _ = (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (4 : ℕ) := by ring

/-! ## 6. Dyadic Block Sum and Step Sum Bounds (`eq:step-sum-anytime`) -/

/-- Exact telescoping antiderivative for `q ^ j * (j + 2)²`. -/
def dyadicAntideriv (q : ℝ) (j : ℕ) : ℝ :=
  q ^ j / (1 - q) ^ (3 : ℕ) *
    ((1 - q) ^ (2 : ℕ) * ((j : ℝ) + 2) ^ (2 : ℕ) +
     2 * q * (1 - q) * ((j : ℝ) + 2) +
     q * (1 + q))

lemma dyadicAntideriv_zero {p : ℝ} (hp : 1 < p) :
    dyadicAntideriv (qBase p) 0 = J_beta p := by
  unfold dyadicAntideriv J_beta
  have h1q : 1 - qBase p ≠ 0 := (one_sub_qBase_pos hp).ne'
  push_cast
  field_simp
  ring

lemma dyadicAntideriv_sub {p : ℝ} (hp : 1 < p) (j : ℕ) :
    dyadicAntideriv (qBase p) j - dyadicAntideriv (qBase p) (j + 1) =
      (qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ) := by
  unfold dyadicAntideriv
  have h1q : 1 - qBase p ≠ 0 := (one_sub_qBase_pos hp).ne'
  rw [pow_succ]
  push_cast
  field_simp
  ring

lemma dyadicAntideriv_nonneg {p : ℝ} (hp : 1 < p) (j : ℕ) :
    0 ≤ dyadicAntideriv (qBase p) j := by
  unfold dyadicAntideriv
  have hq : 0 < qBase p := qBase_pos p
  have h1q : 0 < 1 - qBase p := one_sub_qBase_pos hp
  positivity

/-- Finite dyadic polynomial sum bound `∑_{j=0}^{M-1} q^j (j + 2)² ≤ J_β`
(`eq:anytime-constants`). -/
lemma dyadic_poly_sum_le {p : ℝ} (hp : 1 < p) (M : ℕ) :
    (∑ j ∈ Finset.range M, (qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ)) ≤ J_beta p := by
  have htel : (∑ j ∈ Finset.range M, (qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ)) =
      dyadicAntideriv (qBase p) 0 - dyadicAntideriv (qBase p) M := by
    calc
      (∑ j ∈ Finset.range M, (qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ))
        = ∑ j ∈ Finset.range M,
            (dyadicAntideriv (qBase p) j - dyadicAntideriv (qBase p) (j + 1)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact (dyadicAntideriv_sub hp j).symm
      _ = dyadicAntideriv (qBase p) 0 - dyadicAntideriv (qBase p) M :=
          Finset.sum_range_sub' (dyadicAntideriv (qBase p)) M
  rw [htel, dyadicAntideriv_zero hp]
  linarith [dyadicAntideriv_nonneg hp M]

/-- Step size is nonincreasing in `t ≥ 1`. -/
lemma normStep_anti {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) :
    normStep p c t ≤ normStep p c s := by
  rw [normStep_of_pos p c (hs.trans hst), normStep_of_pos p c hs]
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have hrpow : (t : ℝ) ^ (-aExp p) ≤ (s : ℝ) ^ (-aExp p) :=
    Real.rpow_le_rpow_of_nonpos hs0 hst' (neg_nonpos.mpr (aExp_pos hp).le)
  have hell : (ell s) ^ (2 : ℕ) ≤ (ell t) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (ell_pos hs).le (ell_mono hs hst) 2
  have hell_pos : 0 < (ell s) ^ (2 : ℕ) := pow_pos (ell_pos hs) 2
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hrpow hc) hell_pos hell

/-- Lower bound on the suffix step sum: for `1 ≤ k` and `2 k ≤ T + 1`,
`(c / 2) T ^ β / ℓ_T² ≤ S_k` (`eq:step-sum-anytime`). -/
lemma step_sum_lower_bound {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {k T : ℕ}
    (hk : 1 ≤ k) (hkT : 2 * k ≤ T + 1) :
    (c / 2) * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) ≤
      Potential.tailSum (normStep p c) T k := by
  have hT : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  unfold Potential.tailSum
  rw [Nat.max_eq_right hk]
  have hle : (∑ _i ∈ Finset.Ico k (T + 1), normStep p c T) ≤
      ∑ i ∈ Finset.Ico k (T + 1), normStep p c i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_bounds := Finset.mem_Ico.mp hi
    exact normStep_anti hp hc (hk.trans hi_bounds.1) (by omega)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hle
  have hcard : (T : ℝ) / 2 ≤ ((T + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    have hk' : 2 * (k : ℝ) ≤ (T : ℝ) + 1 := by exact_mod_cast hkT
    linarith
  have hstep_nn : 0 ≤ normStep p c T := normStep_nonneg hc T
  have hmul := (mul_le_mul_of_nonneg_right hcard hstep_nn).trans hle
  refine (le_of_eq ?_).trans hmul
  rw [normStep_of_pos p c hT]
  have hrpow : (T : ℝ) * (T : ℝ) ^ (-aExp p) = (T : ℝ) ^ (betaExp p) := by
    calc
      (T : ℝ) * (T : ℝ) ^ (-aExp p)
        = (T : ℝ) ^ (1 : ℝ) * (T : ℝ) ^ (-aExp p) := by rw [Real.rpow_one]
      _ = (T : ℝ) ^ (1 + -aExp p) := (Real.rpow_add hT0 1 (-aExp p)).symm
      _ = (T : ℝ) ^ (betaExp p) := by
        congr 1
        have := aExp_add_betaExp hp
        linarith
  calc
    (c / 2) * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)
      = (c / 2) * ((T : ℝ) * (T : ℝ) ^ (-aExp p)) / (ell T) ^ (2 : ℕ) := by rw [hrpow]
    _ = (T : ℝ) / 2 * (c * (T : ℝ) ^ (-aExp p) / (ell T) ^ (2 : ℕ)) := by ring

/-- Dyadic partition of `Finset.Ioc (T / 2 ^ m) T`. -/
lemma sum_Ioc_dyadic (f : ℕ → ℝ) (T : ℕ) :
    ∀ m : ℕ, (∑ i ∈ Finset.Ioc (T / 2 ^ m) T, f i) =
      ∑ j ∈ Finset.range m, ∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j), f i := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : T / 2 ^ (m + 1) ≤ T / 2 ^ m :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by omega) (Nat.le_succ m)) (by positivity)
    have h2 : T / 2 ^ m ≤ T := Nat.div_le_self T (2 ^ m)
    have hunion : Finset.Ioc (T / 2 ^ (m + 1)) T =
        Finset.Ioc (T / 2 ^ (m + 1)) (T / 2 ^ m) ∪ Finset.Ioc (T / 2 ^ m) T := by
      ext i
      simp only [Finset.mem_Ioc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Ioc (T / 2 ^ (m + 1)) (T / 2 ^ m))
        (Finset.Ioc (T / 2 ^ m) T) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_Ioc] at hi1 hi2
      omega
    rw [hunion, Finset.sum_union hdisj, ih, Finset.sum_range_succ, add_comm]

/-- Logarithmic comparison on a dyadic block: if `T / 2 ^ (j + 1) < i`, then
`ℓ_T ≤ 2 (j + 2) ℓ_i`. -/
lemma ell_T_le_dyadic {T j i : ℕ} (hi : T / 2 ^ (j + 1) < i) :
    ell T ≤ 2 * ((j : ℝ) + 2) * ell i := by
  have hi1 : 1 ≤ i := Nat.zero_lt_of_lt hi
  rcases Nat.eq_zero_or_pos T with rfl | hT0
  · unfold ell
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Real.log_zero]
    have := ell_pos hi1
    positivity
  · have hlt : T < i * 2 ^ (j + 1) := by
      have hdiv : T < 2 ^ (j + 1) * (T / 2 ^ (j + 1) + 1) :=
        Nat.lt_mul_div_succ T (by positivity : 0 < 2 ^ (j + 1))
      rw [mul_comm] at hdiv
      have hle_i : T / 2 ^ (j + 1) + 1 ≤ i := hi
      exact lt_of_lt_of_le hdiv (Nat.mul_le_mul_right (2 ^ (j + 1)) hle_i)
    have hT_le : (T : ℝ) ≤ (i : ℝ) * (2 : ℝ) ^ (j + 1) := by exact_mod_cast hlt.le
    have hi_ge1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hbase_ge : (4 : ℝ) ≤ 100 * (i : ℝ) ^ (2 : ℕ) := by nlinarith
    have hpow_le : (100 * (T : ℝ) ^ (2 : ℕ)) ≤ (100 * (i : ℝ) ^ (2 : ℕ)) ^ (j + 2) := by
      calc
        100 * (T : ℝ) ^ (2 : ℕ)
          ≤ 100 * ((i : ℝ) * (2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) := by
            nlinarith [ (by positivity : (0 : ℝ) ≤ (T : ℝ)) ]
        _ = (100 * (i : ℝ) ^ (2 : ℕ)) * ((2 : ℝ) ^ (2 : ℕ)) ^ (j + 1) := by
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (j + 1)]
            ring
        _ = (100 * (i : ℝ) ^ (2 : ℕ)) * (4 : ℝ) ^ (j + 1) := by norm_num
        _ ≤ (100 * (i : ℝ) ^ (2 : ℕ)) * (100 * (i : ℝ) ^ (2 : ℕ)) ^ (j + 1) := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_left₀ (by norm_num) hbase_ge (j + 1)
            · positivity
        _ = (100 * (i : ℝ) ^ (2 : ℕ)) ^ (j + 2) := by
            rw [pow_succ' (100 * (i : ℝ) ^ (2 : ℕ)) (j + 1)]
    have hlog : ell T ≤ ((j + 2 : ℕ) : ℝ) * ell i := by
      unfold ell
      have hT_pos : (0 : ℝ) < 100 * (T : ℝ) ^ (2 : ℕ) := by
        have : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT0
        positivity
      calc
        Real.log (100 * (T : ℝ) ^ (2 : ℕ))
          ≤ Real.log ((100 * (i : ℝ) ^ (2 : ℕ)) ^ (j + 2)) := Real.log_le_log hT_pos hpow_le
        _ = ((j + 2 : ℕ) : ℝ) * Real.log (100 * (i : ℝ) ^ (2 : ℕ)) := Real.log_pow _ (j + 2)
    have hell_i : 0 < ell i := ell_pos hi1
    push_cast at hlog
    nlinarith

/-- On a dyadic block `T / 2 ^ (j + 1) < i ≤ T / 2 ^ j`,
`1 / ℓ_i² ≤ 4 (j + 2)² / ℓ_T²`. -/
lemma inv_ell_sq_le_dyadic {T j i : ℕ} (hT : 1 ≤ T) (hi : T / 2 ^ (j + 1) < i) :
    1 / (ell i) ^ (2 : ℕ) ≤ 4 * ((j : ℝ) + 2) ^ (2 : ℕ) / (ell T) ^ (2 : ℕ) := by
  have hi1 : 1 ≤ i := Nat.zero_lt_of_lt hi
  have hell_i : 0 < ell i := ell_pos hi1
  have hell_T : 0 < ell T := ell_pos hT
  have hlog := ell_T_le_dyadic hi
  have hsq : (ell T) ^ (2 : ℕ) ≤ (2 * ((j : ℝ) + 2) * ell i) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hell_T.le hlog 2
  rw [div_le_div_iff₀ (pow_pos hell_i 2) (pow_pos hell_T 2)]
  nlinarith

/-- Power sum on a single dyadic block:
`∑_{T / 2 ^ (j + 1) < i ≤ T / 2 ^ j} i ^ (-a) ≤ 2 T ^ β q ^ j`
. -/
lemma sum_rpow_dyadic_block_le {p : ℝ} (hp : 1 < p) {T : ℕ} (hT : 1 ≤ T) (j : ℕ) :
    (∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j), (i : ℝ) ^ (-aExp p)) ≤
      2 * (T : ℝ) ^ (betaExp p) * (qBase p) ^ j := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hq_id : ((T : ℝ) / (2 : ℝ) ^ j) ^ (betaExp p) = (T : ℝ) ^ (betaExp p) * (qBase p) ^ j := by
    unfold qBase
    rw [Real.div_rpow hT_pos.le (by positivity),
      ← Real.rpow_natCast ((2 : ℝ) ^ (-betaExp p)) j,
      ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) j,
      ← Real.rpow_mul (by norm_num),
      div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    congr 2
    ring
  rw [mul_assoc, ← hq_id]
  let N := T / 2 ^ j
  let M := T / 2 ^ (j + 1)
  have hMN : M = N / 2 := by
    dsimp [M, N]
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
  rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
  · have hM0 : M = 0 := by omega
    change (∑ i ∈ Finset.Ioc M N, (i : ℝ) ^ (-aExp p)) ≤ _
    rw [hM0, hN0, Finset.Ioc_self, Finset.sum_empty]
    positivity
  · rcases Nat.eq_zero_or_pos M with hM0 | hM_pos
    · have hN1 : N = 1 := by omega
      change (∑ i ∈ Finset.Ioc M N, (i : ℝ) ^ (-aExp p)) ≤ _
      rw [hM0, hN1]
      have hIoc01 : Finset.Ioc 0 1 = {1} := rfl
      rw [hIoc01, Finset.sum_singleton, Nat.cast_one, Real.one_rpow]
      have h2j_le_T : 2 ^ j ≤ T := by
        have hmul := Nat.div_mul_le_self T (2 ^ j)
        change N * 2 ^ j ≤ T at hmul
        rw [hN1, one_mul] at hmul
        exact hmul
      have hdiv_ge_one : 1 ≤ (T : ℝ) / (2 : ℝ) ^ j := by
        rw [le_div_iff₀ (by positivity)]
        have : ((2 ^ j : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast h2j_le_T
        simpa using this
      have hrpow_ge_one : 1 ≤ ((T : ℝ) / (2 : ℝ) ^ j) ^ (betaExp p) :=
        Real.one_le_rpow hdiv_ge_one (betaExp_pos hp).le
      linarith
    · change (∑ i ∈ Finset.Ioc M N, (i : ℝ) ^ (-aExp p)) ≤ _
      let X : ℝ := (T : ℝ) / (2 : ℝ) ^ (j + 1)
      have hX_pos : 0 < X := by dsimp [X]; positivity
      have hM_le_X : (M : ℝ) ≤ X := by
        dsimp [X]
        rw [le_div_iff₀ (by positivity)]
        have hmul := Nat.div_mul_le_self T (2 ^ (j + 1))
        change M * 2 ^ (j + 1) ≤ T at hmul
        exact_mod_cast hmul
      have hX_lt_M1 : X < ((M + 1 : ℕ) : ℝ) := by
        dsimp [X]
        rw [div_lt_iff₀ (by positivity)]
        have hlt : T < (M + 1) * 2 ^ (j + 1) := by
          dsimp [M]
          rw [mul_comm]
          exact Nat.lt_mul_div_succ T (by positivity : 0 < 2 ^ (j + 1))
        exact_mod_cast hlt
      have hterm_le : ∀ i ∈ Finset.Ioc M N, (i : ℝ) ^ (-aExp p) ≤ X ^ (-aExp p) := by
        intro i hi
        have hiM : M + 1 ≤ i := (Finset.mem_Ioc.mp hi).1
        have hXi : X ≤ (i : ℝ) := hX_lt_M1.le.trans (by exact_mod_cast hiM)
        exact Real.rpow_le_rpow_of_nonpos hX_pos hXi (neg_nonpos.mpr (aExp_pos hp).le)
      have hcard_le : ((N - M : ℕ) : ℝ) ≤ 2 * X := by
        have hsub : N - M ≤ 2 * M := by omega
        have hsub_r : ((N - M : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hsub
        linarith
      calc
        (∑ i ∈ Finset.Ioc M N, (i : ℝ) ^ (-aExp p))
          ≤ ∑ _i ∈ Finset.Ioc M N, X ^ (-aExp p) := Finset.sum_le_sum hterm_le
        _ = ((N - M : ℕ) : ℝ) * X ^ (-aExp p) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        _ ≤ (2 * X) * X ^ (-aExp p) :=
          mul_le_mul_of_nonneg_right hcard_le (Real.rpow_nonneg hX_pos.le _)
        _ = 2 * (X * X ^ (-aExp p)) := by ring
        _ = 2 * X ^ (betaExp p) := by
          congr 1
          calc
            X * X ^ (-aExp p) = X ^ (1 : ℝ) * X ^ (-aExp p) := by rw [Real.rpow_one]
            _ = X ^ (1 + -aExp p) := (Real.rpow_add hX_pos 1 (-aExp p)).symm
            _ = X ^ (betaExp p) := by
              congr 1
              have := aExp_add_betaExp hp
              linarith
        _ ≤ 2 * ((T : ℝ) / (2 : ℝ) ^ j) ^ (betaExp p) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.rpow_le_rpow hX_pos.le _ (betaExp_pos hp).le
          dsimp [X]
          apply div_le_div_of_nonneg_left hT_pos.le (by positivity)
          rw [pow_succ]
          linarith [ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j) ]

/-- Step sum on a single dyadic block:
`∑_{T / 2 ^ (j + 1) < i ≤ T / 2 ^ j} η_i ≤ 8 c T ^ β / ℓ_T² * q ^ j (j + 2)²`. -/
lemma sum_normStep_dyadic_block_le {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c)
    {T : ℕ} (hT : 1 ≤ T) (j : ℕ) :
    (∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j), normStep p c i) ≤
      (8 * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) *
        ((qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ)) := by
  calc
    (∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j), normStep p c i)
      ≤ ∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j),
          (4 * c * ((j : ℝ) + 2) ^ (2 : ℕ) / (ell T) ^ (2 : ℕ)) * (i : ℝ) ^ (-aExp p) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi_gt : T / 2 ^ (j + 1) < i := (Finset.mem_Ioc.mp hi).1
        have hi1 : 1 ≤ i := Nat.zero_lt_of_lt hi_gt
        rw [normStep_of_pos p c hi1]
        have hell_b := inv_ell_sq_le_dyadic hT hi_gt
        have htr_nn : 0 ≤ c * (i : ℝ) ^ (-aExp p) := by
          have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
          positivity
        calc
          c * (i : ℝ) ^ (-aExp p) / (ell i) ^ (2 : ℕ)
            = (c * (i : ℝ) ^ (-aExp p)) * (1 / (ell i) ^ (2 : ℕ)) := by ring
          _ ≤ (c * (i : ℝ) ^ (-aExp p)) *
                (4 * ((j : ℝ) + 2) ^ (2 : ℕ) / (ell T) ^ (2 : ℕ)) :=
              mul_le_mul_of_nonneg_left hell_b htr_nn
          _ = (4 * c * ((j : ℝ) + 2) ^ (2 : ℕ) / (ell T) ^ (2 : ℕ)) * (i : ℝ) ^ (-aExp p) := by
              ring
    _ = (4 * c * ((j : ℝ) + 2) ^ (2 : ℕ) / (ell T) ^ (2 : ℕ)) *
          ∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j), (i : ℝ) ^ (-aExp p) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * c * ((j : ℝ) + 2) ^ (2 : ℕ) / (ell T) ^ (2 : ℕ)) *
          (2 * (T : ℝ) ^ (betaExp p) * (qBase p) ^ j) := by
        apply mul_le_mul_of_nonneg_left (sum_rpow_dyadic_block_le hp hT j)
        have := ell_pos hT
        positivity
    _ = (8 * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) *
          ((qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ)) := by ring

/-- Sharper upper bound on the step sum:
`S_1 ≤ 8 J_β c T ^ β / ℓ_T²`. -/
lemma step_sum_upper_bound_J_beta {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {T : ℕ} (hT : 1 ≤ T) :
    Potential.tailSum (normStep p c) T 1 ≤
      8 * J_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hell_T : 0 < ell T := ell_pos hT
  unfold Potential.tailSum
  rw [Nat.max_self]
  have hIco_eq : Finset.Ico 1 (T + 1) = Finset.Ioc (T / 2 ^ T) T := by
    have hdiv0 : T / 2 ^ T = 0 := Nat.div_eq_of_lt T.lt_two_pow_self
    rw [hdiv0]
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hIco_eq, sum_Ioc_dyadic (normStep p c) T T]
  calc
    (∑ j ∈ Finset.range T, ∑ i ∈ Finset.Ioc (T / 2 ^ (j + 1)) (T / 2 ^ j), normStep p c i)
      ≤ ∑ j ∈ Finset.range T,
          (8 * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) *
            ((qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ)) := by
        apply Finset.sum_le_sum
        intro j _
        exact sum_normStep_dyadic_block_le hp hc hT j
    _ = (8 * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) *
          ∑ j ∈ Finset.range T, (qBase p) ^ j * ((j : ℝ) + 2) ^ (2 : ℕ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (8 * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) * J_beta p :=
        mul_le_mul_of_nonneg_left (dyadic_poly_sum_le hp T) (by positivity)
    _ = 8 * J_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) := by ring

/-- Upper bound on the step sum:
`S_1 ≤ H_β c T ^ β / ℓ_T²` (`eq:step-sum-anytime`). -/
lemma step_sum_upper_bound {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) {T : ℕ} (hT : 1 ≤ T) :
    Potential.tailSum (normStep p c) T 1 ≤
      H_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) := by
  refine (step_sum_upper_bound_J_beta hp hc hT).trans ?_
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hell_T : 0 < ell T := ell_pos hT
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h8J := eight_J_beta_le_H_beta hp
  have hmul : 0 ≤ c * (T : ℝ) ^ (betaExp p) := by positivity
  calc
    8 * J_beta p * c * (T : ℝ) ^ (betaExp p)
      = (8 * J_beta p) * (c * (T : ℝ) ^ (betaExp p)) := by ring
    _ ≤ H_beta p * (c * (T : ℝ) ^ (betaExp p)) := mul_le_mul_of_nonneg_right h8J hmul
    _ = H_beta p * c * (T : ℝ) ^ (betaExp p) := by ring

/-! ## 7. Tail Integrals (`eq:tail-integrals`) and Capped Budgets (`eq:capped-anytime-budgets`) -/

/-- Total capped step sum `U = 1 + S_1`. -/
def capU (p c : ℝ) (T : ℕ) : ℝ :=
  SuffixPotential.cappedTail (normStep p c) T 1

/-- Capped quadratic weight `Q_t = U η_t² / (1 + S_t)` (`eq:capped-Q`). -/
def capQ (p c : ℝ) (T t : ℕ) : ℝ :=
  capU p c T * (normStep p c t) ^ (2 : ℕ) /
    SuffixPotential.cappedTail (normStep p c) T t

lemma cappedTail_ge_one {p c : ℝ} (hc : 0 ≤ c) (T t : ℕ) :
    1 ≤ SuffixPotential.cappedTail (normStep p c) T t := by
  unfold SuffixPotential.cappedTail
  have : 0 ≤ Potential.tailSum (normStep p c) T t :=
    Potential.tailSum_nonneg (normStep p c) T t (fun i _ _ => normStep_nonneg hc i)
  linarith

lemma cappedTail_pos' {p c : ℝ} (hc : 0 ≤ c) (T t : ℕ) :
    0 < SuffixPotential.cappedTail (normStep p c) T t :=
  SuffixPotential.cappedTail_pos (normStep p c) T t (fun i _ _ => normStep_nonneg hc i)

lemma capU_ge_one {p c : ℝ} (hc : 0 ≤ c) (T : ℕ) : 1 ≤ capU p c T :=
  cappedTail_ge_one hc T 1

lemma capQ_nonneg {p c : ℝ} (hc : 0 ≤ c) (T t : ℕ) : 0 ≤ capQ p c T t := by
  unfold capQ
  have hU : 0 < capU p c T := lt_of_lt_of_le zero_lt_one (capU_ge_one hc T)
  have hden : 0 < SuffixPotential.cappedTail (normStep p c) T t := cappedTail_pos' hc T t
  positivity

lemma cappedTail_mono_left {p c : ℝ} (hc : 0 ≤ c) (T : ℕ) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s ≤ t) :
    SuffixPotential.cappedTail (normStep p c) T t ≤
      SuffixPotential.cappedTail (normStep p c) T s := by
  unfold SuffixPotential.cappedTail Potential.tailSum
  have hmax : max 1 s ≤ max 1 t := max_le_max le_rfl hst
  have hsub : Finset.Ico (max 1 t) (T + 1) ⊆ Finset.Ico (max 1 s) (T + 1) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi ⊢
    exact ⟨ hmax.trans hi.1, hi.2 ⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => normStep_nonneg (p := p) hc i)
  linarith

/-- On any suffix starting at `k ≥ 1`, `Q_t^{(k)} ≤ Q_t`. -/
lemma suffixQuadWeight_le_capQ {p c : ℝ} (hc : 0 ≤ c) (T k i : ℕ) (hk : 1 ≤ k) :
    SuffixPotential.suffixQuadWeight (normStep p c) T k i ≤ capQ p c T (k + i) := by
  unfold SuffixPotential.suffixQuadWeight capQ capU
  apply div_le_div_of_nonneg_right _ (cappedTail_pos' hc T (k + i)).le
  exact mul_le_mul_of_nonneg_right (cappedTail_mono_left hc T le_rfl hk) (sq_nonneg _)

/-- General telescoping identity on `Finset.Ico a (b + 1)`. -/
lemma sum_Ico_sub_eq (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b + 1) :
    (∑ t ∈ Finset.Ico a (b + 1), (g t - g (t + 1))) = g a - g (b + 1) := by
  induction b with
  | zero =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hab with rfl | rfl
    · have hIco : Finset.Ico 0 1 = {0} := rfl
      rw [hIco, Finset.sum_singleton]
    · simp
  | succ b ih =>
    by_cases hlt : a ≤ b + 1
    · rw [Finset.sum_Ico_succ_top hlt, ih hlt]
      ring
    · have heq : a = b + 2 := by omega
      subst heq
      simp

/-- One-step logarithmic bound `η_t / (1 + S_t) ≤ log(1 + S_t) - log(1 + S_{t+1})`. -/
lemma normStep_div_cappedTail_le_log_sub {p c : ℝ} (hc : 0 ≤ c) {T t : ℕ} (ht : t ≤ T) :
    normStep p c t / SuffixPotential.cappedTail (normStep p c) T t ≤
      Real.log (SuffixPotential.cappedTail (normStep p c) T t) -
        Real.log (SuffixPotential.cappedTail (normStep p c) T (t + 1)) := by
  let u_t := SuffixPotential.cappedTail (normStep p c) T t
  let u_next := SuffixPotential.cappedTail (normStep p c) T (t + 1)
  have hu_t : 0 < u_t := cappedTail_pos' hc T t
  have hu_next : 0 < u_next := cappedTail_pos' hc T (t + 1)
  have hrec : u_t = normStep p c t + u_next :=
    SuffixPotential.cappedTail_rec (normStep p c) T t (normStep_zero p c) ht
  have hexp := Real.add_one_le_exp (-(normStep p c t / u_t))
  have hdiv : u_next / u_t = -(normStep p c t / u_t) + 1 := by
    have : u_next = u_t - normStep p c t := by linarith
    rw [this]
    field_simp
    ring
  rw [← hdiv] at hexp
  have hlog := Real.log_le_log (div_pos hu_next hu_t) hexp
  rw [Real.log_exp, Real.log_div hu_next.ne' hu_t.ne'] at hlog
  linarith

/-- First tail integral bound `∑_{t=a}^T η_t / (1 + S_t) ≤ log U`
 (`eq:tail-integrals`). -/
lemma tail_sum_div_le_log {p c : ℝ} (hc : 0 ≤ c) {a T : ℕ} (ha : 1 ≤ a) (haT : a ≤ T + 1) :
    (∑ t ∈ Finset.Ico a (T + 1),
      normStep p c t / SuffixPotential.cappedTail (normStep p c) T t) ≤
        Real.log (capU p c T) := by
  let g : ℕ → ℝ := fun t => Real.log (SuffixPotential.cappedTail (normStep p c) T t)
  calc
    (∑ t ∈ Finset.Ico a (T + 1),
      normStep p c t / SuffixPotential.cappedTail (normStep p c) T t)
      ≤ ∑ t ∈ Finset.Ico a (T + 1), (g t - g (t + 1)) := by
        apply Finset.sum_le_sum
        intro t ht
        have htT : t ≤ T := by have := (Finset.mem_Ico.mp ht).2; omega
        exact normStep_div_cappedTail_le_log_sub hc htT
    _ = g a - g (T + 1) := sum_Ico_sub_eq g haT
    _ ≤ g 1 := by
        dsimp [g]
        have h1 : 0 ≤ Real.log (SuffixPotential.cappedTail (normStep p c) T (T + 1)) :=
          Real.log_nonneg (cappedTail_ge_one hc T (T + 1))
        have h2 : Real.log (SuffixPotential.cappedTail (normStep p c) T a) ≤
            Real.log (SuffixPotential.cappedTail (normStep p c) T 1) :=
          Real.log_le_log (cappedTail_pos' hc T a) (cappedTail_mono_left hc T le_rfl ha)
        linarith
    _ = Real.log (capU p c T) := rfl

/-- One-step square-root bound `η_t / √(1 + S_t) ≤ 2 (√(1 + S_t) - √(1 + S_{t+1}))`. -/
lemma normStep_div_sqrt_cappedTail_le_sub {p c : ℝ} (hc : 0 ≤ c) {T t : ℕ} (ht : t ≤ T) :
    normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t) ≤
      2 * Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t) -
        2 * Real.sqrt (SuffixPotential.cappedTail (normStep p c) T (t + 1)) := by
  let u_t := SuffixPotential.cappedTail (normStep p c) T t
  let u_next := SuffixPotential.cappedTail (normStep p c) T (t + 1)
  have hu_t : 0 < u_t := cappedTail_pos' hc T t
  have hu_next : 0 < u_next := cappedTail_pos' hc T (t + 1)
  have hrec : u_t = normStep p c t + u_next :=
    SuffixPotential.cappedTail_rec (normStep p c) T t (normStep_zero p c) ht
  have hstep_nn : 0 ≤ normStep p c t := normStep_nonneg hc t
  have hsqrt_le : Real.sqrt u_next ≤ Real.sqrt u_t :=
    Real.sqrt_le_sqrt (by linarith)
  have hdiff_sq : normStep p c t =
      (Real.sqrt u_t - Real.sqrt u_next) * (Real.sqrt u_t + Real.sqrt u_next) := by
    calc
      normStep p c t = u_t - u_next := by linarith
      _ = (Real.sqrt u_t) ^ (2 : ℕ) - (Real.sqrt u_next) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt hu_t.le, Real.sq_sqrt hu_next.le]
      _ = (Real.sqrt u_t - Real.sqrt u_next) * (Real.sqrt u_t + Real.sqrt u_next) := by ring
  have hle_mul : normStep p c t ≤
      (2 * Real.sqrt u_t - 2 * Real.sqrt u_next) * Real.sqrt u_t := by
    rw [hdiff_sq]
    nlinarith
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hu_t)).mpr hle_mul

/-- Second tail integral bound `∑_{t=a}^T η_t / √(1 + S_t) ≤ 2 (√U - 1)`
 (`eq:tail-integrals`). -/
lemma tail_sum_div_sqrt_le {p c : ℝ} (hc : 0 ≤ c) {a T : ℕ} (ha : 1 ≤ a) (haT : a ≤ T + 1) :
    (∑ t ∈ Finset.Ico a (T + 1),
      normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)) ≤
        2 * (Real.sqrt (capU p c T) - 1) := by
  let g : ℕ → ℝ := fun t => 2 * Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)
  calc
    (∑ t ∈ Finset.Ico a (T + 1),
      normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t))
      ≤ ∑ t ∈ Finset.Ico a (T + 1), (g t - g (t + 1)) := by
        apply Finset.sum_le_sum
        intro t ht
        have htT : t ≤ T := by have := (Finset.mem_Ico.mp ht).2; omega
        exact normStep_div_sqrt_cappedTail_le_sub hc htT
    _ = g a - g (T + 1) := sum_Ico_sub_eq g haT
    _ ≤ 2 * (Real.sqrt (capU p c T) - 1) := by
        dsimp [g]
        have h1 : 1 ≤ Real.sqrt (SuffixPotential.cappedTail (normStep p c) T (T + 1)) := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (cappedTail_ge_one hc T (T + 1))
        have h2 : Real.sqrt (SuffixPotential.cappedTail (normStep p c) T a) ≤
            Real.sqrt (capU p c T) :=
          Real.sqrt_le_sqrt (cappedTail_mono_left hc T le_rfl ha)
        linarith

/-- On the early half `1 ≤ t ≤ T / 2`, `U / (1 + S_t) ≤ 4 H_β`
. -/
lemma capU_div_cappedTail_early_le {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c)
    {T t : ℕ} (ht1 : 1 ≤ t) (ht_half : 2 * t ≤ T + 1) :
    capU p c T / SuffixPotential.cappedTail (normStep p c) T t ≤ 4 * H_beta p := by
  have hT1 : 1 ≤ T := by omega
  have hden_pos : 0 < SuffixPotential.cappedTail (normStep p c) T t := cappedTail_pos' hc T t
  rw [div_le_iff₀ hden_pos]
  unfold capU SuffixPotential.cappedTail
  have hlow := step_sum_lower_bound hp hc ht1 ht_half
  have hup := step_sum_upper_bound hp hc hT1
  have hS1_le : Potential.tailSum (normStep p c) T 1 ≤
      2 * H_beta p * Potential.tailSum (normStep p c) T t := by
    have hH_pos : 0 < H_beta p := H_beta_pos hp
    have hmul := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 * H_beta p)
    refine hup.trans (le_trans (le_of_eq ?_) hmul)
    ring
  have hH64 : 64 ≤ H_beta p := H_beta_ge_64 hp
  have hSt_nn : 0 ≤ Potential.tailSum (normStep p c) T t :=
    Potential.tailSum_nonneg (normStep p c) T t (fun i _ _ => normStep_nonneg hc i)
  nlinarith

/-- On the early half `1 ≤ t ≤ T / 2`, `Q_t ≤ 4 H_β η_t²` and `√Q_t ≤ 2 √H_β η_t`. -/
lemma capQ_early_le {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c)
    {T t : ℕ} (ht1 : 1 ≤ t) (ht_half : 2 * t ≤ T + 1) :
    capQ p c T t ≤ 4 * H_beta p * (normStep p c t) ^ (2 : ℕ) ∧
      Real.sqrt (capQ p c T t) ≤ 2 * Real.sqrt (H_beta p) * normStep p c t := by
  have hratio := capU_div_cappedTail_early_le hp hc ht1 ht_half
  have h1 : capQ p c T t ≤ 4 * H_beta p * (normStep p c t) ^ (2 : ℕ) := by
    unfold capQ
    calc
      capU p c T * (normStep p c t) ^ (2 : ℕ) / SuffixPotential.cappedTail (normStep p c) T t
        = (capU p c T / SuffixPotential.cappedTail (normStep p c) T t) *
            (normStep p c t) ^ (2 : ℕ) := by ring
      _ ≤ (4 * H_beta p) * (normStep p c t) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  refine ⟨ h1, ?_ ⟩
  have hsqrt := Real.sqrt_le_sqrt h1
  have hstep_nn : 0 ≤ normStep p c t := normStep_nonneg hc t
  have hH_nn : 0 ≤ H_beta p := (H_beta_pos hp).le
  have hrhs : Real.sqrt (4 * H_beta p * (normStep p c t) ^ (2 : ℕ)) =
      2 * Real.sqrt (H_beta p) * normStep p c t := by
    have hsq : 4 * H_beta p * (normStep p c t) ^ (2 : ℕ) =
        (2 * Real.sqrt (H_beta p) * normStep p c t) ^ (2 : ℕ) := by
      calc
        4 * H_beta p * (normStep p c t) ^ (2 : ℕ)
          = 4 * (Real.sqrt (H_beta p)) ^ (2 : ℕ) * (normStep p c t) ^ (2 : ℕ) := by
            rw [Real.sq_sqrt hH_nn]
        _ = (2 * Real.sqrt (H_beta p) * normStep p c t) ^ (2 : ℕ) := by ring
    rw [hsq, Real.sqrt_sq (by positivity)]
  rwa [hrhs] at hsqrt

/-- On the late half `T / 2 < t ≤ T`:
`B_t ≤ 4 T ^ (-β)`, `η_t V_t ≤ 64 c T ^ (-3β/2) / ℓ_T²`, and
`η_t² λ_t² ≤ 512 c² T ^ (-β) / ℓ_T⁴`. -/
lemma late_pointwise_bounds {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hc : 0 ≤ c)
    {T t : ℕ} (hT : 1 ≤ T) (ht_late : T / 2 < t) :
    normB p t ≤ 4 * (T : ℝ) ^ (-betaExp p) ∧
      normStep p c t * normV p t ≤
        64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ) ∧
      (normStep p c t) ^ (2 : ℕ) * (normLambda p t) ^ (2 : ℕ) ≤
        512 * c ^ (2 : ℕ) * (T : ℝ) ^ (-betaExp p) / (ell T) ^ (4 : ℕ) := by
  have ht1 : 1 ≤ t := Nat.zero_lt_of_lt ht_late
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT2_le_t : (T : ℝ) / 2 ≤ (t : ℝ) := by
    have : T < 2 * t := by omega
    have hlt : (T : ℝ) < 2 * (t : ℝ) := by exact_mod_cast this
    linarith
  have hT2_pos : 0 < (T : ℝ) / 2 := half_pos hT_pos
  have hb_pos : 0 < betaExp p := betaExp_pos hp
  have hb_le : betaExp p ≤ 2 / 5 := betaExp_le_two_fifths hp hp2
  -- First show `ℓ_T ≤ 2 ℓ_t` on the late half `T < 2 t`
  have hell_late : ell T ≤ 2 * ell t := by
    unfold ell
    have h2t : (T : ℝ) ≤ 2 * (t : ℝ) := by linarith
    have ht_ge1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
    have hsq_le : 100 * (T : ℝ) ^ (2 : ℕ) ≤ (100 * (t : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
      have h1 : (T : ℝ) ^ (2 : ℕ) ≤ 4 * (t : ℝ) ^ (2 : ℕ) := by
        calc
          (T : ℝ) ^ (2 : ℕ) ≤ (2 * (t : ℝ)) ^ (2 : ℕ) := by
            have : (0 : ℝ) ≤ (T : ℝ) := by positivity
            nlinarith [h2t]
          _ = 4 * (t : ℝ) ^ (2 : ℕ) := by ring
      have h2 : 100 * (T : ℝ) ^ (2 : ℕ) ≤ 400 * (t : ℝ) ^ (2 : ℕ) := by linarith [h1]
      have h3 : 400 * (t : ℝ) ^ (2 : ℕ) ≤ (100 * (t : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
        calc
          400 * (t : ℝ) ^ (2 : ℕ) = 400 * (t : ℝ) ^ (2 : ℕ) * 1 := (mul_one _).symm
          _ ≤ 400 * (t : ℝ) ^ (2 : ℕ) * (25 * (t : ℝ) ^ (2 : ℕ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have ht_sq : 1 ≤ (t : ℝ) ^ (2 : ℕ) := one_le_pow₀ ht_ge1
            linarith
          _ = (100 * (t : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      exact h2.trans h3
    have hlog := Real.log_le_log (by positivity) hsq_le
    rw [Real.log_pow] at hlog
    push_cast at hlog
    exact hlog
  have hell_t_pos : 0 < ell t := ell_pos ht1
  have hell_T_pos : 0 < ell T := ell_pos hT
  have hell_sq_le : 1 / (ell t) ^ (2 : ℕ) ≤ 4 / (ell T) ^ (2 : ℕ) := by
    have hsq : (ell T) ^ (2 : ℕ) ≤ (2 * ell t) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hell_T_pos.le hell_late 2
    rw [div_le_div_iff₀ (pow_pos hell_t_pos 2) (pow_pos hell_T_pos 2)]
    nlinarith
  have hell_pow4_le : 1 / (ell t) ^ (4 : ℕ) ≤ 16 / (ell T) ^ (4 : ℕ) := by
    have h4 : (ell T) ^ (4 : ℕ) ≤ (2 * ell t) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hell_T_pos.le hell_late 4
    rw [div_le_div_iff₀ (pow_pos hell_t_pos 4) (pow_pos hell_T_pos 4)]
    nlinarith
  have hrpow_beta : (t : ℝ) ^ (-betaExp p) ≤ 2 * (T : ℝ) ^ (-betaExp p) := by
    have h1 : (t : ℝ) ^ (-betaExp p) ≤ ((T : ℝ) / 2) ^ (-betaExp p) :=
      Real.rpow_le_rpow_of_nonpos hT2_pos hT2_le_t (neg_nonpos.mpr hb_pos.le)
    have h2 : ((T : ℝ) / 2) ^ (-betaExp p) = (2 : ℝ) ^ (betaExp p) * (T : ℝ) ^ (-betaExp p) := by
      rw [div_eq_mul_inv, Real.mul_rpow hT_pos.le (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg, mul_comm]
    have h3 : (2 : ℝ) ^ (betaExp p) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h3
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hT_pos.le _))
  have hrpow_3beta : (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) ≤
      2 * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) := by
    have h1 : (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) ≤
        ((T : ℝ) / 2) ^ (-(3 / 2 : ℝ) * betaExp p) :=
      Real.rpow_le_rpow_of_nonpos hT2_pos hT2_le_t (by linarith)
    have h2 : ((T : ℝ) / 2) ^ (-(3 / 2 : ℝ) * betaExp p) =
        (2 : ℝ) ^ ((3 / 2 : ℝ) * betaExp p) * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) := by
      have : (-(3 / 2 : ℝ) * betaExp p) = -((3 / 2 : ℝ) * betaExp p) := by ring
      rw [this, div_eq_mul_inv, Real.mul_rpow hT_pos.le (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg, mul_comm]
    have h3 : (2 : ℝ) ^ ((3 / 2 : ℝ) * betaExp p) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h3
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hT_pos.le _))
  refine ⟨ ?_, ?_, ?_ ⟩
  · calc
      normB p t ≤ 2 * (t : ℝ) ^ (-betaExp p) := normB_le hp ht1
      _ ≤ 2 * (2 * (T : ℝ) ^ (-betaExp p)) := mul_le_mul_of_nonneg_left hrpow_beta (by norm_num)
      _ = 4 * (T : ℝ) ^ (-betaExp p) := by ring
  · have hV := normV_le hp ht1
    have hstep_nn : 0 ≤ normStep p c t := normStep_nonneg hc t
    have hrpow_id : (t : ℝ) ^ (-aExp p) * (t : ℝ) ^ (vExp p) =
        (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) := by
      rw [← Real.rpow_add ht_pos]
      congr 1
      have := aExp_sub_vExp (p := p)
      linarith
    have hid : c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ) * (8 * (t : ℝ) ^ (vExp p)) =
        (8 * c * (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p)) * (1 / (ell t) ^ (2 : ℕ)) := by
      calc
        c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ) * (8 * (t : ℝ) ^ (vExp p))
          = 8 * c * ((t : ℝ) ^ (-aExp p) * (t : ℝ) ^ (vExp p)) * (1 / (ell t) ^ (2 : ℕ)) := by
            ring
        _ = (8 * c * (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p)) * (1 / (ell t) ^ (2 : ℕ)) := by
            rw [hrpow_id]
    have hmul1 : normStep p c t * normV p t ≤
        (8 * c * (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p)) * (1 / (ell t) ^ (2 : ℕ)) := by
      calc
        normStep p c t * normV p t ≤ normStep p c t * (8 * (t : ℝ) ^ (vExp p)) :=
          mul_le_mul_of_nonneg_left hV hstep_nn
        _ = (c * (t : ℝ) ^ (-aExp p) / (ell t) ^ (2 : ℕ)) * (8 * (t : ℝ) ^ (vExp p)) := by
          rw [normStep_of_pos p c ht1]
        _ = (8 * c * (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p)) * (1 / (ell t) ^ (2 : ℕ)) := hid
    have hmul2 : (8 * c * (t : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p)) * (1 / (ell t) ^ (2 : ℕ)) ≤
        (8 * c * (2 * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p))) * (4 / (ell T) ^ (2 : ℕ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hrpow_3beta (by positivity)
      · exact hell_sq_le
      · positivity
      · positivity
    have h64 : (8 * c * (2 * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p))) * (4 / (ell T) ^ (2 : ℕ)) =
        64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ) := by ring
    exact (hmul1.trans hmul2).trans_eq h64
  · rw [normStep_sq_mul_normLambda_sq ht1]
    calc
      16 * c ^ (2 : ℕ) * (t : ℝ) ^ (-betaExp p) / (ell t) ^ (4 : ℕ)
        = (16 * c ^ (2 : ℕ) * (t : ℝ) ^ (-betaExp p)) * (1 / (ell t) ^ (4 : ℕ)) := by ring
      _ ≤ (16 * c ^ (2 : ℕ) * (2 * (T : ℝ) ^ (-betaExp p))) * (16 / (ell T) ^ (4 : ℕ)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hrpow_beta (by positivity)
          · exact hell_pow4_le
          · positivity
          · positivity
      _ = 512 * c ^ (2 : ℕ) * (T : ℝ) ^ (-betaExp p) / (ell T) ^ (4 : ℕ) := by ring

/-- Logarithmic bound on `U = 1 + S_1`: for `0 ≤ c ≤ 1` and `1 ≤ T`,
`U * log U ≤ 2 H_β² c T ^ β / ℓ_T`. -/
lemma capU_mul_log_capU_le {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {T : ℕ} (hT : 1 ≤ T) :
    capU p c T * Real.log (capU p c T) ≤
      2 * (H_beta p) ^ (2 : ℕ) * c * (T : ℝ) ^ (betaExp p) / ell T := by
  let S₁ := Potential.tailSum (normStep p c) T 1
  have hS1_nn : 0 ≤ S₁ :=
    Potential.tailSum_nonneg (normStep p c) T 1 (fun i _ _ => normStep_nonneg hc i)
  have hS1_up : S₁ ≤ H_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) :=
    step_sum_upper_bound hp hc hT
  have hU_eq : capU p c T = 1 + S₁ := rfl
  -- Step 1: `log(1 + S₁) ≤ S₁`
  have hlog_le_S1 : Real.log (capU p c T) ≤ S₁ := by
    have hpos : (0 : ℝ) < 1 + S₁ := by linarith [hS1_nn]
    have h1 := Real.log_le_sub_one_of_pos hpos
    have hsub : 1 + S₁ - 1 = S₁ := by ring
    rw [hsub] at h1
    change Real.log (1 + S₁) ≤ S₁
    exact h1
  have hlog_nn : 0 ≤ Real.log (capU p c T) :=
    Real.log_nonneg (capU_ge_one (p := p) hc T)
  -- Step 2: `U * log U = log U + S₁ * log U ≤ S₁ * (1 + log U)`
  have hU_log_le : capU p c T * Real.log (capU p c T) ≤ S₁ * (1 + Real.log (capU p c T)) := by
    calc
      capU p c T * Real.log (capU p c T)
        = Real.log (capU p c T) + S₁ * Real.log (capU p c T) := by rw [hU_eq]; ring
      _ ≤ S₁ + S₁ * Real.log (capU p c T) := add_le_add_right hlog_le_S1 _
      _ = S₁ * (1 + Real.log (capU p c T)) := by ring
  -- Step 3: `1 + log U ≤ 2 H_β ℓ_T`
  have h1_add_log_le : 1 + Real.log (capU p c T) ≤ 2 * H_beta p * ell T := by
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hb_le : betaExp p ≤ 2 / 5 := betaExp_le_two_fifths hp hp2
    have hT_rpow_le : (T : ℝ) ^ (betaExp p) ≤ (T : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (T : ℝ) 2]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
    have hell_T_gt4 : 4 < ell T := four_lt_ell hT
    have hS1_rough : S₁ ≤ H_beta p * (T : ℝ) ^ (2 : ℕ) := by
      have h1 : H_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) ≤
          H_beta p * 1 * (T : ℝ) ^ (2 : ℕ) / 1 := by
        apply div_le_div₀ (by have := H_beta_pos hp; positivity)
        · apply mul_le_mul (mul_le_mul_of_nonneg_left hc1 (H_beta_pos hp).le) hT_rpow_le
          · positivity
          · have := H_beta_pos hp; positivity
        · exact zero_lt_one
        · nlinarith
      exact hS1_up.trans (by linarith)
    have hU_rough : capU p c T ≤ H_beta p * (100 * (T : ℝ) ^ (2 : ℕ)) := by
      rw [hU_eq]
      have hH64 : 64 ≤ H_beta p := H_beta_ge_64 hp
      have hT2_ge1 : 1 ≤ (T : ℝ) ^ (2 : ℕ) := one_le_pow₀ hT1
      nlinarith
    have hlog_U_le : Real.log (capU p c T) ≤ Real.log (H_beta p) + ell T := by
      unfold ell
      rw [← Real.log_mul (H_beta_pos hp).ne' (by positivity)]
      exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (capU_ge_one hc T)) hU_rough
    have hlog_H_le : Real.log (H_beta p) ≤ H_beta p := by
      have h := Real.log_le_sub_one_of_pos (H_beta_pos hp)
      linarith
    have hH64 : 64 ≤ H_beta p := H_beta_ge_64 hp
    nlinarith
  -- Combine Steps 2 and 3
  have hell_T_pos : 0 < ell T := ell_pos hT
  calc
    capU p c T * Real.log (capU p c T)
      ≤ S₁ * (1 + Real.log (capU p c T)) := hU_log_le
    _ ≤ (H_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) *
          (2 * H_beta p * ell T) := by
        apply mul_le_mul hS1_up h1_add_log_le (by linarith)
        have := H_beta_pos hp; positivity
    _ = 2 * (H_beta p) ^ (2 : ℕ) * c * (T : ℝ) ^ (betaExp p) / ell T := by
        field_simp; ring

/-- Partition of `Finset.Ico 1 (T + 1)` into early half `Finset.Ico 1 (T / 2 + 1)` and
late half `Finset.Ico (T / 2 + 1) (T + 1)`. -/
lemma sum_Ico_split_half (f : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Ico 1 (T + 1), f t) =
      (∑ t ∈ Finset.Ico 1 (T / 2 + 1), f t) +
        (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), f t) := by
  exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm

/-- Capped anytime bias budget `∑_{t=1}^T √Q_t B_t ≤ K c / ℓ_1`
 (`eq:capped-anytime-budgets`). -/
lemma capped_bias_sum_le {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hc : 0 ≤ c)
    {T : ℕ} (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Ico 1 (T + 1), Real.sqrt (capQ p c T t) * normB p t) ≤
      K_const p * c / ell 1 := by
  rw [sum_Ico_split_half _ hT]
  have hell1_pos : 0 < ell 1 := ell_pos le_rfl
  have hellT_pos : 0 < ell T := ell_pos hT
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- Early half bound: `≤ 4 √H_β c / ℓ_1`
  have hearly : (∑ t ∈ Finset.Ico 1 (T / 2 + 1), Real.sqrt (capQ p c T t) * normB p t) ≤
      4 * Real.sqrt (H_beta p) * c / ell 1 := by
    have hle1 : (∑ t ∈ Finset.Ico 1 (T / 2 + 1), Real.sqrt (capQ p c T t) * normB p t) ≤
        2 * Real.sqrt (H_beta p) *
          ∑ t ∈ Finset.Ico 1 (T / 2 + 1), normStep p c t * normB p t := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have ht_b := Finset.mem_Ico.mp ht
      have hq := (capQ_early_le (T := T) hp hc ht_b.1 (by omega)).2
      calc
        Real.sqrt (capQ p c T t) * normB p t
          ≤ (2 * Real.sqrt (H_beta p) * normStep p c t) * normB p t :=
            mul_le_mul_of_nonneg_right hq (normB_nonneg p t)
        _ = 2 * Real.sqrt (H_beta p) * (normStep p c t * normB p t) := by ring
    have hreindex : (∑ t ∈ Finset.Ico 1 (T / 2 + 1), normStep p c t * normB p t) =
        ∑ i ∈ Finset.range (T / 2), normStep p c (i + 1) * normB p (i + 1) := by
      simpa [add_comm] using Finset.sum_Ico_eq_sum_range (fun t => normStep p c t * normB p t) 1 (T / 2 + 1)
    have hsum_le : (∑ i ∈ Finset.range (T / 2), normStep p c (i + 1) * normB p (i + 1)) ≤
        2 * c / ell 1 := by
      calc
        (∑ i ∈ Finset.range (T / 2), normStep p c (i + 1) * normB p (i + 1))
          ≤ ∑ i ∈ Finset.range (T / 2),
              2 * c / (((i + 1 : ℕ) : ℝ) * (ell (i + 1)) ^ (2 : ℕ)) :=
            Finset.sum_le_sum (fun i _ => normStep_mul_normB_le hp hc (by omega))
        _ = 2 * c * ∑ i ∈ Finset.range (T / 2),
              1 / (((i + 1 : ℕ) : ℝ) * (ell (i + 1)) ^ (2 : ℕ)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        _ ≤ 2 * c * (1 / ell 1) :=
            mul_le_mul_of_nonneg_left (sum_inv_t_ell_sq_le (T / 2)) (by positivity)
        _ = 2 * c / ell 1 := by ring
    rw [hreindex] at hle1
    calc
      (∑ t ∈ Finset.Ico 1 (T / 2 + 1), Real.sqrt (capQ p c T t) * normB p t)
        ≤ 2 * Real.sqrt (H_beta p) * (2 * c / ell 1) :=
          hle1.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
      _ = 4 * Real.sqrt (H_beta p) * c / ell 1 := by ring
  -- Late half bound: `≤ 8 H_β c / ℓ_1`
  have hlate : (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), Real.sqrt (capQ p c T t) * normB p t) ≤
      8 * H_beta p * c / ell 1 := by
    have hsqrt_Q : ∀ t ∈ Finset.Ico (T / 2 + 1) (T + 1),
        Real.sqrt (capQ p c T t) =
          Real.sqrt (capU p c T) *
            (normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)) := by
      intro t _
      unfold capQ
      have hU_nn : 0 ≤ capU p c T := (lt_of_lt_of_le zero_lt_one (capU_ge_one hc T)).le
      have hstep_nn : 0 ≤ normStep p c t := normStep_nonneg hc t
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul hU_nn, Real.sqrt_sq hstep_nn,
        mul_div_assoc]
    have hle1 : (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), Real.sqrt (capQ p c T t) * normB p t) ≤
        (4 * (T : ℝ) ^ (-betaExp p) * Real.sqrt (capU p c T)) *
          ∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1),
            normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have ht_b := Finset.mem_Ico.mp ht
      have hB := (late_pointwise_bounds (T := T) (t := t) hp hp2 hc hT (by omega)).1
      have hstep : Real.sqrt (capQ p c T t) * normB p t ≤
          (4 * (T : ℝ) ^ (-betaExp p) * Real.sqrt (capU p c T)) *
            (normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)) := by
        rw [hsqrt_Q t ht]
        calc
          Real.sqrt (capU p c T) * (normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)) * normB p t
            ≤ Real.sqrt (capU p c T) * (normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)) *
                (4 * (T : ℝ) ^ (-betaExp p)) := by
                apply mul_le_mul_of_nonneg_left hB
                have : 0 ≤ normStep p c t := normStep_nonneg hc t
                positivity
          _ = (4 * (T : ℝ) ^ (-betaExp p) * Real.sqrt (capU p c T)) *
                (normStep p c t / Real.sqrt (SuffixPotential.cappedTail (normStep p c) T t)) := by ring
      exact hstep
    have htail := tail_sum_div_sqrt_le (p := p) hc (a := T / 2 + 1) (T := T) (by omega) (by omega)
    have hU_sub : Real.sqrt (capU p c T) * (Real.sqrt (capU p c T) - 1) ≤
        Potential.tailSum (normStep p c) T 1 := by
      have hU1 : 1 ≤ Real.sqrt (capU p c T) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (capU_ge_one hc T)
      have hsq : (Real.sqrt (capU p c T)) ^ (2 : ℕ) = 1 + Potential.tailSum (normStep p c) T 1 :=
        Real.sq_sqrt (lt_of_lt_of_le zero_lt_one (capU_ge_one hc T)).le
      nlinarith
    have hS1 := step_sum_upper_bound hp hc hT
    have hrpow_cancel : (T : ℝ) ^ (-betaExp p) * (T : ℝ) ^ (betaExp p) = 1 := by
      rw [← Real.rpow_add hT_pos, neg_add_cancel, Real.rpow_zero]
    have hcomb : (4 * (T : ℝ) ^ (-betaExp p) * Real.sqrt (capU p c T)) *
        (2 * (Real.sqrt (capU p c T) - 1)) ≤ 8 * H_beta p * c / (ell T) ^ (2 : ℕ) := by
      calc
        (4 * (T : ℝ) ^ (-betaExp p) * Real.sqrt (capU p c T)) *
            (2 * (Real.sqrt (capU p c T) - 1))
          = 8 * (T : ℝ) ^ (-betaExp p) *
              (Real.sqrt (capU p c T) * (Real.sqrt (capU p c T) - 1)) := by ring
        _ ≤ 8 * (T : ℝ) ^ (-betaExp p) *
              (H_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) := by
            apply mul_le_mul_of_nonneg_left (hU_sub.trans hS1) (by positivity)
        _ = 8 * H_beta p * c * ((T : ℝ) ^ (-betaExp p) * (T : ℝ) ^ (betaExp p)) /
              (ell T) ^ (2 : ℕ) := by ring
        _ = 8 * H_beta p * c / (ell T) ^ (2 : ℕ) := by rw [hrpow_cancel, mul_one]
    have hell_le : ell 1 ≤ (ell T) ^ (2 : ℕ) := by
      have h1 : ell 1 ≤ ell T := ell_mono le_rfl hT
      have h4 : 4 < ell T := four_lt_ell hT
      nlinarith
    calc
      (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), Real.sqrt (capQ p c T t) * normB p t)
        ≤ (4 * (T : ℝ) ^ (-betaExp p) * Real.sqrt (capU p c T)) *
            (2 * (Real.sqrt (capU p c T) - 1)) :=
          hle1.trans (mul_le_mul_of_nonneg_left htail (by positivity))
      _ ≤ 8 * H_beta p * c / (ell T) ^ (2 : ℕ) := hcomb
      _ ≤ 8 * H_beta p * c / ell 1 :=
          div_le_div_of_nonneg_left (by have := H_beta_pos hp; positivity) hell1_pos hell_le
  -- Combine early and late halves
  have hsqrt_H : Real.sqrt (H_beta p) ≤ H_beta p := by
    have hH1 : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
    have hsq : (Real.sqrt (H_beta p)) ^ (2 : ℕ) = H_beta p := Real.sq_sqrt (by linarith)
    have hge1 : 1 ≤ Real.sqrt (H_beta p) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hH1
    nlinarith
  have h12H_le_K : 12 * H_beta p ≤ K_const p := by
    unfold K_const
    have hH1 : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
    have hH3 : 1 ≤ (H_beta p) ^ (3 : ℕ) := one_le_pow₀ hH1
    calc
      12 * H_beta p ≤ (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (3 : ℕ) * H_beta p := by nlinarith
      _ = (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (4 : ℕ) := by ring
  calc
    (∑ t ∈ Finset.Ico 1 (T / 2 + 1), Real.sqrt (capQ p c T t) * normB p t) +
        (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), Real.sqrt (capQ p c T t) * normB p t)
      ≤ 4 * Real.sqrt (H_beta p) * c / ell 1 + 8 * H_beta p * c / ell 1 :=
        add_le_add hearly hlate
    _ = (4 * Real.sqrt (H_beta p) + 8 * H_beta p) * c / ell 1 := by ring
    _ ≤ (12 * H_beta p) * c / ell 1 := by
        apply div_le_div_of_nonneg_right _ hell1_pos.le
        exact mul_le_mul_of_nonneg_right (by linarith) hc
    _ ≤ K_const p * c / ell 1 := by
        apply div_le_div_of_nonneg_right _ hell1_pos.le
        exact mul_le_mul_of_nonneg_right h12H_le_K hc

/-- Capped anytime variance budget `∑_{t=1}^T Q_t V_t ≤ K c² / ℓ_1³`
 (`eq:capped-anytime-budgets`). -/
lemma capped_variance_sum_le {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {T : ℕ} (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Ico 1 (T + 1), capQ p c T t * normV p t) ≤
      K_const p * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
  rw [sum_Ico_split_half _ hT]
  have hell1_pos : 0 < ell 1 := ell_pos le_rfl
  have hellT_pos : 0 < ell T := ell_pos hT
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  -- Early half bound: `≤ 4 H_β² c² / ℓ_1³`
  have hearly : (∑ t ∈ Finset.Ico 1 (T / 2 + 1), capQ p c T t * normV p t) ≤
      4 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
    have hle1 : (∑ t ∈ Finset.Ico 1 (T / 2 + 1), capQ p c T t * normV p t) ≤
        4 * H_beta p *
          ∑ t ∈ Finset.Ico 1 (T / 2 + 1), (normStep p c t) ^ (2 : ℕ) * normV p t := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have ht_b := Finset.mem_Ico.mp ht
      have hq := (capQ_early_le (T := T) hp hc ht_b.1 (by omega)).1
      calc
        capQ p c T t * normV p t
          ≤ (4 * H_beta p * (normStep p c t) ^ (2 : ℕ)) * normV p t :=
            mul_le_mul_of_nonneg_right hq (normV_nonneg p t)
        _ = 4 * H_beta p * ((normStep p c t) ^ (2 : ℕ) * normV p t) := by ring
    have hreindex : (∑ t ∈ Finset.Ico 1 (T / 2 + 1), (normStep p c t) ^ (2 : ℕ) * normV p t) =
        ∑ i ∈ Finset.range (T / 2), (normStep p c (i + 1)) ^ (2 : ℕ) * normV p (i + 1) := by
      simpa [add_comm] using Finset.sum_Ico_eq_sum_range
        (fun t => (normStep p c t) ^ (2 : ℕ) * normV p t) 1 (T / 2 + 1)
    rw [hreindex] at hle1
    have hglob := global_variance_sum_le_H_beta hp (c := c) (T / 2)
    have hell3_le_4 : (ell 1) ^ (3 : ℕ) ≤ (ell 1) ^ (4 : ℕ) := by
      have : 1 ≤ ell 1 := (one_lt_ell_one).le
      exact pow_le_pow_right₀ this (by omega)
    calc
      (∑ t ∈ Finset.Ico 1 (T / 2 + 1), capQ p c T t * normV p t)
        ≤ 4 * H_beta p * (H_beta p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) :=
          hle1.trans (mul_le_mul_of_nonneg_left hglob (by have := H_beta_pos hp; positivity))
      _ = 4 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring
      _ ≤ 4 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hell1_pos 3) hell3_le_4
  -- Late half bound: `≤ 128 H_β² c² / ℓ_1³`
  have hlate : (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), capQ p c T t * normV p t) ≤
      128 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
    have hle1 : (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), capQ p c T t * normV p t) ≤
        (64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ) * capU p c T) *
          ∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1),
            normStep p c t / SuffixPotential.cappedTail (normStep p c) T t := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      have ht_b := Finset.mem_Ico.mp ht
      have hV := (late_pointwise_bounds (T := T) (t := t) hp hp2 hc hT (by omega)).2.1
      unfold capQ
      have hfac_nn : 0 ≤ capU p c T *
          (normStep p c t / SuffixPotential.cappedTail (normStep p c) T t) := by
        have := capU_ge_one (p := p) hc T
        have := cappedTail_pos' (p := p) hc T t
        have := normStep_nonneg (p := p) hc t
        positivity
      calc
        capU p c T * (normStep p c t) ^ (2 : ℕ) /
            SuffixPotential.cappedTail (normStep p c) T t * normV p t
          = (capU p c T * (normStep p c t / SuffixPotential.cappedTail (normStep p c) T t)) *
              (normStep p c t * normV p t) := by ring
        _ ≤ (capU p c T * (normStep p c t / SuffixPotential.cappedTail (normStep p c) T t)) *
              (64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hV hfac_nn
        _ = (64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ) * capU p c T) *
              (normStep p c t / SuffixPotential.cappedTail (normStep p c) T t) := by ring
    have htail := tail_sum_div_le_log (p := p) hc (a := T / 2 + 1) (T := T) (by omega) (by omega)
    have hUlog := capU_mul_log_capU_le hp hp2 hc hc1 hT
    have hrpow_le1 : (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) * (T : ℝ) ^ (betaExp p) ≤ 1 := by
      rw [← Real.rpow_add hT_pos]
      apply Real.rpow_le_one_of_one_le_of_nonpos hT1
      have := betaExp_pos hp
      linarith
    have hell_mono3 : (ell 1) ^ (3 : ℕ) ≤ (ell T) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hell1_pos.le (ell_mono le_rfl hT) 3
    have hpos_factor : 0 ≤ 64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ) * capU p c T := by
      have hU : 0 ≤ capU p c T := (capU_ge_one (p := p) hc T).trans' zero_le_one
      positivity
    calc
      (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), capQ p c T t * normV p t)
        ≤ (64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ) * capU p c T) *
            Real.log (capU p c T) :=
          hle1.trans (mul_le_mul_of_nonneg_left htail hpos_factor)
      _ = (64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ)) *
            (capU p c T * Real.log (capU p c T)) := by ring
      _ ≤ (64 * c * (T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) / (ell T) ^ (2 : ℕ)) *
            (2 * (H_beta p) ^ (2 : ℕ) * c * (T : ℝ) ^ (betaExp p) / ell T) :=
          mul_le_mul_of_nonneg_left hUlog (by positivity)
      _ = (128 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell T) ^ (3 : ℕ)) *
            ((T : ℝ) ^ (-(3 / 2 : ℝ) * betaExp p) * (T : ℝ) ^ (betaExp p)) := by ring
      _ ≤ (128 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell T) ^ (3 : ℕ)) * 1 :=
          mul_le_mul_of_nonneg_left hrpow_le1 (by positivity)
      _ = 128 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell T) ^ (3 : ℕ) := by ring
      _ ≤ 128 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hell1_pos 3) hell_mono3
  -- Combine early and late halves
  have h132_le_K : 132 * (H_beta p) ^ (2 : ℕ) ≤ K_const p := by
    unfold K_const
    have hH1 : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
    have hH2 : 1 ≤ (H_beta p) ^ (2 : ℕ) := one_le_pow₀ hH1
    calc
      132 * (H_beta p) ^ (2 : ℕ)
        ≤ (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (2 : ℕ) * (H_beta p) ^ (2 : ℕ) := by nlinarith
      _ = (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (4 : ℕ) := by ring
  calc
    (∑ t ∈ Finset.Ico 1 (T / 2 + 1), capQ p c T t * normV p t) +
        (∑ t ∈ Finset.Ico (T / 2 + 1) (T + 1), capQ p c T t * normV p t)
      ≤ 4 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) +
          128 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) :=
        add_le_add hearly hlate
    _ = 132 * (H_beta p) ^ (2 : ℕ) * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by ring
    _ ≤ K_const p * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right h132_le_K (sq_nonneg c)

/-- Capped anytime range budget `Q_t λ_t² ≤ K c² / ℓ_1⁴` for `1 ≤ t ≤ T`
 (`eq:capped-anytime-budgets`). -/
lemma capped_range_le {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {T t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ T) :
    capQ p c T t * (normLambda p t) ^ (2 : ℕ) ≤
      K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  have hT : 1 ≤ T := ht1.trans htT
  have hell1_pos : 0 < ell 1 := ell_pos le_rfl
  by_cases hhalf : 2 * t ≤ T + 1
  · -- Early half `2 t ≤ T + 1`: `Q_t λ_t² ≤ 64 H_β c² / ℓ_1⁴`
    have hq := (capQ_early_le hp hc ht1 hhalf).1
    have hstep_lam := normStep_mul_normLambda_le hp hc ht1
    have hsq_lam : (normStep p c t) ^ (2 : ℕ) * (normLambda p t) ^ (2 : ℕ) ≤
        16 * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
      have hprod_nn : 0 ≤ normStep p c t * normLambda p t :=
        mul_nonneg (normStep_nonneg hc t) (normLambda_pos hp ht1).le
      have hsq := pow_le_pow_left₀ hprod_nn hstep_lam 2
      calc
        (normStep p c t) ^ (2 : ℕ) * (normLambda p t) ^ (2 : ℕ)
          = (normStep p c t * normLambda p t) ^ (2 : ℕ) := (mul_pow _ _ 2).symm
        _ ≤ (4 * c / (ell 1) ^ (2 : ℕ)) ^ (2 : ℕ) := hsq
        _ = 16 * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring
    have h64_le_K : 64 * H_beta p ≤ K_const p := by
      unfold K_const
      have hH1 : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
      have hH3 : 1 ≤ (H_beta p) ^ (3 : ℕ) := one_le_pow₀ hH1
      calc
        64 * H_beta p ≤ (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (3 : ℕ) * H_beta p := by nlinarith
        _ = (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (4 : ℕ) := by ring
    calc
      capQ p c T t * (normLambda p t) ^ (2 : ℕ)
        ≤ (4 * H_beta p * (normStep p c t) ^ (2 : ℕ)) * (normLambda p t) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hq (sq_nonneg _)
      _ = 4 * H_beta p * ((normStep p c t) ^ (2 : ℕ) * (normLambda p t) ^ (2 : ℕ)) := by ring
      _ ≤ 4 * H_beta p * (16 * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left hsq_lam (by have := H_beta_pos hp; positivity)
      _ = (64 * H_beta p) * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring
      _ ≤ K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right h64_le_K (sq_nonneg c)
  · -- Late half `T / 2 < t ≤ T`: `Q_t λ_t² ≤ 1024 H_β c² / ℓ_1⁴`
    have ht_late : T / 2 < t := by omega
    have hlam := (late_pointwise_bounds hp hp2 hc hT ht_late).2.2
    have hU_over_den : capU p c T / SuffixPotential.cappedTail (normStep p c) T t ≤ capU p c T :=
      div_le_self (lt_of_lt_of_le zero_lt_one (capU_ge_one hc T)).le (cappedTail_ge_one hc T t)
    have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hrpow_cancel : (T : ℝ) ^ (-betaExp p) * (T : ℝ) ^ (betaExp p) = 1 := by
      rw [← Real.rpow_add hT_pos, neg_add_cancel, Real.rpow_zero]
    have hrpow_le1 : (T : ℝ) ^ (-betaExp p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hT1 (neg_nonpos.mpr (betaExp_pos hp).le)
    have hS1 := step_sum_upper_bound hp hc hT
    have hellT_ge1 : 1 ≤ (ell T) ^ (2 : ℕ) := by
      have := four_lt_ell hT; nlinarith
    have hU_mul : capU p c T * (T : ℝ) ^ (-betaExp p) ≤ 2 * H_beta p := by
      unfold capU SuffixPotential.cappedTail
      have h1 : Potential.tailSum (normStep p c) T 1 * (T : ℝ) ^ (-betaExp p) ≤ H_beta p := by
        calc
          Potential.tailSum (normStep p c) T 1 * (T : ℝ) ^ (-betaExp p)
            ≤ (H_beta p * c * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) *
                (T : ℝ) ^ (-betaExp p) :=
              mul_le_mul_of_nonneg_right hS1 (Real.rpow_nonneg hT_pos.le _)
          _ = H_beta p * c * ((T : ℝ) ^ (-betaExp p) * (T : ℝ) ^ (betaExp p)) /
                (ell T) ^ (2 : ℕ) := by ring
          _ = H_beta p * c / (ell T) ^ (2 : ℕ) := by rw [hrpow_cancel, mul_one]
          _ ≤ H_beta p * 1 / 1 := by
              apply div_le_div₀ (by have := H_beta_pos hp; positivity)
              · exact mul_le_mul_of_nonneg_left hc1 (H_beta_pos hp).le
              · exact zero_lt_one
              · exact hellT_ge1
          _ = H_beta p := by ring
      have hH64 : 64 ≤ H_beta p := H_beta_ge_64 hp
      nlinarith
    have hell_mono4 : (ell 1) ^ (4 : ℕ) ≤ (ell T) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hell1_pos.le (ell_mono le_rfl hT) 4
    have h1024_le_K : 1024 * H_beta p ≤ K_const p := by
      unfold K_const
      have hH1 : 1 ≤ H_beta p := by linarith [H_beta_ge_64 hp]
      have hH3 : 1 ≤ (H_beta p) ^ (3 : ℕ) := one_le_pow₀ hH1
      calc
        1024 * H_beta p ≤ (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (3 : ℕ) * H_beta p := by nlinarith
        _ = (2 : ℝ) ^ (20 : ℕ) * (H_beta p) ^ (4 : ℕ) := by ring
    calc
      capQ p c T t * (normLambda p t) ^ (2 : ℕ)
        = (capU p c T / SuffixPotential.cappedTail (normStep p c) T t) *
            ((normStep p c t) ^ (2 : ℕ) * (normLambda p t) ^ (2 : ℕ)) := by
          unfold capQ; ring
      _ ≤ capU p c T *
            (512 * c ^ (2 : ℕ) * (T : ℝ) ^ (-betaExp p) / (ell T) ^ (4 : ℕ)) := by
          apply mul_le_mul hU_over_den hlam (by positivity)
          exact (lt_of_lt_of_le zero_lt_one (capU_ge_one hc T)).le
      _ = 512 * (capU p c T * (T : ℝ) ^ (-betaExp p)) * c ^ (2 : ℕ) / (ell T) ^ (4 : ℕ) := by
          ring
      _ ≤ 512 * (2 * H_beta p) * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
          apply div_le_div₀ (by have := H_beta_pos hp; positivity)
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hU_mul (by norm_num)) (sq_nonneg c)
          · exact pow_pos hell1_pos 4
          · exact hell_mono4
      _ = (1024 * H_beta p) * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring
      _ ≤ K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right h1024_le_K (sq_nonneg c)

/-! ## 7.5. Concrete Budget Bounds for Radius and Suffix Potentials -/

lemma radA_sum_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑ t ∈ Finset.range N, 2 * (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (2 * normV p (t + 1))) ≤
      4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  have heq : (∑ t ∈ Finset.range N, 2 * (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (2 * normV p (t + 1))) =
      4 * ∑ t ∈ Finset.range N, (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * normV p (t + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _; ring
  rw [heq]
  have hell1 : 0 < ell 1 := ell_pos le_rfl
  have hK_pos : 0 < K_const p := K_const_pos hp
  have hc_pos : 0 < c_p p := c_p_pos hp
  have h := global_variance_sum_le (c := c_p p) hp N
  calc
    4 * ∑ t ∈ Finset.range N, (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * normV p (t + 1)
      ≤ 4 * (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring

lemma radK_sup_le {p : ℝ} (hp : 1 < p) (t : ℕ) :
    2 * (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (3 * normLambda p (t + 1)) ^ (2 : ℕ) ≤
      288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  have ht : 1 ≤ t + 1 := by omega
  have hid := normStep_sq_mul_normLambda_sq (p := p) (c := c_p p) ht
  calc
    2 * (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (3 * normLambda p (t + 1)) ^ (2 : ℕ)
      = 18 * ((normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (normLambda p (t + 1)) ^ (2 : ℕ)) := by ring
    _ = 18 * (16 * (c_p p) ^ (2 : ℕ) * ((t + 1 : ℕ) : ℝ) ^ (-betaExp p) / (ell (t + 1)) ^ (4 : ℕ)) := by
      rw [hid]
    _ = 288 * (c_p p) ^ (2 : ℕ) * ((t + 1 : ℕ) : ℝ) ^ (-betaExp p) / (ell (t + 1)) ^ (4 : ℕ) := by ring
    _ ≤ 288 * (c_p p) ^ (2 : ℕ) * 1 / (ell 1) ^ (4 : ℕ) := by
      apply div_le_div₀ (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast ht)
        linarith [betaExp_pos hp]
      · exact pow_pos (ell_pos le_rfl) 4
      · exact pow_le_pow_left₀ (ell_pos le_rfl).le (ell_mono le_rfl ht) 4
    _ = 288 * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring

lemma radB_sum_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑ t ∈ Finset.range N, 2 * normStep p (c_p p) (t + 1) * normB p (t + 1)) ≤
      2 * K_const p * c_p p / ell 1 := by
  calc
    (∑ t ∈ Finset.range N, 2 * normStep p (c_p p) (t + 1) * normB p (t + 1))
      = 2 * ∑ t ∈ Finset.range N, normStep p (c_p p) (t + 1) * normB p (t + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _; ring
    _ ≤ 2 * (K_const p * c_p p / ell 1) :=
      mul_le_mul_of_nonneg_left (global_bias_sum_le hp (c_p_pos hp).le N) (by norm_num)
    _ = 2 * K_const p * c_p p / ell 1 := by ring

lemma radV_sum_le {p : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑ t ∈ Finset.range N, (2 * normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (2 * normV p (t + 1))) ≤
      8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  have heq : (∑ t ∈ Finset.range N, (2 * normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * (2 * normV p (t + 1))) =
      8 * ∑ t ∈ Finset.range N, (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * normV p (t + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _; ring
  rw [heq]
  have hell1 : 0 < ell 1 := ell_pos le_rfl
  have hK_pos : 0 < K_const p := K_const_pos hp
  have hc_pos : 0 < c_p p := c_p_pos hp
  have h := global_variance_sum_le (c := c_p p) hp N
  calc
    8 * ∑ t ∈ Finset.range N, (normStep p (c_p p) (t + 1)) ^ (2 : ℕ) * normV p (t + 1)
      ≤ 8 * (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring

lemma radJ_sup_le {p : ℝ} (hp : 1 < p) (t : ℕ) :
    2 * normStep p (c_p p) (t + 1) * (2 * normLambda p (t + 1)) ≤
      16 * c_p p / (ell 1) ^ (2 : ℕ) := by
  have ht : 1 ≤ t + 1 := by omega
  have h := normStep_mul_normLambda_le hp (c_p_pos hp).le ht
  calc
    2 * normStep p (c_p p) (t + 1) * (2 * normLambda p (t + 1))
      = 4 * (normStep p (c_p p) (t + 1) * normLambda p (t + 1)) := by ring
    _ ≤ 4 * (4 * c_p p / (ell 1) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 16 * c_p p / (ell 1) ^ (2 : ℕ) := by ring

lemma sufA_sum_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {T k : ℕ} (hT : 1 ≤ T) (hk : 1 ≤ k) (hkT : k ≤ T) :
    let N := T + 1 - k
    (∑ i ∈ Finset.range N, 2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * normV p (k + i)) ≤
      4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
  intro N
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hell1 : 0 < ell 1 := ell_pos le_rfl
  have hK_pos : 0 < K_const p := K_const_pos hp
  have h1 : (∑ i ∈ Finset.range N, 2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * normV p (k + i))
      ≤ 2 * ∑ t ∈ Finset.Ico 1 (T + 1), capQ p (c_p p) T t * normV p t := by
    calc
      (∑ i ∈ Finset.range N, 2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * normV p (k + i))
        = 2 * ∑ i ∈ Finset.range N, SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * normV p (k + i) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ 2 * ∑ i ∈ Finset.range N, capQ p (c_p p) T (k + i) * normV p (k + i) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right (suffixQuadWeight_le_capQ (p := p) hc_pos.le T k i hk)
          exact normV_nonneg p (k + i)
      _ = 2 * ∑ t ∈ Finset.Ico k (k + N), capQ p (c_p p) T t * normV p t := by
          congr 1
          rw [Finset.range_eq_Ico]
          have h := Finset.sum_Ico_add (fun t => capQ p (c_p p) T t * normV p t) 0 N k
          simpa only [zero_add, add_comm k] using h
      _ = 2 * ∑ t ∈ Finset.Ico k (T + 1), capQ p (c_p p) T t * normV p t := by
          have : k + N = T + 1 := by dsimp [N]; omega
          rw [this]
      _ ≤ 2 * ∑ t ∈ Finset.Ico 1 (T + 1), capQ p (c_p p) T t * normV p t := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have hsub : Finset.Ico k (T + 1) ⊆ Finset.Ico 1 (T + 1) := by
            intro x hx; simp only [Finset.mem_Ico] at hx ⊢; exact ⟨hk.trans hx.1, hx.2⟩
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ =>
            mul_nonneg (capQ_nonneg hc_pos.le T t) (normV_nonneg p t))
  have h2 := capped_variance_sum_le hp hp2 hc_pos.le (c_p_le_one hp) hT
  have hpos : 0 ≤ K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by positivity
  have hK : 2 * (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ)) ≤
      4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
    rw [show 4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) =
        4 * (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ)) by ring]
    linarith
  exact h1.trans ((mul_le_mul_of_nonneg_left h2 (by norm_num)).trans hK)

lemma sufK_sup_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {T k : ℕ} (hT : 1 ≤ T) (hk : 1 ≤ k) (i : ℕ) (hi : k + i ≤ T) :
    2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * (2 * normLambda p (k + i)) ^ (2 : ℕ) ≤
      8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hQ := suffixQuadWeight_le_capQ (p := p) hc_pos.le T k i hk
  have hki : 1 ≤ k + i := by omega
  have hcap := capped_range_le hp hp2 hc_pos.le (c_p_le_one hp) hki hi
  calc
    2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * (2 * normLambda p (k + i)) ^ (2 : ℕ)
      = 8 * (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * (normLambda p (k + i)) ^ (2 : ℕ)) := by ring
    _ ≤ 8 * (capQ p (c_p p) T (k + i) * (normLambda p (k + i)) ^ (2 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right hQ (sq_nonneg _)
    _ ≤ 8 * (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcap (by norm_num)
    _ = 8 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ) := by ring

lemma sufB_sum_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {T k : ℕ} (hT : 1 ≤ T) (hk : 1 ≤ k) (hkT : k ≤ T) :
    let N := T + 1 - k
    (∑ i ∈ Finset.range N, Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normB p (k + i)) ≤
      2 * K_const p * c_p p / ell 1 := by
  intro N
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hell1 : 0 < ell 1 := ell_pos le_rfl
  have hK_pos : 0 < K_const p := K_const_pos hp
  have hW_nn : ∀ i, 0 ≤ SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i := by
    intro i
    have hW : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T k := by
      linarith [cappedTail_ge_one (p := p) hc_pos.le T k]
    have hU : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T (k + i) := by
      linarith [cappedTail_ge_one (p := p) hc_pos.le T (k + i)]
    unfold SuffixPotential.suffixQuadWeight; positivity
  have h1 : (∑ i ∈ Finset.range N, Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normB p (k + i))
      ≤ Real.sqrt 2 * ∑ t ∈ Finset.Ico 1 (T + 1), Real.sqrt (capQ p (c_p p) T t) * normB p t := by
    calc
      (∑ i ∈ Finset.range N, Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normB p (k + i))
        = ∑ i ∈ Finset.range N, (Real.sqrt 2 * Real.sqrt (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i)) * normB p (k + i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * ∑ i ∈ Finset.range N, Real.sqrt (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normB p (k + i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _; ring
      _ ≤ Real.sqrt 2 * ∑ i ∈ Finset.range N, Real.sqrt (capQ p (c_p p) T (k + i)) * normB p (k + i) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          apply Finset.sum_le_sum
          intro i _
          have hQ := suffixQuadWeight_le_capQ (p := p) hc_pos.le T k i hk
          apply mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hQ) (normB_nonneg p _)
      _ = Real.sqrt 2 * ∑ t ∈ Finset.Ico k (k + N), Real.sqrt (capQ p (c_p p) T t) * normB p t := by
          congr 1
          rw [Finset.range_eq_Ico]
          have h := Finset.sum_Ico_add (fun t => Real.sqrt (capQ p (c_p p) T t) * normB p t) 0 N k
          simpa only [zero_add, add_comm k] using h
      _ = Real.sqrt 2 * ∑ t ∈ Finset.Ico k (T + 1), Real.sqrt (capQ p (c_p p) T t) * normB p t := by
          have : k + N = T + 1 := by dsimp [N]; omega
          rw [this]
      _ ≤ Real.sqrt 2 * ∑ t ∈ Finset.Ico 1 (T + 1), Real.sqrt (capQ p (c_p p) T t) * normB p t := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          have hsub : Finset.Ico k (T + 1) ⊆ Finset.Ico 1 (T + 1) := by
            intro x hx; simp only [Finset.mem_Ico] at hx ⊢; exact ⟨hk.trans hx.1, hx.2⟩
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ =>
            mul_nonneg (Real.sqrt_nonneg _) (normB_nonneg p t))
  have h2 := capped_bias_sum_le hp hp2 hc_pos.le hT
  have hsqrt2 : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hK_nn : 0 ≤ K_const p * c_p p / ell 1 := by positivity
  calc
    (∑ i ∈ Finset.range N, Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normB p (k + i))
      ≤ Real.sqrt 2 * (K_const p * c_p p / ell 1) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    _ ≤ 2 * (K_const p * c_p p / ell 1) := mul_le_mul_of_nonneg_right hsqrt2 hK_nn
    _ = 2 * K_const p * c_p p / ell 1 := by ring

lemma sufV_sum_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {T k : ℕ} (hT : 1 ≤ T) (hk : 1 ≤ k) (hkT : k ≤ T) :
    let N := T + 1 - k
    (∑ i ∈ Finset.range N, (Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i)) ^ (2 : ℕ) * normV p (k + i)) ≤
      4 * K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ) := by
  intro N
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hW_nn : ∀ i, 0 ≤ SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i := by
    intro i
    have hW : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T k := by
      linarith [cappedTail_ge_one (p := p) hc_pos.le T k]
    have hU : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T (k + i) := by
      linarith [cappedTail_ge_one (p := p) hc_pos.le T (k + i)]
    unfold SuffixPotential.suffixQuadWeight; positivity
  have heq : (∑ i ∈ Finset.range N, (Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i)) ^ (2 : ℕ) * normV p (k + i)) =
      ∑ i ∈ Finset.range N, 2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * normV p (k + i) := by
    apply Finset.sum_congr rfl
    intro i _
    have : 0 ≤ 2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i := by
      have := hW_nn i; positivity
    rw [Real.sq_sqrt this]
  rw [heq]
  exact sufA_sum_le hp hp2 hT hk hkT

lemma sufJ_sup_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) {T k : ℕ} (hT : 1 ≤ T) (hk : 1 ≤ k) (i : ℕ) (hi : k + i ≤ T) :
    Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * (2 * normLambda p (k + i)) ≤
      2 * Real.sqrt 2 * Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ) := by
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hQ := suffixQuadWeight_le_capQ (p := p) hc_pos.le T k i hk
  have hki : 1 ≤ k + i := by omega
  have hcap := capped_range_le hp hp2 hc_pos.le (c_p_le_one hp) hki hi
  have hW_nn : 0 ≤ SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i := by
    have hW : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T k := by
      linarith [cappedTail_ge_one (p := p) hc_pos.le T k]
    have hU : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T (k + i) := by
      linarith [cappedTail_ge_one (p := p) hc_pos.le T (k + i)]
    unfold SuffixPotential.suffixQuadWeight; positivity
  have hLam_nn : 0 ≤ normLambda p (k + i) := normLambda_nonneg p (k + i)
  have hsqrt_eq : Real.sqrt (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normLambda p (k + i) =
      Real.sqrt (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * (normLambda p (k + i)) ^ (2 : ℕ)) := by
    rw [Real.sqrt_mul hW_nn, Real.sqrt_sq hLam_nn]
  calc
    Real.sqrt (2 * SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * (2 * normLambda p (k + i))
      = 2 * Real.sqrt 2 * (Real.sqrt (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i) * normLambda p (k + i)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring
    _ = 2 * Real.sqrt 2 * Real.sqrt (SuffixPotential.suffixQuadWeight (normStep p (c_p p)) T k i * (normLambda p (k + i)) ^ (2 : ℕ)) := by
        rw [hsqrt_eq]
    _ ≤ 2 * Real.sqrt 2 * Real.sqrt (capQ p (c_p p) T (k + i) * (normLambda p (k + i)) ^ (2 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_right hQ (sq_nonneg _)
    _ ≤ 2 * Real.sqrt 2 * Real.sqrt (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcap) (by positivity)
    _ = 2 * Real.sqrt 2 * (Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ)) := by
        have hsq : Real.sqrt (K_const p * (c_p p) ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)) =
            Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ) := by
          have hK_nn : 0 ≤ K_const p := (K_const_pos hp).le
          have hc_nn : 0 ≤ c_p p := hc_pos.le
          have hell_nn : 0 ≤ (ell 1) ^ (2 : ℕ) := by positivity
          rw [Real.sqrt_div (by positivity), Real.sqrt_mul hK_nn,
            Real.sqrt_sq hc_nn,
            show (ell 1) ^ (4 : ℕ) = ((ell 1) ^ (2 : ℕ)) ^ (2 : ℕ) by ring,
            Real.sqrt_sq hell_nn]
        rw [hsq]
    _ = 2 * Real.sqrt 2 * Real.sqrt (K_const p) * c_p p / (ell 1) ^ (2 : ℕ) := by ring

/-! ## 8. Numeric Closure Inequalities for the Radius, Suffix, and Direct Bounds -/

set_option maxHeartbeats 1000000

/-- Global radius energy threshold bound:
with the global budgets at `c = c_p` and confidence `q = confH δ`,
`energyThreshold 1 A_bud K₀ B₀ V₀ J₀ (confH δ) ≤ (confH δ)²`. -/
lemma global_radius_threshold_le {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let c := c_p p
    let A_bud := 4 * K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)
    let K₀ := 288 * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)
    let B₀ := 2 * K_const p * c / ell 1
    let V₀ := 8 * K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)
    let J₀ := 16 * c / (ell 1) ^ (2 : ℕ)
    EnergyBudget.energyThreshold 1 A_bud K₀ B₀ V₀ J₀ (confH δ) ≤ (confH δ) ^ (2 : ℕ) := by
  intro c A_bud K₀ B₀ V₀ J₀
  have hh : 4 < confH δ := four_lt_confH hδ hδ1
  have hh_pos : 0 < confH δ := by linarith
  have hell1 : 4 < ell 1 := four_lt_ell_one
  have hell1_ge1 : 1 ≤ ell 1 := by linarith
  have hell1_2 : 1 ≤ (ell 1) ^ (2 : ℕ) := one_le_pow₀ hell1_ge1
  have hell1_4 : 1 ≤ (ell 1) ^ (4 : ℕ) := one_le_pow₀ hell1_ge1
  have hKc : K_const p * c = 1 / 1000 := K_mul_c_p hp
  have hc_pos : 0 < c := c_p_pos hp
  have hc_le : c ≤ 1 / 1000 := c_p_le_inv_1000 hp
  have hK_pos : 0 < K_const p := K_const_pos hp
  -- Simple numeric upper bounds on `A_bud, K₀, B₀, V₀, J₀`
  have hA_le : A_bud ≤ 4 / 1000 := by
    dsimp [A_bud]
    have hnum : 4 * K_const p * c ^ (2 : ℕ) ≤ 4 / 1000 := by
      calc
        4 * K_const p * c ^ (2 : ℕ) = 4 * (K_const p * c) * c := by ring
        _ ≤ 4 * (1 / 1000) * 1 := by nlinarith
        _ = 4 / 1000 := by ring
    exact (div_le_self (by positivity) hell1_4).trans hnum
  have hK0_le : K₀ ≤ 1 / 1000 := by
    dsimp [K₀]
    have hnum : 288 * c ^ (2 : ℕ) ≤ 1 / 1000 := by nlinarith
    exact (div_le_self (by positivity) hell1_4).trans hnum
  have hB0_le : B₀ ≤ 2 / 1000 := by
    dsimp [B₀]
    have hnum : 2 * K_const p * c = 2 / 1000 := by linarith
    exact (div_le_self (by positivity) hell1_ge1).trans hnum.le
  have hV0_le : V₀ ≤ 8 / 1000 ^ (2 : ℕ) := by
    dsimp [V₀]
    have hnum : 8 * K_const p * c ^ (2 : ℕ) ≤ 8 / 1000 ^ (2 : ℕ) := by
      calc
        8 * K_const p * c ^ (2 : ℕ) = 8 * (K_const p * c) * c := by ring
        _ ≤ 8 * (1 / 1000) * (1 / 1000) := by nlinarith
        _ = 8 / 1000 ^ (2 : ℕ) := by ring
    exact (div_le_self (by positivity) hell1_4).trans hnum
  have hJ0_le : J₀ ≤ 16 / 1000 := by
    dsimp [J₀]
    have hnum : 16 * c ≤ 16 / 1000 := by linarith
    exact (div_le_self (by positivity) hell1_2).trans hnum
  have hA_nn : 0 ≤ A_bud := by dsimp [A_bud]; positivity
  have hK0_nn : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hV0_nn : 0 ≤ V₀ := by dsimp [V₀]; positivity
  have hsqrt_KA : Real.sqrt (K₀ * A_bud * confH δ) ≤ (2 / 1000) * confH δ := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (2 / 1000) * confH δ)]
    apply Real.sqrt_le_sqrt
    have : K₀ * A_bud ≤ 4 / 1000 ^ (2 : ℕ) := by nlinarith
    nlinarith
  have hsqrt_V : Real.sqrt (V₀ * confH δ) ≤ (3 / 1000) * confH δ := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (3 / 1000) * confH δ)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hC_le : EnergyBudget.energyC 1 A_bud K₀ (confH δ) ≤ (1 + (10 / 1000) * confH δ) ^ (2 : ℕ) := by
    unfold EnergyBudget.energyC
    nlinarith
  have hsqrt_C : Real.sqrt (EnergyBudget.energyC 1 A_bud K₀ (confH δ)) ≤
      1 + (10 / 1000) * confH δ := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 + (10 / 1000) * confH δ)]
    exact Real.sqrt_le_sqrt hC_le
  have hB0_h : B₀ ≤ (1 / 1000 : ℝ) * confH δ := by
    nlinarith [hB0_le, hh]
  have hJ_term : 2 * J₀ * confH δ ≤ (32 / 1000 : ℝ) * confH δ := by
    nlinarith [hJ0_le, hh_pos]
  have hD_le : EnergyBudget.energyD B₀ V₀ J₀ (confH δ) ≤ (40 / 1000) * confH δ := by
    unfold EnergyBudget.energyD
    linarith [hB0_h, hsqrt_V, hJ_term]
  have hsum_le : Real.sqrt (EnergyBudget.energyC 1 A_bud K₀ (confH δ)) +
      EnergyBudget.energyD B₀ V₀ J₀ (confH δ) ≤ confH δ := by
    linarith
  unfold EnergyBudget.energyThreshold
  have hsum_nn : 0 ≤ Real.sqrt (EnergyBudget.energyC 1 A_bud K₀ (confH δ)) +
      EnergyBudget.energyD B₀ V₀ J₀ (confH δ) := by
    have : 0 ≤ EnergyBudget.energyD B₀ V₀ J₀ (confH δ) := by
      unfold EnergyBudget.energyD; dsimp [B₀, J₀]; positivity
    positivity
  exact pow_le_pow_left₀ hsum_nn hsum_le 2

/-- Suffix potential energy threshold bound:
with the capped budgets at `c = c_p`, `p₀ = (confH δ)² / 2`, and `q = iota δ T` (`T ≥ 1`),
`energyThreshold ((confH δ)² / 2) A_bud K₀ B₀ V₀ J₀ (iota δ T) ≤ (iota δ T)²`. -/
lemma suffix_potential_threshold_le {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T : ℕ} (hT : 1 ≤ T) :
    let c := c_p p
    let A_bud := 4 * K_const p * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ)
    let K₀ := 8 * K_const p * c ^ (2 : ℕ) / (ell 1) ^ (4 : ℕ)
    let B₀ := 2 * K_const p * c / ell 1
    let V₀ := 4 * K_const p * c ^ (2 : ℕ) / (ell 1) ^ (3 : ℕ)
    let J₀ := 2 * Real.sqrt 2 * Real.sqrt (K_const p) * c / (ell 1) ^ (2 : ℕ)
    EnergyBudget.energyThreshold ((confH δ) ^ (2 : ℕ) / 2) A_bud K₀ B₀ V₀ J₀ (iota δ T) ≤
      (iota δ T) ^ (2 : ℕ) := by
  intro c A_bud K₀ B₀ V₀ J₀
  have hq : 4 < iota δ T := four_lt_iota hδ hδ1 hT
  have hq_pos : 0 < iota δ T := by linarith
  have hh_le_q : confH δ ≤ iota δ T := confH_le_iota hδ hT
  have hh_pos : 0 < confH δ := confH_pos hδ hδ1
  have hell1 : 4 < ell 1 := four_lt_ell_one
  have hell1_ge1 : 1 ≤ ell 1 := by linarith
  have hell1_2 : 1 ≤ (ell 1) ^ (2 : ℕ) := one_le_pow₀ hell1_ge1
  have hell1_3 : 1 ≤ (ell 1) ^ (3 : ℕ) := one_le_pow₀ hell1_ge1
  have hell1_4 : 1 ≤ (ell 1) ^ (4 : ℕ) := one_le_pow₀ hell1_ge1
  have hKc : K_const p * c = 1 / 1000 := K_mul_c_p hp
  have hc_pos : 0 < c := c_p_pos hp
  have hc_le : c ≤ 1 / 1000 := c_p_le_inv_1000 hp
  have hK_ge1 : 1 ≤ K_const p := K_const_ge_one hp
  have hsqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtK_le_K : Real.sqrt (K_const p) ≤ K_const p := by
    have hsq : (Real.sqrt (K_const p)) ^ (2 : ℕ) = K_const p := Real.sq_sqrt (by linarith)
    have hge1 : 1 ≤ Real.sqrt (K_const p) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hK_ge1
    nlinarith
  have hA_le : A_bud ≤ 4 / 1000 := by
    dsimp [A_bud]
    have hnum : 4 * K_const p * c ^ (2 : ℕ) ≤ 4 / 1000 := by
      calc
        4 * K_const p * c ^ (2 : ℕ) = 4 * (K_const p * c) * c := by ring
        _ ≤ 4 * (1 / 1000) * 1 := by nlinarith
        _ = 4 / 1000 := by ring
    exact (div_le_self (by positivity) hell1_3).trans hnum
  have hK0_le : K₀ ≤ 8 / 1000 := by
    dsimp [K₀]
    have hnum : 8 * K_const p * c ^ (2 : ℕ) ≤ 8 / 1000 := by
      calc
        8 * K_const p * c ^ (2 : ℕ) = 8 * (K_const p * c) * c := by ring
        _ ≤ 8 * (1 / 1000) * 1 := by nlinarith
        _ = 8 / 1000 := by ring
    exact (div_le_self (by positivity) hell1_4).trans hnum
  have hB0_le : B₀ ≤ 2 / 1000 := by
    dsimp [B₀]
    have hnum : 2 * K_const p * c = 2 / 1000 := by linarith
    exact (div_le_self (by positivity) hell1_ge1).trans hnum.le
  have hV0_le : V₀ ≤ 4 / 1000 := hA_le
  have hJ0_le : J₀ ≤ 3 / 1000 := by
    dsimp [J₀]
    have hnum : 2 * Real.sqrt 2 * Real.sqrt (K_const p) * c ≤ 3 / 1000 := by
      have h1 : 2 * Real.sqrt 2 * Real.sqrt (K_const p) * c ≤
          2 * (3 / 2) * K_const p * c := by
        calc
          2 * Real.sqrt 2 * Real.sqrt (K_const p) * c
            ≤ 2 * (3 / 2) * Real.sqrt (K_const p) * c := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
              linarith [hsqrt2_le]
          _ ≤ 2 * (3 / 2) * K_const p * c := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              apply mul_le_mul_of_nonneg_left hsqrtK_le_K (by norm_num)
      have h2 : 2 * (3 / 2) * K_const p * c = 3 * (K_const p * c) := by ring
      have h3 : 3 * (K_const p * c) = 3 / 1000 := by rw [hKc]; ring
      linarith
    exact (div_le_self (by positivity) hell1_2).trans hnum
  have hA_nn : 0 ≤ A_bud := by dsimp [A_bud]; positivity
  have hK0_nn : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hV0_nn : 0 ≤ V₀ := by dsimp [V₀]; positivity
  have hsqrt_KA : Real.sqrt (K₀ * A_bud * iota δ T) ≤ (8 / 1000) * iota δ T := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (8 / 1000) * iota δ T)]
    apply Real.sqrt_le_sqrt
    have : K₀ * A_bud ≤ 64 / 1000 ^ (2 : ℕ) := by nlinarith
    nlinarith
  have hsqrt_V : Real.sqrt (V₀ * iota δ T) ≤ (70 / 1000) * iota δ T := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (70 / 1000) * iota δ T)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hp0_le : (confH δ) ^ (2 : ℕ) / 2 ≤ (iota δ T) ^ (2 : ℕ) / 2 := by
    have : (confH δ) ^ (2 : ℕ) ≤ (iota δ T) ^ (2 : ℕ) := pow_le_pow_left₀ hh_pos.le hh_le_q 2
    linarith
  have hC_le : EnergyBudget.energyC ((confH δ) ^ (2 : ℕ) / 2) A_bud K₀ (iota δ T) ≤
      ((4 / 5 : ℝ) * iota δ T) ^ (2 : ℕ) := by
    unfold EnergyBudget.energyC
    have hq4 : 4 ≤ iota δ T := hq.le
    have hq2 : 16 ≤ (iota δ T) ^ (2 : ℕ) := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hq.le 2
      norm_num at h
      exact h
    have h1 : (confH δ) ^ (2 : ℕ) / 2 ≤ (1 / 2 : ℝ) * (iota δ T) ^ (2 : ℕ) := by linarith [hp0_le]
    have h2 : A_bud ≤ (1 / 1000 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
      calc
        A_bud ≤ 4 / 1000 := hA_le
        _ ≤ (1 / 1000 : ℝ) * 16 := by norm_num
        _ ≤ (1 / 1000 : ℝ) * (iota δ T) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hq2 (by norm_num)
    have hq_le_sq : iota δ T ≤ (1 / 4 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
      have : 4 * iota δ T ≤ (iota δ T) ^ (2 : ℕ) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hq.le hq_pos.le
      linarith
    have h3 : 2 * Real.sqrt (K₀ * A_bud * iota δ T) ≤ (2 / 100 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
      calc
        2 * Real.sqrt (K₀ * A_bud * iota δ T) ≤ 2 * ((8 / 1000) * iota δ T) :=
          mul_le_mul_of_nonneg_left hsqrt_KA (by norm_num)
        _ = (16 / 1000) * iota δ T := by ring
        _ ≤ (16 / 1000) * ((1 / 4 : ℝ) * (iota δ T) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hq_le_sq (by norm_num)
        _ = (4 / 1000 : ℝ) * (iota δ T) ^ (2 : ℕ) := by ring
        _ ≤ (2 / 100 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
            apply mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    have h4 : 2 * K₀ * iota δ T ≤ (2 / 100 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
      calc
        2 * K₀ * iota δ T ≤ 2 * (8 / 1000) * iota δ T := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK0_le (by norm_num)) hq_pos.le
        _ = (16 / 1000) * iota δ T := by ring
        _ ≤ (16 / 1000) * ((1 / 4 : ℝ) * (iota δ T) ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hq_le_sq (by norm_num)
        _ = (4 / 1000 : ℝ) * (iota δ T) ^ (2 : ℕ) := by ring
        _ ≤ (2 / 100 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
            apply mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    calc
      ((confH δ) ^ (2 : ℕ) / 2) + A_bud + 2 * Real.sqrt (K₀ * A_bud * iota δ T) + 2 * K₀ * iota δ T
        ≤ (1 / 2 : ℝ) * (iota δ T) ^ (2 : ℕ) + (1 / 1000 : ℝ) * (iota δ T) ^ (2 : ℕ) +
            (2 / 100 : ℝ) * (iota δ T) ^ (2 : ℕ) + (2 / 100 : ℝ) * (iota δ T) ^ (2 : ℕ) := by
          linarith [h1, h2, h3, h4]
      _ = (541 / 1000 : ℝ) * (iota δ T) ^ (2 : ℕ) := by ring
      _ ≤ ((4 / 5 : ℝ) * iota δ T) ^ (2 : ℕ) := by
          rw [mul_pow]
          have : (541 / 1000 : ℝ) ≤ (4 / 5 : ℝ) ^ (2 : ℕ) := by norm_num
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hsqrt_C : Real.sqrt (EnergyBudget.energyC ((confH δ) ^ (2 : ℕ) / 2) A_bud K₀ (iota δ T)) ≤
      (4 / 5 : ℝ) * iota δ T := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (4 / 5 : ℝ) * iota δ T)]
    exact Real.sqrt_le_sqrt hC_le
  have hD_le : EnergyBudget.energyD B₀ V₀ J₀ (iota δ T) ≤ (1 / 5 : ℝ) * iota δ T := by
    unfold EnergyBudget.energyD
    have hB_le : B₀ ≤ (1 / 1000 : ℝ) * iota δ T := by
      have h1 : (2 / 1000 : ℝ) ≤ (1 / 1000 : ℝ) * iota δ T := by
        calc
          (2 / 1000 : ℝ) ≤ (1 / 1000 : ℝ) * 4 := by norm_num
          _ ≤ (1 / 1000 : ℝ) * iota δ T := mul_le_mul_of_nonneg_left hq.le (by norm_num)
      exact hB0_le.trans h1
    have hsqrtV_le : 2 * Real.sqrt (V₀ * iota δ T) ≤ (140 / 1000 : ℝ) * iota δ T := by
      calc
        2 * Real.sqrt (V₀ * iota δ T) ≤ 2 * ((70 / 1000 : ℝ) * iota δ T) :=
          mul_le_mul_of_nonneg_left hsqrt_V (by norm_num)
        _ = (140 / 1000 : ℝ) * iota δ T := by ring
    have hJ_le : 2 * J₀ * iota δ T ≤ (6 / 1000 : ℝ) * iota δ T := by
      calc
        2 * J₀ * iota δ T ≤ 2 * (3 / 1000) * iota δ T := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ0_le (by norm_num)) hq_pos.le
        _ = (6 / 1000 : ℝ) * iota δ T := by ring
    calc
      B₀ + 2 * Real.sqrt (V₀ * iota δ T) + 2 * J₀ * iota δ T
        ≤ (1 / 1000 : ℝ) * iota δ T + (140 / 1000 : ℝ) * iota δ T + (6 / 1000 : ℝ) * iota δ T := by
          linarith [hB_le, hsqrtV_le, hJ_le]
      _ = (147 / 1000 : ℝ) * iota δ T := by ring
      _ ≤ (1 / 5 : ℝ) * iota δ T := by
          apply mul_le_mul_of_nonneg_right (by norm_num) hq_pos.le
  have hsum_le : Real.sqrt (EnergyBudget.energyC ((confH δ) ^ (2 : ℕ) / 2) A_bud K₀ (iota δ T)) +
      EnergyBudget.energyD B₀ V₀ J₀ (iota δ T) ≤ iota δ T := by
    linarith [hsqrt_C, hD_le]
  unfold EnergyBudget.energyThreshold
  have hsum_nn : 0 ≤ Real.sqrt (EnergyBudget.energyC ((confH δ) ^ (2 : ℕ) / 2) A_bud K₀ (iota δ T)) +
      EnergyBudget.energyD B₀ V₀ J₀ (iota δ T) := by
    have : 0 ≤ EnergyBudget.energyD B₀ V₀ J₀ (iota δ T) := by
      unfold EnergyBudget.energyD; dsimp [B₀, J₀]; positivity
    positivity
  exact pow_le_pow_left₀ hsum_nn hsum_le 2

/-- Suffix split time `k = ⌈h ^ (1 / b)⌉`. -/
def kCut (p δ : ℝ) : ℕ := Nat.ceil ((confH δ) ^ (1 / bExp p))

lemma one_lt_confH_rpow_inv_b {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 < (confH δ) ^ (1 / bExp p) := by
  have hh : 1 < confH δ := by linarith [four_lt_confH hδ hδ1]
  have hb : 0 < 1 / bExp p := one_div_pos.mpr (bExp_pos hp)
  exact Real.one_lt_rpow hh hb

lemma kCut_pos {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 ≤ kCut p δ := by
  unfold kCut
  have h := one_lt_confH_rpow_inv_b hp hδ hδ1
  exact Nat.ceil_pos.mpr (by linarith)

lemma kCut_le_two_rpow {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (kCut p δ : ℝ) ≤ 2 * (confH δ) ^ (1 / bExp p) := by
  unfold kCut
  have h1 : 1 < (confH δ) ^ (1 / bExp p) := one_lt_confH_rpow_inv_b hp hδ hδ1
  have hceil : (Nat.ceil ((confH δ) ^ (1 / bExp p)) : ℝ) <
      (confH δ) ^ (1 / bExp p) + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

/-- For `t ≥ kCut p δ`, `4 h ≤ λ_t`. -/
lemma four_confH_le_normLambda_of_ge_kCut {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1)
    {t : ℕ} (ht : kCut p δ ≤ t) :
    4 * confH δ ≤ normLambda p t := by
  unfold normLambda
  have hb_pos : 0 < bExp p := bExp_pos hp
  have hh_pos : 0 < confH δ := confH_pos hδ hδ1
  have hle_t : (confH δ) ^ (1 / bExp p) ≤ (t : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast ht)
  have hrpow := Real.rpow_le_rpow (by positivity) hle_t hb_pos.le
  rw [← Real.rpow_mul hh_pos.le, one_div_mul_cancel hb_pos.ne', Real.rpow_one] at hrpow
  linarith

/-- Early-time rate bound for `1 ≤ T < 2 kCut p δ`:
if `G ≤ h² / 2`, then `G ≤ D_p T ^ (-β) ι_T(δ)⁴`. -/
lemma early_time_rate_bound {p δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T : ℕ} (hT1 : 1 ≤ T) (hT_early : T < 2 * kCut p δ)
    {G : ℝ} (hG : G ≤ (confH δ) ^ (2 : ℕ) / 2) :
    G ≤ D_p p * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  have hh : 4 < confH δ := four_lt_confH hδ hδ1
  have hh_pos : 0 < confH δ := by linarith
  have hb_pos : 0 < bExp p := bExp_pos hp
  have hbeta_pos : 0 < betaExp p := betaExp_pos hp
  have hbeta_le : betaExp p ≤ 2 / 5 := betaExp_le_two_fifths hp hp2
  have hT_le_4 : (T : ℝ) ≤ 4 * (confH δ) ^ (1 / bExp p) := by
    have hlt : (T : ℝ) < 2 * (kCut p δ : ℝ) := by exact_mod_cast hT_early
    have hk := kCut_le_two_rpow hp hδ hδ1
    linarith
  have hT_beta : (T : ℝ) ^ (betaExp p) ≤ 4 * confH δ := by
    have h1 := Real.rpow_le_rpow hT_pos.le hT_le_4 hbeta_pos.le
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hh_pos.le] at h1
    have hexp : 1 / bExp p * betaExp p = p - 1 := by
      rw [← bExp_mul_sub_one]
      field_simp [hb_pos.ne']
    rw [hexp] at h1
    have h4_le : (4 : ℝ) ^ (betaExp p) ≤ (4 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h4_le
    have hh_p1 : (confH δ) ^ (p - 1) ≤ (confH δ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_one] at hh_p1
    calc
      (T : ℝ) ^ (betaExp p)
        ≤ (4 : ℝ) ^ (betaExp p) * (confH δ) ^ (p - 1) := h1
      _ ≤ 4 * confH δ :=
        mul_le_mul h4_le hh_p1 (Real.rpow_nonneg hh_pos.le _) (by norm_num)
  have hprod_le : (T : ℝ) ^ (betaExp p) * ((confH δ) ^ (2 : ℕ) / 2) ≤
      D_p p * (iota δ T) ^ (4 : ℕ) := by
    have h1 : (T : ℝ) ^ (betaExp p) * ((confH δ) ^ (2 : ℕ) / 2) ≤
        (4 * confH δ) * ((confH δ) ^ (2 : ℕ) / 2) :=
      mul_le_mul_of_nonneg_right hT_beta (by positivity)
    have h2 : (4 * confH δ) * ((confH δ) ^ (2 : ℕ) / 2) ≤ (confH δ) ^ (4 : ℕ) := by
      calc
        (4 * confH δ) * ((confH δ) ^ (2 : ℕ) / 2) = 2 * (confH δ) ^ (3 : ℕ) := by ring
        _ ≤ (confH δ) * (confH δ) ^ (3 : ℕ) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (confH δ) ^ (4 : ℕ) := by ring
    have h3 : (confH δ) ^ (4 : ℕ) ≤ (iota δ T) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hh_pos.le (confH_le_iota hδ hT1) 4
    have hD1 : 1 ≤ D_p p := D_p_ge_one hp
    have h4 : (iota δ T) ^ (4 : ℕ) ≤ D_p p * (iota δ T) ^ (4 : ℕ) := by
      have : 0 ≤ (iota δ T) ^ (4 : ℕ) := by positivity
      nlinarith
    exact ((h1.trans h2).trans h3).trans h4
  have hrpow_inv : (T : ℝ) ^ (betaExp p) * (T : ℝ) ^ (-betaExp p) = 1 := by
    rw [← Real.rpow_add hT_pos, add_neg_cancel, Real.rpow_zero]
  have hdiv := mul_le_mul_of_nonneg_right hprod_le (Real.rpow_nonneg hT_pos.le (-betaExp p))
  have hlhs : (T : ℝ) ^ (betaExp p) * ((confH δ) ^ (2 : ℕ) / 2) * (T : ℝ) ^ (-betaExp p) =
      (confH δ) ^ (2 : ℕ) / 2 := by
    calc
      (T : ℝ) ^ (betaExp p) * ((confH δ) ^ (2 : ℕ) / 2) * (T : ℝ) ^ (-betaExp p)
        = ((T : ℝ) ^ (betaExp p) * (T : ℝ) ^ (-betaExp p)) * ((confH δ) ^ (2 : ℕ) / 2) := by
          ring
      _ = (confH δ) ^ (2 : ℕ) / 2 := by rw [hrpow_inv, one_mul]
  rw [hlhs] at hdiv
  exact hG.trans (hdiv.trans_eq (by ring))

/-- Late-time rate bound for `T ≥ 2 kCut p δ`:
if `P_T ≤ ι_T(δ)²`, then `2 P_T / W ≤ D_p T ^ (-β) ι_T(δ)⁴`. -/
lemma late_time_rate_bound {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1)
    {T : ℕ} (hT_late : 2 * kCut p δ ≤ T)
    {P_T : ℝ} (hP_T : P_T ≤ (iota δ T) ^ (2 : ℕ)) :
    2 * P_T / SuffixPotential.cappedTail (normStep p (c_p p)) T (kCut p δ) ≤
      D_p p * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) := by
  have hk1 : 1 ≤ kCut p δ := kCut_pos hp hδ hδ1
  have hT1 : 1 ≤ T := by omega
  have hT_pos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  have hc_pos : 0 < c_p p := c_p_pos hp
  have hell_T_pos : 0 < ell T := ell_pos hT1
  have hlow := step_sum_lower_bound hp hc_pos.le hk1 (by omega : 2 * kCut p δ ≤ T + 1)
  have hW_ge : (c_p p / 2) * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) ≤
      SuffixPotential.cappedTail (normStep p (c_p p)) T (kCut p δ) := by
    unfold SuffixPotential.cappedTail
    linarith
  have hlow_pos : 0 < (c_p p / 2) * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ) := by
    positivity
  have hW_pos : 0 < SuffixPotential.cappedTail (normStep p (c_p p)) T (kCut p δ) :=
    lt_of_lt_of_le hlow_pos hW_ge
  have hrpow_inv : (T : ℝ) ^ (betaExp p) * (T : ℝ) ^ (-betaExp p) = 1 := by
    rw [← Real.rpow_add hT_pos, add_neg_cancel, Real.rpow_zero]
  have hell_le_iota : (ell T) ^ (2 : ℕ) ≤ (iota δ T) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hell_T_pos.le (ell_le_iota hδ hδ1 hT1) 2
  calc
    2 * P_T / SuffixPotential.cappedTail (normStep p (c_p p)) T (kCut p δ)
      ≤ 2 * (iota δ T) ^ (2 : ℕ) /
          ((c_p p / 2) * (T : ℝ) ^ (betaExp p) / (ell T) ^ (2 : ℕ)) := by
        apply div_le_div₀ (by positivity)
        · linarith
        · exact hlow_pos
        · exact hW_ge
    _ = (4 / c_p p) * (1 / (T : ℝ) ^ (betaExp p)) *
          (ell T) ^ (2 : ℕ) * (iota δ T) ^ (2 : ℕ) := by
        field_simp; ring
    _ = D_p p * (T : ℝ) ^ (-betaExp p) * (ell T) ^ (2 : ℕ) * (iota δ T) ^ (2 : ℕ) := by
        unfold D_p
        rw [one_div, ← Real.rpow_neg hT_pos.le]
    _ ≤ D_p p * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (2 : ℕ) * (iota δ T) ^ (2 : ℕ) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left hell_le_iota
          have := D_p_ge_one hp
          positivity
        · positivity
    _ = D_p p * (T : ℝ) ^ (-betaExp p) * (iota δ T) ^ (4 : ℕ) := by ring

/-- Total failure probability bound:
`exp(-h) + ∑_{i=0}^{N-1} exp(-ι_{2k + i}) ≤ δ`. -/
lemma total_failure_prob_le {p δ : ℝ} (hp : 1 < p) (hδ : 0 < δ) (hδ1 : δ < 1) (N : ℕ) :
    Real.exp (-confH δ) +
      (∑ i ∈ Finset.range N, Real.exp (-iota δ (2 * kCut p δ + i))) ≤ δ := by
  have hk1 : 1 ≤ kCut p δ := kCut_pos hp hδ hδ1
  have hexp_h : Real.exp (-confH δ) = δ / 100 := by
    unfold confH
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hexp_iota : ∀ t : ℕ, 1 ≤ t → Real.exp (-iota δ t) = δ / 100 * ((t : ℝ) ^ (-1 - (1 : ℝ))) := by
    intro t ht
    have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    unfold iota
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div,
      show (-1 - (1 : ℝ)) = (-2 : ℝ) by ring,
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ht_pos.le, Real.rpow_natCast]
    ring
  have hterm_le : ∀ i : ℕ,
      Real.exp (-iota δ (2 * kCut p δ + i)) ≤
        (δ / 100) * (((i + 1 : ℕ) : ℝ) ^ (-1 - (1 : ℝ))) := by
    intro i
    have ht_ge : i + 1 ≤ 2 * kCut p δ + i := by omega
    have ht1 : 1 ≤ 2 * kCut p δ + i := by omega
    rw [hexp_iota (2 * kCut p δ + i) ht1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_nonpos (by positivity) (by exact_mod_cast ht_ge) (by norm_num)
  have hsum_le : (∑ i ∈ Finset.range N, Real.exp (-iota δ (2 * kCut p δ + i))) ≤
      (δ / 100) * 2 := by
    calc
      (∑ i ∈ Finset.range N, Real.exp (-iota δ (2 * kCut p δ + i)))
        ≤ ∑ i ∈ Finset.range N, (δ / 100) * (((i + 1 : ℕ) : ℝ) ^ (-1 - (1 : ℝ))) :=
          Finset.sum_le_sum (fun i _ => hterm_le i)
      _ = (δ / 100) * (∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ (-1 - (1 : ℝ)))) := by
          rw [← Finset.mul_sum]
      _ ≤ (δ / 100) * (1 + 1 / (1 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (sum_rpow_neg_one_sub_le zero_lt_one N) (by positivity)
      _ = (δ / 100) * 2 := by ring
  linarith

end

end ClippedSGD.AnytimeParameters
