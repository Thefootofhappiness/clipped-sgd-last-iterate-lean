import ClippedSGD.Potential
import ClippedSGD.Radius

/-! `lem:potential` with boundary mass `ζ = 1`, endpoint conversion
(`eq:potential-endpoint`), global radius step, and suffix potential on `k..T`
 (`eq:capped-partial-potential`). -/
open Set
open scoped BigOperators InnerProductSpace
namespace ClippedSGD.SuffixPotential
open Potential Radius
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Global radius step: if `y = x - η • (A • ∇f(x) + d)` with `0 ≤ η`,
`0 ≤ η * A ≤ 1 / (2 * L)`, then
`‖y - xstar‖^2 ≤ ‖x - xstar‖^2 - 2 * η * ⟪d, x - xstar⟫ + 2 * η^2 * ‖d‖^2`. -/
lemma global_radius_step {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (hdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hlip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : E) (hmin : ∀ u, f xstar ≤ f u)
    (x y d : E) (η A : ℝ) (hη : 0 ≤ η) (hγ0 : 0 ≤ η * A) (hγL : η * A ≤ 1 / (2 * L))
    (hy : y = x - η • (A • gradient f x + d)) :
    ‖y - xstar‖ ^ 2 ≤ ‖x - xstar‖ ^ 2 +
      (2 * η ^ 2 * ‖d‖ ^ 2 + ⟪d, (-2 * η) • (x - xstar)⟫_ℝ) := by
  let γ := η * A
  let μ := gradient f x
  have hgrad : ∀ u, HasGradientAt f (gradient f u) u := fun u => (hdiff u).hasGradientAt
  have hsupp := convex_support hconv hgrad x xstar
  rw [show xstar - x = -(x - xstar) by abel, inner_neg_right] at hsupp
  have hgap : f x - f xstar ≤ ⟪μ, x - xstar⟫_ℝ := by linarith
  have hgap0 : 0 ≤ f x - f xstar := sub_nonneg.mpr (hmin x)
  have hμsq : ‖μ‖ ^ 2 ≤ 2 * L * (f x - f xstar) :=
    gradient_sq_le_gap hgrad L hL hlip xstar hmin x
  have h2γL : 2 * L * γ ≤ 1 := by
    have := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hγL
    dsimp [γ]
    linarith
  have hy_sub : y - xstar = (x - xstar) - (γ • μ + η • d) := by
    rw [hy, smul_add, smul_smul]
    abel
  have hpara : ‖γ • μ + η • d‖ ^ 2 ≤ 2 * ‖γ • μ‖ ^ 2 + 2 * ‖η • d‖ ^ 2 := by
    have h1 := norm_add_sq_real (γ • μ) (η • d)
    have h2 := norm_sub_sq_real (γ • μ) (η • d)
    have h3 : 0 ≤ ‖γ • μ - η • d‖ ^ 2 := sq_nonneg _
    linarith
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hpara
  have hexp : ‖y - xstar‖ ^ 2 = ‖x - xstar‖ ^ 2 - 2 * γ * ⟪μ, x - xstar⟫_ℝ -
      2 * η * ⟪d, x - xstar⟫_ℝ + ‖γ • μ + η • d‖ ^ 2 := by
    rw [hy_sub, norm_sub_sq_real, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm (x - xstar) μ, real_inner_comm (x - xstar) d]
    ring
  have hμ_term : -2 * γ * ⟪μ, x - xstar⟫_ℝ + 2 * γ ^ 2 * ‖μ‖ ^ 2 ≤ 0 := by
    have h1 : 2 * γ ^ 2 * ‖μ‖ ^ 2 ≤ 4 * L * γ ^ 2 * (f x - f xstar) := by
      have := mul_le_mul_of_nonneg_left hμsq (show 0 ≤ 2 * γ ^ 2 by positivity)
      linarith
    have h2 : -2 * γ * ⟪μ, x - xstar⟫_ℝ ≤ -2 * γ * (f x - f xstar) := by
      have := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * γ by positivity)
      linarith
    have h3 : 2 * γ * (2 * L * γ - 1) * (f x - f xstar) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) hgap0
    linarith
  rw [real_inner_smul_right]
  linarith

/-- Endpoint conversion of `eq:potential-endpoint`: for `L`-smooth convex `f`
and any `w, η, U` satisfying `U t = η t + U (t+1)`, `U t * w t = 1` up to `T+1` with
`U (T+1) = 1` (boundary mass `ζ = 1`),
`f (x (T+1)) - f xstar ≤ (1 + L) * (recursiveAverage G η w T + distanceEnergy xstar x w T)`. -/
theorem potential_endpoint_bound {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : E) (hmin : ∀ u, f xstar ≤ f u)
    (x : ℕ → E) (w η U : ℕ → ℝ) (T : ℕ)
    (hw : ∀ t ≤ T + 1, 0 < w t) (hwmono : ∀ t ≤ T, w t ≤ w (t + 1))
    (hη0 : η 0 = 0) (hηT : 0 ≤ η T)
    (hU : ∀ t ≤ T, U t = η t + U (t + 1))
    (hUw : ∀ t ≤ T + 1, U t * w t = 1)
    (hU_term : U (T + 1) = 1) :
    f (x (T + 1)) - f xstar ≤
      (1 + L) * (recursiveAverage (fun t => f (x t) - f xstar) η w T +
        distanceEnergy xstar x w T) := by
  let z := comparator xstar x w (T + 1)
  let y := x (T + 1)
  have hgrad : ∀ u, HasGradientAt f (gradient f u) u := fun u => (hdiff u).hasGradientAt
  have hcomp_gap : f z - f xstar ≤ recursiveAverage (fun t => f (x t) - f xstar) η w T :=
    comparator_gap_le_recursiveAverage hconv xstar x w η U T hw hwmono hη0 hU hUw
  have hwT1 : w (T + 1) = 1 := by
    have h := hUw (T + 1) le_rfl
    rw [hU_term, one_mul] at h
    exact h
  have hUT : U T = 1 + η T := by
    have h := hU T le_rfl
    linarith [hU_term]
  have hwT_le_one : w T ≤ 1 := by
    rw [← hwT1]
    exact hwmono T le_rfl
  have hwT_pos : 0 < w T := hw T (by omega)
  have hdisp : ‖y - z‖ ^ 2 = (2 * w T) * distanceEnergy xstar x w T := by
    have hd := comparator_displacement xstar x w T
    change z - y = (w T / w (T + 1)) • (comparator xstar x w T - y) at hd
    rw [hwT1, div_one] at hd
    rw [norm_sub_rev y z, hd, norm_smul, Real.norm_eq_abs, abs_of_pos hwT_pos, mul_pow]
    unfold distanceEnergy
    ring
  have hdisp_le : ‖y - z‖ ^ 2 ≤ 2 * distanceEnergy xstar x w T := by
    rw [hdisp]
    have hde : 0 ≤ distanceEnergy xstar x w T := by
      unfold distanceEnergy
      positivity
    nlinarith
  have hsmooth := smooth_upper hgrad hlip z y
  have hcs : ⟪gradient f z, y - z⟫_ℝ ≤ ‖gradient f z‖ * ‖y - z‖ :=
    real_inner_le_norm (gradient f z) (y - z)
  have hyoung : ‖gradient f z‖ * ‖y - z‖ ≤
      (1 / 2) * ‖gradient f z‖ ^ 2 + (1 / 2) * ‖y - z‖ ^ 2 := by
    have hsq : 0 ≤ (‖gradient f z‖ - ‖y - z‖) ^ 2 := sq_nonneg _
    linarith
  have hgrad_sq : ‖gradient f z‖ ^ 2 ≤ 2 * L * (f z - f xstar) :=
    gradient_sq_le_gap hgrad L hL hlip xstar hmin z
  have hde_nonneg : 0 ≤ distanceEnergy xstar x w T := by
    unfold distanceEnergy
    positivity
  have hFz_nonneg : 0 ≤ f z - f xstar := sub_nonneg.mpr (hmin z)
  have hA_nonneg : 0 ≤ recursiveAverage (fun t => f (x t) - f xstar) η w T :=
    hFz_nonneg.trans hcomp_gap
  nlinarith

/-- Capped tail sum `U_t = 1 + S_t` with `S_t = ∑_{s = max 1 t}^T η_s`. -/
def cappedTail (η : ℕ → ℝ) (T t : ℕ) : ℝ := 1 + tailSum η T t

/-- Inverse capped tail weight `w_t = 1 / (1 + S_t)`. -/
def invCappedTail (η : ℕ → ℝ) (T t : ℕ) : ℝ := 1 / cappedTail η T t

lemma cappedTail_pos (η : ℕ → ℝ) (T t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i) : 0 < cappedTail η T t := by
  unfold cappedTail
  have := tailSum_nonneg η T t hη
  linarith

lemma cappedTail_terminal (η : ℕ → ℝ) (T : ℕ) : cappedTail η T (T + 1) = 1 := by
  simp [cappedTail, tailSum_terminal]

lemma cappedTail_rec (η : ℕ → ℝ) (T t : ℕ) (hη0 : η 0 = 0) (ht : t ≤ T) :
    cappedTail η T t = η t + cappedTail η T (t + 1) := by
  unfold cappedTail
  rw [tailSum_rec η T t hη0 ht]
  ring

lemma invCappedTail_pos (η : ℕ → ℝ) (T t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i) : 0 < invCappedTail η T t :=
  one_div_pos.mpr (cappedTail_pos η T t hη)

lemma cappedTail_mul_invCappedTail (η : ℕ → ℝ) (T t : ℕ)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i) :
    cappedTail η T t * invCappedTail η T t = 1 :=
  mul_one_div_cancel (cappedTail_pos η T t hη).ne'

lemma invCappedTail_mono (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (hη0 : η 0 = 0) (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i) :
    invCappedTail η T t ≤ invCappedTail η T (t + 1) := by
  have hηt : 0 ≤ η t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · rw [hη0]
    · exact hη t ht0 ht
  apply one_div_le_one_div_of_le (cappedTail_pos η T (t + 1) hη)
  rw [cappedTail_rec η T t hη0 ht]
  linarith

/-- Shifted step sizes starting at index `k ≥ 1`: `suffixStep η k 0 = 0`,
`suffixStep η k (i + 1) = η (k + i)`. -/
def suffixStep (η : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => η (k + i)

/-- Shifted capped tail sum starting at `k ≥ 1`:
`suffixCappedTail η T k 0 = cappedTail η T k`,
`suffixCappedTail η T k (i + 1) = cappedTail η T (k + i)`. -/
def suffixCappedTail (η : ℕ → ℝ) (T k : ℕ) : ℕ → ℝ
  | 0 => cappedTail η T k
  | i + 1 => cappedTail η T (k + i)

/-- Shifted inverse capped tail weights starting at `k ≥ 1`. -/
def suffixWeight (η : ℕ → ℝ) (T k i : ℕ) : ℝ := 1 / suffixCappedTail η T k i

/-- Shifted sequence of iterates starting at `x k`: `suffixIter x k i = x (k - 1 + i)` for `i ≥ 1`. -/
def suffixIter (x : ℕ → E) (k : ℕ) : ℕ → E
  | 0 => x k
  | i + 1 => x (k + i)

/-- Shifted sequence of errors starting at `e k`: `suffixErr e k (i + 1) = e (k + i)`. -/
def suffixErr (e : ℕ → E) (k : ℕ) : ℕ → E
  | 0 => 0
  | i + 1 => e (k + i)

/-- Capped quadratic weight on the suffix `Q_t^{(k)} = W η_t^2 / U_t` for `t = k + i`. -/
def suffixQuadWeight (η : ℕ → ℝ) (T k i : ℕ) : ℝ :=
  cappedTail η T k * (η (k + i)) ^ 2 / cappedTail η T (k + i)

/-- Scaled potential `P_{m'} = W A_{m'} + H_{m'}` on the suffix `k..T`. -/
def suffixPotential (f : E → ℝ) (xstar : E) (x : ℕ → E) (η : ℕ → ℝ) (T k m' : ℕ) : ℝ :=
  cappedTail η T k *
    (recursiveAverage (fun j => f (suffixIter x k j) - f xstar)
      (suffixStep η k) (suffixWeight η T k) m' +
    distanceEnergy xstar (suffixIter x k) (suffixWeight η T k) m')

/-- Predictable linear direction `w_t^{(k)} = (W η_t / U_{t-1}) (z_{t-1} - x_t)` on the suffix. -/
def suffixDirection (xstar : E) (x : ℕ → E) (η : ℕ → ℝ) (T k i : ℕ) : E :=
  (cappedTail η T k * η (k + i) * suffixWeight η T k i) •
    (comparator xstar (suffixIter x k) (suffixWeight η T k) i - x (k + i))

lemma suffixCappedTail_pos (η : ℕ → ℝ) (T k i : ℕ)
    (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) : 0 < suffixCappedTail η T k i := by
  cases i <;> exact cappedTail_pos η T _ hη

lemma suffixWeight_pos (η : ℕ → ℝ) (T k i : ℕ)
    (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) : 0 < suffixWeight η T k i :=
  one_div_pos.mpr (suffixCappedTail_pos η T k i hη)

lemma suffixCappedTail_mul_suffixWeight (η : ℕ → ℝ) (T k i : ℕ)
    (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) :
    suffixCappedTail η T k i * suffixWeight η T k i = 1 :=
  mul_one_div_cancel (suffixCappedTail_pos η T k i hη).ne'

lemma suffixCappedTail_rec (η : ℕ → ℝ) (T k i : ℕ) (hk : 1 ≤ k) (hi : k + i ≤ T + 1)
    (hη0 : η 0 = 0) :
    suffixCappedTail η T k i = suffixStep η k i + suffixCappedTail η T k (i + 1) := by
  cases i with
  | zero => simp [suffixCappedTail, suffixStep]
  | succ i =>
    simp only [suffixCappedTail, suffixStep]
    exact cappedTail_rec η T (k + i) hη0 (by omega)

lemma suffixWeight_mono (η : ℕ → ℝ) (T k i : ℕ) (hk : 1 ≤ k) (hi : k + i ≤ T + 1)
    (hη0 : η 0 = 0) (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) :
    suffixWeight η T k i ≤ suffixWeight η T k (i + 1) := by
  have hstep : 0 ≤ suffixStep η k i := by
    cases i with
    | zero => simp [suffixStep]
    | succ i => exact hη (k + i) (by omega) (by omega)
  apply one_div_le_one_div_of_le (suffixCappedTail_pos η T k (i + 1) hη)
  rw [suffixCappedTail_rec η T k i hk hi hη0]
  linarith

lemma suffixPotential_zero (f : E → ℝ) (xstar : E) (x : ℕ → E) (η : ℕ → ℝ) (T k : ℕ)
    (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) :
    suffixPotential f xstar x η T k 0 = (1 / 2) * ‖x k - xstar‖ ^ 2 := by
  unfold suffixPotential
  simp only [recursiveAverage, zero_add, distanceEnergy, comparator, suffixIter, Nat.add_zero]
  have hw0 : cappedTail η T k * suffixWeight η T k 0 = 1 :=
    suffixCappedTail_mul_suffixWeight η T k 0 hη
  rw [norm_sub_rev xstar (x k)]
  calc
    cappedTail η T k * (suffixWeight η T k 0 / 2 * ‖x k - xstar‖ ^ 2) =
      (cappedTail η T k * suffixWeight η T k 0) * (1 / 2 * ‖x k - xstar‖ ^ 2) := by ring
    _ = (1 / 2) * ‖x k - xstar‖ ^ 2 := by rw [hw0, one_mul]

lemma suffixPotential_nonneg {f : E → ℝ} (xstar : E) (hmin : ∀ u, f xstar ≤ f u)
    (x : ℕ → E) (η : ℕ → ℝ) (T k m' : ℕ) (hk : 1 ≤ k) (hm' : k + m' ≤ T + 1)
    (hη0 : η 0 = 0) (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) :
    0 ≤ suffixPotential f xstar x η T k m' := by
  unfold suffixPotential
  apply mul_nonneg (cappedTail_pos η T k hη).le
  apply add_nonneg
  · rw [recursiveAverage_eq_objectivePotential _ (suffixWeight η T k) (suffixStep η k)
      (suffixCappedTail η T k) m' rfl
      (fun i hi => suffixCappedTail_rec η T k i hk (by omega) hη0)
      (fun i _ => suffixCappedTail_mul_suffixWeight η T k i hη)]
    apply objectivePotential_nonneg
    · intro j
      exact sub_nonneg.mpr (hmin _)
    · exact (suffixWeight_pos η T k m' hη).le
    · cases m' with
      | zero => simp [suffixStep]
      | succ i => exact hη (k + i) (by omega) (by omega)
    · exact (suffixCappedTail_pos η T k (m' + 1) hη).le
    · intro i hi
      exact suffixWeight_mono η T k i hk (by omega) hη0 hη
  · unfold distanceEnergy
    exact mul_nonneg (div_nonneg (suffixWeight_pos η T k m' hη).le zero_le_two) (sq_nonneg _)

/-- Norm bound `‖w_t^{(k)}‖ ≤ √(2 Q_t^{(k)}) √(P_{t-1})` on the suffix. -/
lemma norm_suffixDirection_le {f : E → ℝ} (xstar : E) (hmin : ∀ u, f xstar ≤ f u)
    (x : ℕ → E) (η : ℕ → ℝ) (T k i : ℕ) (hk : 1 ≤ k) (hi : k + i ≤ T)
    (hη0 : η 0 = 0) (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) :
    ‖suffixDirection xstar x η T k i‖ ≤
      Real.sqrt (2 * suffixQuadWeight η T k i) *
        Real.sqrt (suffixPotential f xstar x η T k i) := by
  have hW : 0 < cappedTail η T k := cappedTail_pos η T k hη
  have hηi : 0 ≤ η (k + i) := hη (k + i) (by omega) (by omega)
  have hwi : 0 < suffixWeight η T k i := suffixWeight_pos η T k i hη
  have hwi1 : 0 < suffixWeight η T k (i + 1) := suffixWeight_pos η T k (i + 1) hη
  have hwmono : suffixWeight η T k i ≤ suffixWeight η T k (i + 1) :=
    suffixWeight_mono η T k i hk (by omega) hη0 hη
  have hA_nonneg : 0 ≤ recursiveAverage (fun j => f (suffixIter x k j) - f xstar)
      (suffixStep η k) (suffixWeight η T k) i := by
    rw [recursiveAverage_eq_objectivePotential _ (suffixWeight η T k) (suffixStep η k)
      (suffixCappedTail η T k) i rfl
      (fun j hj => suffixCappedTail_rec η T k j hk (by omega) hη0)
      (fun j _ => suffixCappedTail_mul_suffixWeight η T k j hη)]
    apply objectivePotential_nonneg
    · intro j; exact sub_nonneg.mpr (hmin _)
    · exact hwi.le
    · cases i with
      | zero => simp [suffixStep]
      | succ j => exact hη (k + j) (by omega) (by omega)
    · exact (suffixCappedTail_pos η T k (i + 1) hη).le
    · intro j hj; exact suffixWeight_mono η T k j hk (by omega) hη0 hη
  have hQ_eq : suffixQuadWeight η T k i =
      cappedTail η T k * (η (k + i)) ^ 2 * suffixWeight η T k (i + 1) := by
    unfold suffixQuadWeight suffixWeight suffixCappedTail
    ring
  have hsq : ‖suffixDirection xstar x η T k i‖ ^ 2 ≤
      (2 * suffixQuadWeight η T k i) * suffixPotential f xstar x η T k i := by
    unfold suffixDirection
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow, hQ_eq]
    have h1 : suffixWeight η T k i ^ 2 ≤ suffixWeight η T k (i + 1) * suffixWeight η T k i := by
      nlinarith
    have h2 : (cappedTail η T k * η (k + i) * suffixWeight η T k i) ^ 2 *
        ‖comparator xstar (suffixIter x k) (suffixWeight η T k) i - x (k + i)‖ ^ 2 ≤
        (2 * (cappedTail η T k * η (k + i) ^ 2 * suffixWeight η T k (i + 1))) *
        (cappedTail η T k * distanceEnergy xstar (suffixIter x k) (suffixWeight η T k) i) := by
      have hiter : suffixIter x k (i + 1) = x (k + i) := rfl
      unfold distanceEnergy
      rw [hiter]
      have hd : 0 ≤ ‖comparator xstar (suffixIter x k) (suffixWeight η T k) i - x (k + i)‖ ^ 2 :=
        sq_nonneg _
      have hc : 0 ≤ cappedTail η T k ^ 2 * η (k + i) ^ 2 := by positivity
      have hm := mul_le_mul_of_nonneg_left h1 hc
      have hm' := mul_le_mul_of_nonneg_right hm hd
      linarith
    have h3 : cappedTail η T k * distanceEnergy xstar (suffixIter x k) (suffixWeight η T k) i ≤
        suffixPotential f xstar x η T k i := by
      unfold suffixPotential
      nlinarith
    have hQ0 : 0 ≤ 2 * (cappedTail η T k * η (k + i) ^ 2 * suffixWeight η T k (i + 1)) := by
      positivity
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hQ0)
  have hQ0' : 0 ≤ 2 * suffixQuadWeight η T k i := by
    rw [hQ_eq]
    positivity
  rw [← Real.sqrt_mul hQ0', ← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt hsq

/-- Equation (53) (`eq:capped-partial-potential`): partial-sum bound for
the suffix potential on `k..T`. -/
theorem suffix_partial_sum_potential {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : E) (x e : ℕ → E) (η : ℕ → ℝ) (T k m' : ℕ)
    (hk : 1 ≤ k) (hm' : k + m' ≤ T + 1)
    (hη0 : η 0 = 0) (hη : ∀ j, 1 ≤ j → j ≤ T → 0 < η j)
    (hstep : ∀ j, 1 ≤ j → j ≤ T → η j ≤ 1 / (2 * L))
    (hupdate : ∀ i < m',
      x (k + i + 1) = x (k + i) - η (k + i) • (gradient f (x (k + i)) + e (k + i))) :
    suffixPotential f xstar x η T k m' ≤
      suffixPotential f xstar x η T k 0 +
        ∑ i ∈ Finset.range m',
          (2 * suffixQuadWeight η T k i * ‖e (k + i)‖ ^ 2 +
            ⟪e (k + i), suffixDirection xstar x η T k i⟫_ℝ) := by
  have hη_nn : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j := fun j hj1 hjT => (hη j hj1 hjT).le
  have hrec := recursive_partial_sum_potential hconv hdiff L hL hlip xstar
    (suffixIter x k) (suffixErr e k) (suffixWeight η T k) (suffixStep η k) (suffixCappedTail η T k) m'
    (fun i _ => suffixWeight_pos η T k i hη_nn)
    (fun i hi => suffixWeight_mono η T k i hk (by omega) hη0 hη_nn)
    rfl
    (fun i hi => hη (k + i) (by omega) (by omega))
    (fun i hi => hstep (k + i) (by omega) (by omega))
    (fun i hi => suffixCappedTail_rec η T k i hk (by omega) hη0)
    (fun i _ => suffixCappedTail_mul_suffixWeight η T k i hη_nn)
    (fun i hi => by
      simp only [suffixIter, suffixStep, suffixErr]
      exact hupdate i hi)
  have hW : 0 ≤ cappedTail η T k := (cappedTail_pos η T k hη_nn).le
  have hmul := mul_le_mul_of_nonneg_left hrec hW
  unfold suffixPotential
  refine hmul.trans_eq ?_
  rw [mul_add, Finset.mul_sum]
  congr 1
  · simp [recursiveAverage]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [suffixStep, suffixErr, suffixIter, suffixQuadWeight, suffixDirection,
      suffixWeight, suffixCappedTail]
    rw [real_inner_smul_right]
    ring

/-- Endpoint conversion on the suffix `k..T`: at `m' = T + 1 - k`,
`f (x (T + 1)) - f xstar ≤ (1 + L) * suffixPotential f xstar x η T k (T + 1 - k) / cappedTail η T k`. -/
theorem suffix_endpoint_bound {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hlip : ∀ u v, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : E) (hmin : ∀ u, f xstar ≤ f u)
    (x : ℕ → E) (η : ℕ → ℝ) (T k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T)
    (hη0 : η 0 = 0) (hη : ∀ j, 1 ≤ j → j ≤ T → 0 ≤ η j) :
    f (x (T + 1)) - f xstar ≤
      (1 + L) * suffixPotential f xstar x η T k (T + 1 - k) / cappedTail η T k := by
  let m' := T + 1 - k
  have hkm : k + m' = T + 1 := by omega
  have hstep_m' : 0 ≤ suffixStep η k m' := by
    have hm'pos : m' = (T - k) + 1 := by omega
    rw [hm'pos]
    simp only [suffixStep]
    exact hη (k + (T - k)) (by omega) (by omega)
  have h := potential_endpoint_bound hconv hdiff L hL hlip xstar hmin
    (suffixIter x k) (suffixWeight η T k) (suffixStep η k) (suffixCappedTail η T k) m'
    (fun i _ => suffixWeight_pos η T k i hη)
    (fun i hi => suffixWeight_mono η T k i hk (by omega) hη0 hη)
    rfl
    hstep_m'
    (fun i hi => suffixCappedTail_rec η T k i hk (by omega) hη0)
    (fun i _ => suffixCappedTail_mul_suffixWeight η T k i hη)
    (by
      show suffixCappedTail η T k (m' + 1) = 1
      simp only [suffixCappedTail, hkm, cappedTail_terminal])
  have hx : suffixIter x k (m' + 1) = x (T + 1) := by
    simp only [suffixIter, hkm]
  rw [hx] at h
  have hW : 0 < cappedTail η T k := cappedTail_pos η T k hη
  unfold suffixPotential
  rw [mul_left_comm (1 + L) (cappedTail η T k), mul_div_cancel_left₀ _ hW.ne']
  exact h

end
end ClippedSGD.SuffixPotential
