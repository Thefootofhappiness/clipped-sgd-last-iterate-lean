import ClippedSGD.AnytimeLowerParameters

/-! The forgetting windows `⌈Λ (j+1)^a log N⌉`. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace ClippedSGD.MomentumLogWindow
open MomentumParameters

def window (Λ a : ℝ) (N j : ℕ) : ℕ :=
  ⌈Λ*(j+1 : ℝ)^a*Real.log N⌉₊

lemma window_upper (Λ a : ℝ) (hΛ : 0 ≤ Λ) (N j : ℕ) (hN : 1 ≤ N) :
    (window Λ a N j : ℝ) ≤ Λ*(j+1 : ℝ)^a*Real.log N+1 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (Nat.ceil_lt_add_one (mul_nonneg (by positivity) (Real.log_nonneg hn))).le

lemma late_power_bound (e θ : ℝ) (he : e ≤ 0) (N j : ℕ)
    (hN : 0 < N) (hj : earlyCutoff θ N ≤ j) :
    (j+1 : ℝ)^e ≤ (N : ℝ)^(θ*e) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_mul hn.le]
  exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn θ)
    (late_time_lower θ N j hj).le he

lemma normalized_window_bound (Λ a θ : ℝ) (hΛ : 0 ≤ Λ) (ha : a ≤ 1)
    (N j : ℕ) (hN : 0 < N) (hj : earlyCutoff θ N ≤ j) :
    (window Λ a N j : ℝ)/(j+1) ≤
      Λ*Real.log N*(N : ℝ)^(θ*(a-1))+(N : ℝ)^(-θ) := by
  have hj0 : (0 : ℝ) < j+1 := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw := div_le_div_of_nonneg_right (window_upper Λ a hΛ N j hN) hj0.le
  calc
    _ ≤ (Λ*(j+1 : ℝ)^a*Real.log N+1)/(j+1) := hw
    _ = Λ*Real.log N*(j+1 : ℝ)^(a-1)+(j+1 : ℝ)^(-1 : ℝ) := by
      rw [Real.rpow_sub hj0, Real.rpow_one, Real.rpow_neg_one]
      ring
    _ ≤ Λ*Real.log N*(N : ℝ)^(θ*(a-1))+(N : ℝ)^(θ*(-1)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (late_power_bound (a-1) θ (by linarith) N j hN hj)
          (mul_nonneg hΛ (Real.log_nonneg hn1))
      · exact late_power_bound (-1) θ (by norm_num) N j hN hj
    _ = _ := by ring_nf

lemma log_decay (e : ℝ) (he : e < 0) :
    Tendsto (fun N : ℕ => Real.log N*(N : ℝ)^e) atTop (𝓝 0) := by
  have hh := AnytimeLowerParameters.log_power_decay 1 e (by norm_num) he
  simp only [Real.rpow_one] at hh
  apply squeeze_zero' ?_ ?_ hh
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < N))
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

theorem eventually_short_windows (Λ a θ : ℝ) (hΛ : 0 ≤ Λ)
    (ha : a < 1) (hθ : 0 < θ) :
    ∀ᶠ N : ℕ in atTop, ∀ j, earlyCutoff θ N ≤ j → window Λ a N j ≤ j+1 := by
  have he : θ*(a-1) < 0 := mul_neg_of_pos_of_neg hθ (by linarith)
  have hlim := ((log_decay _ he).const_mul Λ).add (MomentumAsymptotics.power_decay 1 (-θ) (by linarith))
  simp only [mul_one, one_mul, mul_zero, add_zero] at hlim
  have hh := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hsmall hN j hj
  simp only [← mul_assoc] at hsmall
  have hb := (normalized_window_bound Λ a θ hΛ ha.le N j hN hj).trans_lt hsmall
  have hw : (window Λ a N j : ℝ) < j+1 := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < j+1)).mp hb
    simpa using this
  exact_mod_cast hw.le

lemma small_window_sq_bound (D Λ u a θ : ℝ) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ)
    (hau : a ≤ u) (hu : 0 ≤ u) (N j : ℕ) (hN : 0 < N)
    (hj : earlyCutoff θ N ≤ j) :
    (Real.sqrt (2*envelope D u (j+1))*Real.sqrt (window Λ a N j : ℝ))^2 ≤
      (2*D*Λ)*Real.log N*(N : ℝ)^(θ*(a-u))+2*D*(N : ℝ)^(-θ*u) := by
  have hj0 : (0 : ℝ) < j+1 := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [mul_pow, Real.sq_sqrt (by unfold envelope; positivity), Real.sq_sqrt (by positivity),
    envelope_of_pos D u (j+1) (by omega)]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ 2*(D*(j+1 : ℝ)^(-u))*(Λ*(j+1 : ℝ)^a*Real.log N+1) :=
      mul_le_mul_of_nonneg_left (window_upper Λ a hΛ N j hN) (by positivity)
    _ = (2*D*Λ)*Real.log N*(j+1 : ℝ)^(a-u)+2*D*(j+1 : ℝ)^(-u) := by
      rw [show a-u = -u+a by ring, Real.rpow_add hj0]
      ring
    _ ≤ (2*D*Λ)*Real.log N*(N : ℝ)^(θ*(a-u))+2*D*(N : ℝ)^(θ*(-u)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (late_power_bound (a-u) θ (by linarith) N j hN hj)
          (by positivity)
      · exact mul_le_mul_of_nonneg_left (late_power_bound (-u) θ (by linarith) N j hN hj)
          (by positivity)
    _ = _ := by ring_nf

theorem eventually_small_windows (D Λ u a θ B : ℝ) (hD : 0 ≤ D) (hΛ : 0 ≤ Λ)
    (hau : a < u) (hu : 0 < u) (hθ : 0 < θ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, ∀ j, earlyCutoff θ N ≤ j →
      Real.sqrt (2*envelope D u (j+1))*Real.sqrt (window Λ a N j : ℝ) ≤ B/2 := by
  have hl := ((log_decay (θ*(a-u)) (mul_neg_of_pos_of_neg hθ (by linarith))).const_mul (2*D*Λ)).add
    (MomentumAsymptotics.power_decay (2*D) (-θ*u) (mul_neg_of_neg_of_pos (by linarith) hu))
  simp only [mul_zero, add_zero] at hl
  have hh := hl.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (B/2)^2))
  filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hsmall hN j hj
  simp only [← mul_assoc] at hsmall
  have hs := (small_window_sq_bound D Λ u a θ hD hΛ hau.le hu.le N j hN hj).trans_lt hsmall
  have hn : 0 ≤ Real.sqrt (2*envelope D u (j+1))*Real.sqrt (window Λ a N j : ℝ) := by positivity
  nlinarith

theorem window_damping_lower (ρ P a : ℝ) (hρ : 0 < ρ) (hP : 0 ≤ P)
    (N j : ℕ) (hN : 1 ≤ N) :
    P*Real.log N ≤ (window ((3:ℝ)^a*P/ρ) a N j : ℝ)*windowGap ρ a j := by
  have hj0 : (0 : ℝ) < j+1 := by positivity
  have hl := Nat.le_ceil (((3:ℝ)^a*P/ρ)*(j+1 : ℝ)^a*Real.log N)
  have hc : 0 ≤ windowGap ρ a j := by unfold windowGap; positivity
  have hh := mul_le_mul_of_nonneg_right hl hc
  change _ ≤ _ at hh
  have he : (((3:ℝ)^a*P/ρ)*(j+1 : ℝ)^a*Real.log N)*windowGap ρ a j = P*Real.log N := by
    rw [windowGap, Real.mul_rpow (by norm_num : (0:ℝ)≤3) hj0.le,
      Real.rpow_neg (by norm_num : (0:ℝ)≤3), Real.rpow_neg hj0.le]
    field_simp
    ring
  rw [he] at hh
  exact hh

theorem exponential_tail (ρ P a : ℝ) (hρ : 0 < ρ) (hP : 0 ≤ P)
    (N j : ℕ) (hN : 0 < N) :
    Real.exp (-(window ((3:ℝ)^a*P/ρ) a N j : ℝ)*windowGap ρ a j) ≤ (N:ℝ)^(-P) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  have hh := window_damping_lower ρ P a hρ hP N j hN
  nlinarith

end ClippedSGD.MomentumLogWindow
