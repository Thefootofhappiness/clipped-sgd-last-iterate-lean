import ClippedSGD.MomentumParameters
import ClippedSGD.MomentumAsymptotics

/-! Parameters of the time-uniform lower-bound instance: the exponents, the rare-event
amplitude and probability, the logarithmic envelope, and the choice of the horizon. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ClippedSGD.AnytimeLowerParameters

def beta (p : ℝ) : ℝ := 2*(p-1)/(3*p-1)
def qExponent (p : ℝ) : ℝ := p/(p-1)
def rareA (p μ : ℝ) : ℝ := (2*μ)^(-1/(p-1))
def rareProb (p μ : ℝ) : ℝ := μ/rareA p μ
def envelope (D u : ℝ) (t : ℕ) : ℝ := D*((t+1:ℕ):ℝ)^(-u)
def probabilityConstant (D p : ℝ) : ℝ :=
  (2:ℝ)^(1/(p-1))*(8*D)^(qExponent p)

lemma qExponent_eq (p : ℝ) (hp : 1<p) : qExponent p=1+1/(p-1) := by
  unfold qExponent
  have hp0 : p-1≠0 := by linarith
  field_simp

lemma qExponent_pos (p : ℝ) (hp : 1<p) : 0<qExponent p :=
  div_pos (by linarith) (by linarith)

lemma beta_eq (p : ℝ) (hp : 1<p) : beta p=1/(qExponent p+1/2) := by
  have hp0 : p-1≠0 := by linarith
  have hp3 : 3*p-1≠0 := by linarith
  have hq : qExponent p+1/2≠0 := ne_of_gt (by linarith [qExponent_pos p hp])
  apply (eq_div_iff hq).mpr
  unfold beta qExponent
  field_simp
  ring

lemma beta_pos (p : ℝ) (hp : 1<p) : 0<beta p := by
  rw [beta_eq p hp]
  exact one_div_pos.mpr (by linarith [qExponent_pos p hp])

lemma beta_lt_one (p : ℝ) (hp : 1<p) : beta p<1 := by
  unfold beta
  apply (div_lt_one (by linarith : 0<3*p-1)).mpr
  linarith

lemma rareA_pos {p μ : ℝ} (hμ : 0<μ) : 0<rareA p μ :=
  Real.rpow_pos_of_pos (by positivity) _

lemma rareA_eq {p μ : ℝ} (hμ : 0<μ) :
    rareA p μ=(1/(2*μ))^(1/(p-1)) := by
  unfold rareA
  rw [one_div, Real.inv_rpow (by positivity : 0≤2*μ), ←Real.rpow_neg (by positivity)]
  congr 1
  ring

lemma rareA_ge_one {p μ : ℝ} (hp : 1<p) (hμ : 0<μ) (hμsmall : μ≤1/2) :
    1≤rareA p μ := by
  rw [rareA_eq hμ]
  apply Real.one_le_rpow
  · apply (le_div_iff₀ (by positivity : 0<2*μ)).mpr
    linarith
  · exact one_div_nonneg.mpr (by linarith)

lemma signal_le_amplitude {p μ : ℝ} (hp : 1<p) (hμ : 0<μ) (hμsmall : μ≤1/2) :
    μ≤rareA p μ := by
  have := rareA_ge_one hp hμ hμsmall
  linarith

lemma rareProb_pos {p μ : ℝ} (hμ : 0<μ) : 0<rareProb p μ :=
  div_pos hμ (rareA_pos hμ)

lemma rareProb_le_one {p μ : ℝ} (hp : 1<p) (hμ : 0<μ) (hμsmall : μ≤1/2) :
    rareProb p μ≤1 := by
  exact (div_le_one (rareA_pos hμ)).mpr (signal_le_amplitude hp hμ hμsmall)

lemma rare_centering {p μ : ℝ} (hμ : 0<μ) : rareProb p μ*rareA p μ=μ :=
  div_mul_cancel₀ _ (rareA_pos hμ).ne'

lemma rare_moment_identity {p μ : ℝ} (hp : 1<p) (hμ : 0<μ) :
    2*μ*(rareA p μ)^(p-1)=1 := by
  have hp0 : p-1≠0 := by linarith
  unfold rareA
  rw [←Real.rpow_mul (by positivity : 0≤2*μ)]
  have he : (-1/(p-1))*(p-1)=(-1:ℝ) := by field_simp
  rw [he, Real.rpow_neg_one]
  exact mul_inv_cancel₀ (by positivity)

lemma rareProb_power {p μ : ℝ} (hp : 1<p) (hμ : 0<μ) :
    rareProb p μ=(2:ℝ)^(1/(p-1))*μ^(qExponent p) := by
  unfold rareProb rareA
  rw [div_eq_mul_inv, ←Real.rpow_neg (by positivity : 0≤2*μ)]
  have he : -(-1/(p-1))=1/(p-1) := by ring
  rw [he, Real.mul_rpow (by norm_num : (0:ℝ)≤2) hμ.le,
    qExponent_eq p hp, Real.rpow_add hμ, Real.rpow_one]
  ring

lemma rareProb_horizon (D p u : ℝ) (hD : 0<D) (hp : 1<p)
    (N : ℕ) (hN : 0<N) :
    rareProb p (8*D*(N:ℝ)^(-u))=
      probabilityConstant D p*(N:ℝ)^(-u*qExponent p) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [rareProb_power hp (by positivity),
    Real.mul_rpow (by positivity : (0:ℝ)≤8*D) (Real.rpow_nonneg hn.le (-u)),
    ←Real.rpow_mul hn.le]
  unfold probabilityConstant
  ring

lemma envelope_sqrt (D u : ℝ) (hD : 0≤D) (j : ℕ) :
    Real.sqrt (2*envelope D u j)=Real.sqrt (2*D)*((j+1:ℕ):ℝ)^(-u/2) := by
  unfold envelope
  rw [←mul_assoc, Real.sqrt_mul (by positivity)]
  congr 1
  rw [Real.sqrt_eq_rpow, ←Real.rpow_mul (by positivity : (0:ℝ)≤((j+1:ℕ):ℝ))]
  congr 1
  ring

def budget (D p u : ℝ) (N : ℕ) : ℝ :=
  2*rareProb p (8*D*(N:ℝ)^(-u))*
    (∑t∈Finset.range N, (8*D*(N:ℝ)^(-u)+Real.sqrt (2*envelope D u t)))

def budgetExpression (D p u : ℝ) (N : ℕ) : ℝ :=
  (16*D*probabilityConstant D p)*(N:ℝ)^(1-u*(qExponent p+1))+
  (2*Real.sqrt (2*D)*probabilityConstant D p)*
    ((N:ℝ)^(-u*qExponent p)*(∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-u/2)))

lemma budget_eq (D p u : ℝ) (hD : 0<D) (hp : 1<p)
    (N : ℕ) (hN : 0<N) : budget D p u N=budgetExpression D p u N := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  unfold budget budgetExpression
  rw [rareProb_horizon D p u hD hp N hN]
  simp_rw [envelope_sqrt D u hD.le]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ←Finset.mul_sum]
  have hexp : 1-u*(qExponent p+1)=(1+(-u*qExponent p))+(-u) := by ring
  rw [hexp, Real.rpow_add hn, Real.rpow_add hn, Real.rpow_one]
  ring

/-- Every `r > β_p` admits `u` with `β_p < u < r` and `u < 1`. -/
theorem select_exponent (p r : ℝ) (hp : 1<p) (hr : beta p<r) :
    ∃u : ℝ, beta p<u ∧ u<r ∧ u<1 := by
  let u := (beta p+min r 1)/2
  have hb : beta p<min r 1 := lt_min hr (beta_lt_one p hp)
  refine ⟨u,?_,?_,?_⟩ <;> dsimp [u]
  · linarith
  · linarith [min_le_left r (1:ℝ)]
  · linarith [min_le_right r (1:ℝ)]

def logCoefficient (C m : ℝ) (N : ℕ) : ℝ :=
  C*(Real.log (Real.exp 1*(N:ℝ)))^m

lemma log_exp_mul_pos {x : ℝ} (hx : 1≤x) : 0<Real.log (Real.exp 1*x) := by
  have hx0 : 0<x := by linarith
  rw [Real.log_mul (Real.exp_pos _).ne' hx0.ne',Real.log_exp]
  linarith [Real.log_nonneg hx]

lemma logCoefficient_pos (C m : ℝ) (hC : 0<C) {N : ℕ} (hN : 0<N) :
    0<logCoefficient C m N := by
  unfold logCoefficient
  exact mul_pos hC (Real.rpow_pos_of_pos (log_exp_mul_pos (by exact_mod_cast hN)) _)

/-- `(log(eN))^m N^e → 0` for `e < 0`. -/
lemma log_power_decay (m e : ℝ) (hm : 0≤m) (he : e<0) :
    Tendsto (fun N : ℕ => (Real.log (Real.exp 1*(N:ℝ)))^m*(N:ℝ)^e)
      atTop (𝓝 0) := by
  obtain ⟨D,hD,hbound⟩ := MomentumParameters.logarithmic_envelope_dominated
    1 (-e) (-e/2) m (by norm_num) (by linarith) hm
  apply squeeze_zero' ?_ ?_ (MomentumAsymptotics.power_decay D (e/2) (by linarith))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact mul_nonneg (Real.rpow_nonneg
      (log_exp_mul_pos (by exact_mod_cast hN : (1:ℝ)≤N)).le m)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have h := hbound (N:ℝ) (by exact_mod_cast hN)
    simpa only [one_mul,mul_one,neg_neg,neg_div,mul_comm] using h

lemma coefficient_power_decay (C m a e : ℝ) (hC : 0<C) (hm : 0≤m)
    (ha : 0≤a) (he : e<0) :
    Tendsto (fun N : ℕ => (logCoefficient C m N)^a*(N:ℝ)^e) atTop (𝓝 0) := by
  have h := (log_power_decay (m*a) e (mul_nonneg hm ha) he).const_mul (C^a)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hlog := (log_exp_mul_pos (by exact_mod_cast hN : (1:ℝ)≤N)).le
  dsimp only [logCoefficient]
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hlog m),←Real.rpow_mul hlog]
  ring

lemma coefficient_weighted_sum_tendsto (C m a s b : ℝ) (hC : 0<C)
    (hm : 0≤m) (ha : 0≤a) (hb : 0<b) (hs : 1-s<b) :
    Tendsto (fun N : ℕ => (logCoefficient C m N)^a*(N:ℝ)^(-b)*
      (∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-s))) atTop (𝓝 0) := by
  let r := (max 0 (1-s)+b)/2
  have hmax : max 0 (1-s)<b := max_lt hb hs
  have hr : 0≤r := by dsimp [r];linarith [le_max_left (0:ℝ) (1-s)]
  have hrs : 1-s<r := by dsimp [r];linarith [le_max_right (0:ℝ) (1-s)]
  have hrb : r<b := by dsimp [r];linarith
  let K := ∑'j : ℕ,((j+1:ℕ):ℝ)^(-s-r)
  have hlim := (coefficient_power_decay C m a (r-b) hC hm ha (by linarith)).mul_const K
  simp only [zero_mul] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (logCoefficient_pos C m hC hN).le _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have h := mul_le_mul_of_nonneg_left
      (MomentumAsymptotics.weighted_power_sum_bound hr hrs N hN)
      (mul_nonneg (Real.rpow_nonneg (logCoefficient_pos C m hC hN).le a)
        (Real.rpow_nonneg (Nat.cast_nonneg N) (-b)))
    have heq : (logCoefficient C m N)^a*(N:ℝ)^(-b)*((N:ℝ)^r*K)=
        (logCoefficient C m N)^a*(N:ℝ)^(r-b)*K := by
      rw [mul_assoc _ ((N:ℝ)^(-b)),←mul_assoc ((N:ℝ)^(-b)),
        ←Real.rpow_add (by exact_mod_cast hN : (0:ℝ)<N)]
      have he : -b+r=r-b := by ring
      rw [he]
      ring
    exact h.trans_eq heq

lemma budget_coefficient_form (D p u : ℝ) (hD : 0<D) (hp : 1<p)
    (N : ℕ) (hN : 0<N) :
    budget D p u N=
      (16*((2:ℝ)^(1/(p-1))*8^(qExponent p)))*D^(qExponent p+1)*
        (N:ℝ)^(1-u*(qExponent p+1))+
      (2*Real.sqrt 2*((2:ℝ)^(1/(p-1))*8^(qExponent p)))*D^(qExponent p+1/2)*
        ((N:ℝ)^(-u*qExponent p)*(∑j∈Finset.range N,((j+1:ℕ):ℝ)^(-u/2))) := by
  rw [budget_eq D p u hD hp N hN]
  unfold budgetExpression probabilityConstant
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤8) hD.le,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_eq_rpow,
    Real.rpow_add hD,Real.rpow_add hD,Real.rpow_one]
  simp only [Real.sqrt_eq_rpow]
  ring

/-- The arrival budget of the logarithmic envelope tends to zero when `u > β_p`. -/
theorem log_budget_tendsto (C m p u : ℝ) (hC : 0<C) (hm : 0≤m)
    (hp : 1<p) (hthreshold : beta p<u) :
    Tendsto (fun N => budget (logCoefficient C m N) p u N) atTop (𝓝 0) := by
  have hu : 0<u := lt_trans (beta_pos p hp) hthreshold
  have hq : 0<qExponent p := qExponent_pos p hp
  have ht : 1/(qExponent p+1/2)<u := by rwa [←beta_eq p hp]
  have ht' : 1<u*(qExponent p+1/2) := (div_lt_iff₀ (by linarith)).mp ht
  have hfirst := (coefficient_power_decay C m (qExponent p+1)
    (1-u*(qExponent p+1)) hC hm (by linarith) (by nlinarith)).const_mul
      (16*((2:ℝ)^(1/(p-1))*8^(qExponent p)))
  have hsecond := (coefficient_weighted_sum_tendsto C m (qExponent p+1/2)
    (u/2) (u*qExponent p) hC hm (by linarith) (mul_pos hu hq) (by nlinarith)).const_mul
      (2*Real.sqrt 2*((2:ℝ)^(1/(p-1))*8^(qExponent p)))
  have hsum := hfirst.add hsecond
  simp only [mul_zero,add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  rw [budget_coefficient_form _ p u (logCoefficient_pos C m hC hN) hp N hN]
  simp only [neg_mul,neg_div]
  ring

/-- On the first `N` times, the rate is dominated by the envelope with coefficient
`logCoefficient C m N`. -/
lemma log_envelope_dominates_prefix (C m r u : ℝ) (hC : 0<C)
    (hm : 0≤m) (hur : u<r) {N t : ℕ} (ht : t<N) :
    C*((t+1:ℕ):ℝ)^(-r)*(Real.log (Real.exp 1*((t+1:ℕ):ℝ)))^m≤
      envelope (logCoefficient C m N) u t := by
  have ht1 : (1:ℝ)≤((t+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le t)
  have ht0 : (0:ℝ)<((t+1:ℕ):ℝ) := by positivity
  have htN : ((t+1:ℕ):ℝ)≤(N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt ht
  have hlog := log_exp_mul_pos ht1
  have hlogle : Real.log (Real.exp 1*((t+1:ℕ):ℝ))≤Real.log (Real.exp 1*(N:ℝ)) :=
    Real.log_le_log (mul_pos (Real.exp_pos _) ht0)
      (mul_le_mul_of_nonneg_left htN (Real.exp_pos _).le)
  have hpow := Real.rpow_le_rpow_of_exponent_le ht1 (show -r≤-u by linarith)
  have hlogs := Real.rpow_le_rpow hlog.le hlogle hm
  have h := mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) hlogs
    (Real.rpow_nonneg hlog.le m) (by positivity : 0≤C*((t+1:ℕ):ℝ)^(-u))
  dsimp only [envelope,logCoefficient]
  nlinarith only [h]

/-- A horizon `N` and a signal `μ` for which the rare-event parameters are admissible and
the arrival budget is below `1 - 2δ`. -/
theorem exists_log_parameters (C m p u δ : ℝ) (hC : 0<C) (hm : 0≤m) (hp : 1<p)
    (hδ : δ<1/2) (hthreshold : beta p<u) :
    ∃ (N : ℕ) (μ : ℝ), 0<N ∧ 0<μ ∧ μ≤1/2 ∧
      1≤rareA p μ ∧ μ≤rareA p μ ∧ 0<rareProb p μ ∧ rareProb p μ≤1 ∧
      rareProb p μ*rareA p μ=μ ∧ 2*μ*(rareA p μ)^(p-1)=1 ∧
      envelope (logCoefficient C m N) u (N-1)<μ/4 ∧
      2*rareProb p μ*(∑t∈Finset.range N,
        (μ+Real.sqrt (2*envelope (logCoefficient C m N) u t)))<1-2*δ := by
  have hu : 0<u := lt_trans (beta_pos p hp) hthreshold
  have hsignal := (coefficient_power_decay C m 1 (-u) hC hm (by norm_num)
    (by linarith)).const_mul 8
  simp only [Real.rpow_one,mul_zero] at hsignal
  have hsmall := hsignal.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hnumeric := (log_budget_tendsto C m p u hC hm hp hthreshold).eventually
    (gt_mem_nhds (by linarith : (0:ℝ)<1-2*δ))
  obtain ⟨N,hN,hsmallN,hnumericN⟩ :=
    ((eventually_gt_atTop (0:ℕ)).and (hsmall.and hnumeric)).exists
  let D := logCoefficient C m N
  have hD : 0<D := logCoefficient_pos C m hC hN
  let μ := 8*D*(N:ℝ)^(-u)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hμ : 0<μ := by dsimp [μ]; positivity
  have hμsmall : μ≤1/2 := by dsimp [μ,D]; nlinarith only [hsmallN]
  have hend : envelope D u (N-1)<μ/4 := by
    unfold envelope
    rw [Nat.sub_add_cancel hN]
    dsimp only [μ]
    nlinarith [mul_pos hD (Real.rpow_pos_of_pos hn (-u))]
  exact ⟨N,μ,hN,hμ,hμsmall,rareA_ge_one hp hμ hμsmall,
    signal_le_amplitude hp hμ hμsmall,rareProb_pos hμ,rareProb_le_one hp hμ hμsmall,
    rare_centering hμ,rare_moment_identity hp hμ,hend,hnumericN⟩

end ClippedSGD.AnytimeLowerParameters
