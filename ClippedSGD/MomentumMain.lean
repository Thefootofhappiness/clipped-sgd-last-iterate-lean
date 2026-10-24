import ClippedSGD.MomentumHorizon
import ClippedSGD.MomentumLegalOracle
import ClippedSGD.MomentumInfiniteIID

/-! The dimension-uniform momentum lower bound. A controller reads the whole gradient
transcript and an independent seed. -/
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ClippedSGD.MomentumMain
open MomentumGeometry MomentumProbability MomentumOracle MomentumRun
open MomentumFiniteLower MomentumParameters
noncomputable section

variable {S : Type*} [MeasurableSpace S]

def betaExponent (p : ℝ) : ℝ := 1/(qExponent p+1/2)

/-- `betaExponent p` is the exponent $2(p-1)/(3p-1)$ of the paper. -/
lemma betaExponent_formula (p : ℝ) (hp : 1 < p) :
    betaExponent p = 2*(p-1)/(3*p-1) := by
  unfold betaExponent qExponent
  have h1 : p-1 ≠ 0 := by linarith
  have h2 : 3*p-1 ≠ 0 := by linarith
  have h3 : p/(p-1)+1/2 ≠ 0 := ne_of_gt (add_pos (div_pos (by linarith) (by linarith)) (by norm_num))
  apply (div_eq_div_iff h3 h2).mpr
  field_simp [h1]
  ring

def proposedRate (C r k : ℝ) (t : ℕ) : ℝ :=
  C*(t : ℝ)^(-r)*(Real.log (Real.exp 1*(t : ℝ)))^k

/-- Constraints on the controls, with constants shared by all dimensions, histories, and
seeds. -/
structure UniformControls (R : (d : ℕ) → Rule (Space d) S)
    (ρ a H h : ℝ) (t₀ : ℕ) : Prop where
  measurable : ∀ d t, Measurable (R d t)
  bound : ∀ d t hist seed, let q := R d t (hist, seed)
    0 ≤ damping q ∧ damping q < 1 ∧ 0 ≤ scale q ∧ scale q ≤ 1 ∧
      0 ≤ gain q ∧ gain q ≤ H*(t+2 : ℝ)^h
  forget : ∀ d t, t₀ ≤ t → ∀ hist seed,
    damping (R d t (hist, seed)) ≤ 1-ρ*(t+2 : ℝ)^(-a)

/-- The failure part of `main_obstruction`. -/
theorem finite_prefix_rate_failure (ν : Measure S) [IsProbabilityMeasure ν]
    (R : (d : ℕ) → Rule (Space d) S) (p δ a ρ H h C r k : ℝ) (t₀ : ℕ)
    (hp : 1 < p) (hδ : δ < 1) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hρ : 0 < ρ) (hH : 0 ≤ H) (hh : 0 ≤ h) (hC : 0 < C) (hk : 0 ≤ k)
    (hr : max (betaExponent p) a < r) (ctrl : UniformControls R ρ a H h t₀) :
    ∃ (d N : ℕ) (μ : ℝ) (hμ : 0 < μ) (hμsmall : μ ≤ 1/128),
      0 < N ∧
      δ < ((iid N (sampleLaw d (rareProbability μ p)
        (rareProbability_le_one hμ hμsmall hp))).prod ν).real
        (successEvent (R d) μ (rareAmplitude μ p) (1/16) N (proposedRate C r k))ᶜ := by
  have hQ : 1 < qExponent p := by
    rw [qExponent_eq p hp]
    have hpos : 0 < 1/(p-1) := one_div_pos.mpr (by linarith)
    linarith
  have hb0 : 0 < betaExponent p := by unfold betaExponent; positivity
  have hb1 : betaExponent p < 1 := by
    unfold betaExponent
    apply (div_lt_one (by linarith)).mpr
    linarith
  have hlo : max (betaExponent p) a < min r 1 :=
    lt_min hr (max_lt hb1 ha1)
  obtain ⟨u, hlu, hur⟩ := exists_between hlo
  have hu : 0 < u := hb0.trans ((le_max_left _ _).trans_lt hlu)
  have hau : a < u := (le_max_right _ _).trans_lt hlu
  have hβu : betaExponent p < u := (le_max_left _ _).trans_lt hlu
  have hu1 : u < 1 := hur.trans_le (min_le_right _ _)
  have hur' : u < r := hur.trans_le (min_le_left _ _)
  let θ := min 1 (u*qExponent p)/2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [min_le_left (1 : ℝ) (u*qExponent p)]
  have hθQ : θ < u*qExponent p := by
    have hpos : 0 < u*qExponent p := mul_pos hu (by linarith)
    dsimp [θ]
    linarith [min_le_right (1 : ℝ) (u*qExponent p)]
  obtain ⟨D, hD, hdom⟩ := logarithmic_envelope_dominated C r u k hC hur' hk
  obtain ⟨q⟩ := MomentumHorizon.select_horizon D p u θ ρ a H h δ t₀
    hD hp hu ha1 hau hθ hθ1 hθQ hρ hH hh hδ hβu
  let w := MomentumLogWindow.window
    (MomentumHorizon.windowScale ρ a (MomentumHorizon.tailPower p u h)) a q.N
  have hNreal : (0 : ℝ) < q.N := by exact_mod_cast q.positive
  let μ := 8*D*(q.N : ℝ)^(-u)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμsmall : μ ≤ 1/128 := q.signal_small
  have hμhalf : μ ≤ 1/2 := by linarith
  have hA := rareAmplitude_pos (p := p) hμ
  have hA1 := rareAmplitude_ge_one hμ hμsmall hp
  have hπ := rareProbability_pos (p := p) hμ
  have hπ1 := rareProbability_le_one hμ hμsmall hp
  have hfinal : envelope D u q.N < μ/4 := by
    rw [envelope_of_pos D u q.N q.positive]
    have hpos : 0 < D*(q.N : ℝ)^(-u) := by positivity
    dsimp [μ]
    linarith
  have hbound : ∀ t hist seed, let z := R q.d t (hist, seed)
      0 ≤ damping z ∧ damping z ≤ 1 ∧ 0 ≤ scale z ∧ scale z ≤ 1 ∧
        0 ≤ gain z ∧ (t < q.N → gain z ≤ H*(q.N+1 : ℝ)^h) := by
    intro t hist seed
    have hc := ctrl.bound q.d t hist seed
    refine ⟨hc.1, hc.2.1.le, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, ?_⟩
    intro ht
    apply hc.2.2.2.2.2.trans
    apply mul_le_mul_of_nonneg_left _ hH
    apply Real.rpow_le_rpow (by positivity) _ hh
    have ht' : t+2 ≤ q.N+1 := by omega
    exact_mod_cast ht'
  have hforget : ∀ j, earlyCutoff θ q.N ≤ j → j < q.N →
      ∀ i ∈ Finset.Ico (j+1) (j+w j+1), ∀ hist seed,
        damping (R q.d i (hist, seed)) ≤ 1-windowGap ρ a j := by
    intro j hj _ i hi hist seed
    have hw := q.short j hj
    change w j ≤ j+1 at hw
    have hib := Finset.mem_Ico.mp hi
    have hti : t₀ ≤ i := by have hh' := q.cutoff_large; omega
    apply (ctrl.forget q.d i hti hist seed).trans
    apply sub_le_sub_left
    apply mul_le_mul_of_nonneg_left _ hρ.le
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    have hi' : i+2 ≤ 3*(j+1) := by omega
    exact_mod_cast hi'
  have hfail := finite_prefix_failure ν (R q.d) (ctrl.measurable q.d)
    μ (rareAmplitude μ p) (1/16) (H*(q.N+1 : ℝ)^h) (rareProbability μ p) δ
    q.N (earlyCutoff θ q.N) q.positive q.cutoff_le hμ.le hμhalf hA.le
    (by norm_num) (by linarith) (by positivity) hπ.le hπ1
    (envelope D u) (windowGap ρ a) w (envelope_antitone D u hD.le hu.le)
    hfinal hbound hforget (fun j hj _ => q.small j hj) q.numeric
  refine ⟨q.d, q.N, μ, hμ, hμsmall, q.positive, hfail.trans_le ?_⟩
  apply measureReal_mono _ (measure_ne_top _ _)
  apply compl_subset_compl.mpr
  intro sample hgood t ht htN
  apply (hgood t ht htN).trans
  rw [envelope_of_pos D u t ht]
  exact hdom t (by exact_mod_cast ht)

open MomentumLegalOracle MomentumInfiniteIID

def prefixFailure (R : Rule (Space d) S) (μ A B C r k : ℝ) (N : ℕ) :
    Set ((ℕ → Sample d) × S) :=
  {q | ∃ t, 0 < t ∧ t ≤ N ∧ proposedRate C r k t <
    populationLoss μ (position R (legalOracle μ A B q.1) q.2 t) - populationLoss μ (target d)}

lemma prefixFailure_eq_preimage (R : Rule (Space d) S) (μ A B C r k : ℝ) (N : ℕ) :
    prefixFailure R μ A B C r k N =
      (fun q : (ℕ → Sample d) × S => (takePrefix N q.1, q.2)) ⁻¹'
        (successEvent R μ A B N (proposedRate C r k))ᶜ := by
  ext q
  simp only [prefixFailure, mem_setOf_eq, mem_preimage, mem_compl_iff, successEvent,
    not_forall, not_le]
  constructor
  · rintro ⟨t, ht, htN, hgap⟩
    refine ⟨t, ht, htN, ?_⟩
    rwa [legal_prefix_position R μ A B q.1 q.2 N t htN]
  · rintro ⟨t, ht, htN, hgap⟩
    refine ⟨t, ht, htN, ?_⟩
    rwa [legal_prefix_position R μ A B q.1 q.2 N t htN] at hgap

/-- The dimension-uniform momentum lower bound: under `UniformControls`, there are a
dimension, a horizon `N`, and an i.i.d. instance on which, with probability greater than
`δ`, the gap at `x_{t+1}` exceeds `C t^(-r) (log(et))^k` for some `1 ≤ t ≤ N`. -/
theorem main_obstruction (ν : Measure S) [IsProbabilityMeasure ν]
    (R : (d : ℕ) → Rule (Space d) S) (p δ a ρ H h C r k : ℝ) (t₀ : ℕ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hδ : δ < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hρ : 0 < ρ) (hH : 0 ≤ H) (hh : 0 ≤ h)
    (hC : 0 < C) (hk : 0 ≤ k) (hr : max (betaExponent p) a < r)
    (ctrl : UniformControls R ρ a H h t₀) :
    ∃ (d N : ℕ) (μ : ℝ) (hμ : 0 < μ) (hμsmall : μ ≤ 1/128),
      0 < N ∧
      LegalInstance d μ (rareAmplitude μ p) (1/16) (rareProbability μ p) p
        (rareProbability_le_one hμ hμsmall hp) ∧
      δ < ((infiniteIID (sampleLaw d (rareProbability μ p)
        (rareProbability_le_one hμ hμsmall hp))).prod ν).real
        (prefixFailure (R d) μ (rareAmplitude μ p) (1/16) C r k N) := by
  obtain ⟨d, N, μ, hμ, hμsmall, hN, hfail⟩ := finite_prefix_rate_failure ν R
    p δ a ρ H h C r k t₀ hp hδ ha0 ha1 hρ hH hh hC hk hr ctrl
  refine ⟨d, N, μ, hμ, hμsmall, hN, fixed_legal_instance d hμ hμsmall hp hp2, ?_⟩
  rw [prefixFailure_eq_preimage]
  rw [(seedPrefix_preserving (sampleLaw d (rareProbability μ p)
    (rareProbability_le_one hμ hμsmall hp)) ν N).measureReal_preimage
    (successEvent_measurable (R d) (ctrl.measurable d) μ (rareAmplitude μ p) (1/16)
      N (proposedRate C r k)).compl.nullMeasurableSet]
  exact hfail

end
end ClippedSGD.MomentumMain
