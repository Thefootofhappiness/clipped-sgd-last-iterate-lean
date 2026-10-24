import ClippedSGD.ArrivalExpectation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The crossing budget: a path that moves only at rare arrivals and must pass every
boundary in `[0, c)` without a bad crossing needs a large expected total jump length. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace ClippedSGD.AnytimeLower

lemma continuous_crossing_exists (X : ℕ → ℝ) {N : ℕ} {z : ℝ}
    (hzero : X 0≤z) (hN : z<X N) : ∃t<N, X t≤z ∧ z<X (t+1) := by
  induction N with
  | zero => exact (not_lt_of_ge hzero hN).elim
  | succ N ih =>
    by_cases h : z<X N
    · obtain ⟨t,ht,hb,ha⟩ := ih h
      exact ⟨t,by omega,hb,ha⟩
    · exact ⟨N,by omega,le_of_not_gt h,hN⟩

def badCrossing {Ω : Type*} (X : ℕ → Ω → ℝ) (s : ℕ → ℝ) (N : ℕ) (z : ℝ) : Set Ω :=
  {ω | ∃t<N, X t ω≤z ∧ z+s t<X (t+1) ω}

def crossingJoint {Ω : Type*} (X : ℕ → Ω → ℝ) (s : ℕ → ℝ) (N : ℕ) : Set (ℝ × Ω) :=
  {q | ∃t<N, X t q.2≤q.1 ∧ q.1+s t<X (t+1) q.2}

lemma badCrossing_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀t,Measurable (X t)) (s : ℕ → ℝ) (N : ℕ) (z : ℝ) :
    MeasurableSet (badCrossing X s N z) := by
  simp only [badCrossing,setOf_exists]
  apply MeasurableSet.iUnion
  intro t
  by_cases ht : t<N
  · simp only [ht,true_and]
    exact (measurableSet_le (hX t) measurable_const).inter
      (measurableSet_lt measurable_const (hX (t+1)))
  · simp [ht]

lemma crossingJoint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀t,Measurable (X t)) (s : ℕ → ℝ) (N : ℕ) :
    MeasurableSet (crossingJoint X s N) := by
  simp only [crossingJoint,setOf_exists]
  apply MeasurableSet.iUnion
  intro t
  by_cases ht : t<N
  · simp only [ht,true_and]
    exact (measurableSet_le ((hX t).comp measurable_snd) measurable_fst).inter
      (measurableSet_lt (measurable_fst.add_const _) ((hX (t+1)).comp measurable_snd))
  · simp [ht]

/-- For a boundary `z ∈ [0, c)`, a path ends at most `c`, crosses `z` badly, or has an
arrival whose interval `[X (t+1) - s t, X (t+1))` contains `z`. -/
lemma crossing_indicator_bound {Ω : Type*} (X : ℕ → Ω → ℝ)
    (arrival : Ω → ℕ → Bool) (s : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hzero : ∀ω, X 0 ω=0)
    (hstill : ∀ω t, t<N → arrival ω t=false → X (t+1) ω=X t ω)
    (ω : Ω) (z : ℝ) (hz : z∈Ico 0 c) :
    (1:ℝ) ≤ {ω | X N ω≤c}.indicator (fun _ => (1:ℝ)) ω+
      (badCrossing X s N z).indicator (fun _ => (1:ℝ)) ω+
      ∑t∈Finset.range N, if arrival ω t then
        (Ico (X (t+1) ω-s t) (X (t+1) ω)).indicator (fun _ => (1:ℝ)) z else 0 := by
  classical
  have hn : ∀t, 0 ≤ (if arrival ω t then
      (Ico (X (t+1) ω-s t) (X (t+1) ω)).indicator (fun _ => (1:ℝ)) z else 0) := by
    intro t
    split_ifs
    · exact Set.indicator_nonneg (fun _ _ => by norm_num) _
    · rfl
  have hb0 : 0 ≤ (badCrossing X s N z).indicator (fun _ => (1:ℝ)) ω :=
    Set.indicator_nonneg (fun _ _ => by norm_num) _
  have hs0 := Finset.sum_nonneg (s := Finset.range N) (fun t _ => hn t)
  by_cases he : X N ω≤c
  · rw [Set.indicator_of_mem (show ω∈{ω | X N ω≤c} from he)]
    linarith
  · rw [Set.indicator_of_not_mem (show ω∉{ω | X N ω≤c} from he),zero_add]
    by_cases hb : ω∈badCrossing X s N z
    · rw [Set.indicator_of_mem hb]
      linarith
    · rw [Set.indicator_of_not_mem hb,zero_add]
      obtain ⟨t,ht,hbefore,hafter⟩ := continuous_crossing_exists (fun t => X t ω)
        (by change X 0 ω≤z; rw [hzero]; exact hz.1) (hz.2.trans (lt_of_not_ge he))
      have ha : arrival ω t=true := by
        cases heq : arrival ω t
        · have hh := hstill ω t ht heq
          linarith
        · rfl
      have hsafe : z∈Ico (X (t+1) ω-s t) (X (t+1) ω) := by
        refine ⟨?_,hafter⟩
        apply le_of_not_gt
        intro hlarge
        exact hb ⟨t,ht,hbefore,by linarith only [hlarge]⟩
      have hs := Finset.single_le_sum (fun t _ => hn t) (Finset.mem_range.mpr ht)
      simpa only [ha,Bool.true_eq,if_true,Set.indicator_of_mem hsafe] using hs


/-- If the path ends at most `c`, and crosses each boundary in `[0, c)` badly, with
probability at most `δ`, then `c (1 - 2δ) ≤ π ∑_{t<N} s t`. The proof integrates
`crossing_indicator_bound` over the boundary. -/
theorem continuous_crossing_budget {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (hX : ∀t,Measurable (X t))
    (arrival : Ω → ℕ → Bool) (ha : Measurable arrival)
    (s : ℕ → ℝ) (c δ π : ℝ) (hc : 0<c) (N : ℕ)
    (hs : ∀t<N, 0≤s t) (hzero : ∀ω, X 0 ω=0)
    (hstill : ∀ω t, t<N → arrival ω t=false → X (t+1) ω=X t ω)
    (hmass : ∀t<N, ν.real {ω | arrival ω t=true}=π)
    (hend : ν.real {ω | X N ω≤c}≤δ)
    (hbad : ∀z∈Ico 0 c, ν.real (badCrossing X s N z)≤δ) :
    c*(1-2*δ) ≤ π*(∑t∈Finset.range N,s t) := by
  classical
  let νz : Measure ℝ := volume.restrict (Ico 0 c)
  letI : IsFiniteMeasure νz := ⟨by simp only [νz,Measure.restrict_apply_univ,Real.volume_Ico]; finiteness⟩
  have hνz : νz.real univ=c := by
    simp only [νz,measureReal_restrict_apply_univ,Real.volume_real_Ico,sub_zero,max_eq_left hc.le]
  let F : ℝ × Ω → ℝ := (crossingJoint X s N).indicator (fun _ => 1)
  have hF : Integrable F (νz.prod ν) :=
    (integrable_const 1).indicator (crossingJoint_measurable X hX s N)
  have hFz (z : ℝ) : (fun ω => F (z,ω))=(badCrossing X s N z).indicator (fun _ => (1:ℝ)) := rfl
  have hFω (ω : Ω) : Measurable (fun z => F (z,ω)) :=
    (((measurable_const.indicator (crossingJoint_measurable X hX s N)).comp
      (measurable_id.prodMk measurable_const)))
  have hiFω (ω : Ω) : Integrable (fun z => F (z,ω)) νz := by
    apply Integrable.mono' (integrable_const (1:ℝ)) (hFω ω).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      dsimp [F]
      by_cases h : (z,ω)∈crossingJoint X s N <;> simp [Set.indicator_apply,h])
  let area : Ω → ℝ := fun ω => ∫z, F (z,ω) ∂νz
  have hiarea : Integrable area ν := hF.integral_prod_right
  have harea : (∫ω,area ω ∂ν)≤c*δ := by
    have hswap := integral_prod_symm F hF
    change (∫q,F q ∂νz.prod ν)=(∫ω,area ω ∂ν) at hswap
    rw [←hswap,integral_prod F hF]
    have hmono := integral_mono_ae hF.integral_prod_left (integrable_const δ) (by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
      rw [hFz,integral_indicator_const _ (badCrossing_measurable X hX s N z),smul_eq_mul,mul_one]
      exact hbad z hz)
    simpa only [integral_const,smul_eq_mul,hνz] using hmono
  let E : Set Ω := {ω | X N ω≤c}
  have hE : MeasurableSet E := measurableSet_le (hX N) measurable_const
  have hiE : Integrable (E.indicator (fun _ => (1:ℝ))) ν := (integrable_const 1).indicator hE
  have hiA := arrivals_integrable ν arrival ha s N
  have hpath (ω : Ω) : c ≤ c*E.indicator (fun _ => (1:ℝ)) ω+area ω+
      ∑t∈Finset.range N,if arrival ω t then s t else 0 := by
    let safe (t : ℕ) : ℝ → ℝ := fun z => if arrival ω t then
      (Ico (X (t+1) ω-s t) (X (t+1) ω)).indicator (fun _ => (1:ℝ)) z else 0
    have hisafe (t : ℕ) : Integrable (safe t) νz := by
      dsimp only [safe]
      split_ifs
      · exact (integrable_const 1).indicator measurableSet_Ico
      · exact integrable_zero _ _ _
    have hsafeb (t : ℕ) (ht : t<N) : (∫z,safe t z ∂νz) ≤ (if arrival ω t then s t else 0) := by
      dsimp only [safe]
      split_ifs
      · rw [integral_indicator_const _ measurableSet_Ico,smul_eq_mul,mul_one]
        change (volume.restrict (Ico 0 c)).real (Ico (X (t+1) ω-s t) (X (t+1) ω))≤s t
        rw [measureReal_restrict_apply measurableSet_Ico]
        have hle := measureReal_mono (μ := volume) (inter_subset_left :
          Ico (X (t+1) ω-s t) (X (t+1) ω)∩Ico 0 c ⊆ Ico (X (t+1) ω-s t) (X (t+1) ω))
          (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
        apply hle.trans
        rw [Real.volume_real_Ico]
        simp only [sub_sub_cancel]
        exact max_le (le_refl _) (hs t ht)
      · simp
    have hip := integral_mono_ae (integrable_const (1:ℝ))
      (((integrable_const (E.indicator (fun _ => (1:ℝ)) ω)).add (hiFω ω)).add
        (integrable_finset_sum _ (fun t _ => hisafe t))) (by
          filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
          exact crossing_indicator_bound X arrival s c N hzero hstill ω z hz)
    have hsplit1 := integral_add
      ((integrable_const (E.indicator (fun _ => (1:ℝ)) ω) (μ:=νz)).add (hiFω ω))
      (integrable_finset_sum (Finset.range N) (fun t _ => hisafe t))
    have hsplit2 := integral_add (integrable_const (E.indicator (fun _ => (1:ℝ)) ω) (μ:=νz)) (hiFω ω)
    dsimp only [Pi.add_apply] at hip hsplit1 hsplit2
    rw [hsplit1,hsplit2,integral_finset_sum _ (fun t _ => hisafe t)] at hip
    simp only [integral_const,smul_eq_mul,hνz,mul_one] at hip
    have hsums := Finset.sum_le_sum (s := Finset.range N)
      (fun t ht => hsafeb t (Finset.mem_range.mp ht))
    exact hip.trans (add_le_add_left hsums _)
  have hint := integral_mono (integrable_const c) (((hiE.const_mul c).add hiarea).add hiA) hpath
  have hsplit1 := integral_add ((hiE.const_mul c).add hiarea) hiA
  have hsplit2 := integral_add (hiE.const_mul c) hiarea
  dsimp only [Pi.add_apply] at hint hsplit1 hsplit2
  rw [hsplit1,hsplit2,integral_const_mul,
    integral_indicator_const _ hE,smul_eq_mul,mul_one,
    arrivals_expectation ν arrival ha s N hmass] at hint
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hint
  have he := mul_le_mul_of_nonneg_left hend hc.le
  change c*ν.real E≤c*δ at he
  nlinarith only [hint,he,harea]

end ClippedSGD.AnytimeLower
