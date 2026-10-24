import ClippedSGD.AnytimeLowerRule

/-! The reference trajectory: the run on the endpoint instance, stopped after it first
exceeds one half. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ClippedSGD.AnytimeLower

/-- Stops a path after the first time it exceeds the boundary. -/
def freezePath (X : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => X 0
  | n+1 => if c < freezePath X c n then freezePath X c n else X (n+1)

lemma freezePath_spec (X : ℕ → ℝ) (c : ℝ) (hmono : Monotone X) (n : ℕ) :
    freezePath X c n ≤ X n ∧ (freezePath X c n ≤ c → freezePath X c n=X n) := by
  induction n with
  | zero => exact ⟨le_rfl,fun _ => rfl⟩
  | succ n ih =>
    by_cases hc : c < freezePath X c n
    · simp only [freezePath,if_pos hc]
      exact ⟨ih.1.trans (hmono (by omega)),fun h => (not_lt_of_ge h hc).elim⟩
    · simp [freezePath,hc]

lemma freezePath_no_move (X : ℕ → ℝ) (c : ℝ) (hmono : Monotone X)
    (n : ℕ) (hn : X (n+1)=X n) : freezePath X c (n+1)=freezePath X c n := by
  by_cases hc : c < freezePath X c n
  · simp [freezePath,hc]
  · rw [freezePath,if_neg hc,hn,(freezePath_spec X c hmono n).2 (le_of_not_gt hc)]

lemma freezePath_crossing (X : ℕ → ℝ) (c z : ℝ) (hmono : Monotone X)
    (n : ℕ) (hz : z<c) (hn : freezePath X c n≤z) :
    freezePath X c n=X n ∧ freezePath X c (n+1)=X (n+1) := by
  have hnc : freezePath X c n≤c := hn.trans hz.le
  exact ⟨(freezePath_spec X c hmono n).2 hnc,by rw [freezePath,if_neg (not_lt_of_ge hnc)]⟩

lemma freezePath_le_boundary_iff (X : ℕ → ℝ) (c : ℝ) (hmono : Monotone X) (n : ℕ) :
    freezePath X c n≤c ↔ X n≤c := by
  constructor
  · intro h; rwa [(freezePath_spec X c hmono n).2 h] at h
  · intro h; exact (freezePath_spec X c hmono n).1.trans h

lemma freezePath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀n,Measurable (X n)) (c : ℝ) (n : ℕ) :
    Measurable (fun ω => freezePath (fun t => X t ω) c n) := by
  induction n with
  | zero => exact hX 0
  | succ n ih =>
    exact Measurable.ite (measurableSet_lt measurable_const ih) ih (hX (n+1))

/-- The run on the endpoint instance (minimizer `1`), stopped after it first exceeds one
half. -/
def frozenReference {S : Type*} (R : Rule S) (μ A : ℝ)
    (bits : ℕ → Bool) (seed : S) : ℕ → ℝ :=
  freezePath (position R (actualOracle μ 1 A bits) seed) (1/2)

/-- The stopped run on the endpoint instance equals the stopped run on flat gradients. -/
theorem frozenReference_eq_flat {S : Type*} (R : Rule S) (hR : Nonnegative R)
    (μ A : ℝ) (hμ : μ≤1/2) (hA : 0≤A) (bits : ℕ → Bool) (seed : S) :
    frozenReference R μ A bits seed=freezePath (position R (referenceOracle A bits) seed) (1/2) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    change freezePath (position R (actualOracle μ 1 A bits) seed) (1/2) (n+1)=_
    change freezePath (position R (actualOracle μ 1 A bits) seed) (1/2) n=_ at ih
    simp only [freezePath,ih]
    by_cases hc : 1/2<freezePath (position R (referenceOracle A bits) seed) (1/2) n
    · rw [if_pos hc,if_pos hc]
    · simp only [if_neg hc]
      have hm := reference_monotone hR hA bits seed
      have hn := (freezePath_spec _ (1/2) hm n).2 (le_of_not_gt hc)
      have hb : position R (referenceOracle A bits) seed n≤1/2 := by
        rw [←hn]; exact le_of_not_gt hc
      exact flat_coupling R μ 1 A bits seed (n+1) (by
        intro j hj
        have hh := (hm (show j≤n by omega)).trans hb
        linarith) (n+1) le_rfl

lemma frozenReference_measurable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (R : Rule S) (hR : ∀t,Measurable (R t)) (μ A : ℝ)
    (bits : Ω → ℕ → Bool) (hbits : Measurable bits)
    (seed : Ω → S) (hs : Measurable seed) (t : ℕ) :
    Measurable (fun ω => frozenReference R μ A (bits ω) (seed ω) t) :=
  freezePath_measurable _ (fun n => position_measurable R hR _
    (actualOracle_measurable μ 1 A bits hbits) seed hs n) _ t

end ClippedSGD.AnytimeLower
