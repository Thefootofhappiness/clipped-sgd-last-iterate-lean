import ClippedSGD.MomentumRun

/-! The momentum lower bound on a finite prefix, under numerical conditions on the horizon
that are verified in `MomentumHorizon`. -/

open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ClippedSGD.MomentumFiniteLower
open MomentumGeometry MomentumProbability MomentumOracle MomentumRun
noncomputable section

variable {S : Type*} [MeasurableSpace S]

def successEvent (R : Rule (Space d) S) (μ A B : ℝ) (N : ℕ) (b : ℕ → ℝ) :
    Set ((Fin N → Sample d) × S) :=
  {q | ∀ t, 0 < t → t ≤ N →
    populationLoss μ (position R (legalOracle μ A B (prefixSamples q.1)) q.2 t) -
      populationLoss μ (target d) ≤ b t}

lemma successEvent_measurable (R : Rule (Space d) S) (hR : ∀ t, Measurable (R t))
    (μ A B : ℝ) (N : ℕ) (b : ℕ → ℝ) : MeasurableSet (successEvent R μ A B N b) := by
  have hc : Continuous (populationLoss μ : Space d → ℝ) :=
    (show Differentiable ℝ (populationLoss μ : Space d → ℝ) from
      fun x => (sampleLoss_hasGradientAt μ μ 0 x).differentiableAt).continuous
  simp only [successEvent, setOf_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le ((hc.measurable.comp
    (legal_position_measurable R hR μ A B N t)).sub measurable_const) measurable_const

def arrivalWeight (A H : ℝ) (N n₀ : ℕ) (b g : ℕ → ℝ) (w : ℕ → ℕ) (i : Fin N) : ℝ :=
  if n₀ ≤ i.val then
    2 * Real.sqrt (2 * b (i.val + 1)) + A * H * N * Real.exp (-(w i.val : ℝ) * g i.val)
  else 0

lemma arrivalWeight_nonneg (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (N n₀ : ℕ) (b g : ℕ → ℝ) (w : ℕ → ℕ) (i : Fin N) :
    0 ≤ arrivalWeight A H N n₀ b g w i := by
  unfold arrivalWeight
  split_ifs <;> positivity

/-- Under the numerical condition `numeric`, the run leaves the success event with
probability greater than `δ`. -/
theorem finite_prefix_failure (ν : Measure S) [IsProbabilityMeasure ν]
    (R : Rule (Space d) S) (hR : ∀ t, Measurable (R t))
    (μ A B H π δ : ℝ) (N n₀ : ℕ) (hN : 0 < N) (hn₀N : n₀ ≤ N)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1/2) (hA : 0 ≤ A) (hB : 0 < B) (hBA : B ≤ A)
    (hH : 0 ≤ H) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (b g : ℕ → ℝ) (w : ℕ → ℕ) (bmono : Antitone b) (hfinal : b N < μ / 4)
    (bound : ∀ t hist seed, let q := R t (hist, seed)
      0 ≤ damping q ∧ damping q ≤ 1 ∧ 0 ≤ scale q ∧ scale q ≤ 1 ∧
        0 ≤ gain q ∧ (t < N → gain q ≤ H))
    (forget : ∀ j, n₀ ≤ j → j < N → ∀ i ∈ Finset.Ico (j + 1) (j + w j + 1),
      ∀ hist seed, damping (R i (hist, seed)) ≤ 1 - g j)
    (small : ∀ j, n₀ ≤ j → j < N →
      Real.sqrt (2 * b (j + 1)) * Real.sqrt (w j : ℝ) ≤ B / 2)
    (numeric : π * ∑ i : Fin N, arrivalWeight A H N n₀ b g w i <
      (1 - δ - (N : ℝ)^2 / (d + 1 : ℝ) - (n₀ : ℝ)*π) / 2) :
    δ < ((iid N (sampleLaw d π hπ1)).prod ν).real (successEvent R μ A B N b)ᶜ := by
  let ρ := (iid N (sampleLaw d π hπ1)).prod ν
  let G := successEvent R μ A B N b
  let C : Set ((Fin N → Sample d) × S) :=
    {q | ∃ i j : Fin N, i ≠ j ∧ (q.1 i).2.1 = (q.1 j).2.1}
  let E₀ : Set ((Fin N → Sample d) × S) :=
    ⋃ i : Fin n₀, {q | (q.1 ⟨i.val, i.isLt.trans_le hn₀N⟩).1 = true}
  let E := G \ (C ∪ E₀)
  let W := arrivalWeight A H N n₀ b g w
  let Z := fun q : (Fin N → Sample d) × S => ∑ i : Fin N, if (q.1 i).1 = true then W i else 0
  have hG : MeasurableSet G := successEvent_measurable R hR μ A B N b
  have hC : MeasurableSet C :=
    (show MeasurableSet {ω : Fin N → Sample d | ∃ i j : Fin N, i ≠ j ∧ (ω i).2.1 = (ω j).2.1}
      from .of_discrete).preimage measurable_fst
  have hE₀ : MeasurableSet E₀ := by
    apply MeasurableSet.iUnion
    intro i
    exact (show MeasurableSet {ω : Fin N → Sample d |
      (ω ⟨i.val, i.isLt.trans_le hn₀N⟩).1 = true} from .of_discrete).preimage measurable_fst
  have hE : MeasurableSet E := hG.diff (hC.union hE₀)
  have hCprob : ρ.real C ≤ (N : ℝ)^2/(d+1 : ℝ) := by
    have hm := seed_event_mass (N := N) ν d π hπ1
      {ω | ∃ i j : Fin N, i ≠ j ∧ (ω i).2.1 = (ω j).2.1}
    exact hm.trans_le (collision_probability_le d π hπ1)
  have hE₀prob : ρ.real E₀ ≤ (n₀ : ℝ)*π := by
    calc
      _ ≤ ∑ i : Fin n₀, ρ.real {q | (q.1 ⟨i.val, i.isLt.trans_le hn₀N⟩).1 = true} :=
        measureReal_iUnion_fintype_le _
      _ = (n₀ : ℝ)*π := by
        have hm (i : Fin n₀) : ρ.real {q | (q.1 ⟨i.val, i.isLt.trans_le hn₀N⟩).1 = true} = π := by
          exact (seed_event_mass ν d π hπ1 _).trans
            (iid_rare_mass d hπ0 hπ1 ⟨i.val, i.isLt.trans_le hn₀N⟩)
        simp_rw [hm]
        simp
  have hiZ : Integrable Z ρ := weighted_rare_integrable ν d π hπ1 W
  have hZ0 : ∀ q, 0 ≤ Z q := by
    intro q
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact arrivalWeight_nonneg A H hA hH N n₀ b g w i
    · exact le_rfl
  have hprogress : ∀ q ∈ E, 1/2 ≤ Z q := by
    intro q hq
    have hgood := hq.1
    have hdistinct : ∀ i < N, ∀ j < N, i ≠ j →
        (prefixSamples q.1 i).2.1 ≠ (prefixSamples q.1 j).2.1 := by
      intro i hi j hj hij he
      apply hq.2
      left
      exact ⟨⟨i,hi⟩, ⟨j,hj⟩, (by intro h; exact hij (congrArg Fin.val h)),
        by simpa only [prefixSamples_at q.1 i hi, prefixSamples_at q.1 j hj] using he⟩
    have hearly : ∀ i < n₀, (prefixSamples q.1 i).1 = false := by
      intro i hi
      have hiN := hi.trans_le hn₀N
      rw [prefixSamples_at q.1 i hiN]
      cases hbit : (q.1 ⟨i,hiN⟩).1
      · rfl
      · exfalso
        apply hq.2
        right
        exact mem_iUnion.mpr ⟨⟨i,hi⟩, hbit⟩
    have hp := pathwise_progress R μ A B H (prefixSamples q.1) q.2 N n₀ hN
      hμ0 hμhalf hA hB hBA hH b g w bmono hfinal
      (fun t => bound t _ q.2)
      (fun j hj hjN i hi => forget j hj hjN i hi _ q.2) small hgood hdistinct hearly
    have heq : (∑ j ∈ Finset.range N, if (prefixSamples q.1 j).1 then
        2 * Real.sqrt (2*b (j+1)) + A*H*N*Real.exp (-(w j : ℝ)*g j) else 0) = Z q := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rw [prefixSamples_at q.1 i.val i.isLt]
      dsimp [Z, W, arrivalWeight]
      by_cases hi : n₀ ≤ i.val
      · simp [hi]
      · have hn := hearly i.val (by omega)
        rw [prefixSamples_at q.1 i.val i.isLt] at hn
        simp [hi, hn]
    rw [heq] at hp
    exact hp.le
  have hbudget := event_progress_budget ρ E hE Z hiZ hZ0 (1/2) hprogress
  rw [weighted_rare_seed_expectation ν d hπ0 hπ1 W] at hbudget
  by_contra hn
  have hfail : ρ.real Gᶜ ≤ δ := le_of_not_gt hn
  rw [measureReal_compl hG, measureReal_univ_eq_one] at hfail
  have hinter := le_measureReal_diff (μ := ρ) (s₁ := G) (s₂ := C ∪ E₀)
  have hunion := measureReal_union_le (μ := ρ) C E₀
  change ρ.real G - ρ.real (C ∪ E₀) ≤ ρ.real E at hinter
  dsimp [W] at hbudget
  nlinarith

end
end ClippedSGD.MomentumFiniteLower
