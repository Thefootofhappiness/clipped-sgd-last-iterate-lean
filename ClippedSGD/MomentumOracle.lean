import ClippedSGD.MomentumGeometry
import ClippedSGD.MomentumProbability
import Mathlib.Analysis.MeanInequalitiesPow

/-! The additive noise of the momentum instance and its moment bound. -/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal

namespace ClippedSGD.MomentumOracle
open MomentumGeometry MomentumProbability
noncomputable section

def amplitude (A B : ℝ) (b : Bool) : ℝ := if b then A else B

def pulse (A B : ℝ) (a : Sample d) : Nuisance d :=
  EuclideanSpace.single a.2.1 (if a.2.2 then amplitude A B a.1 else -amplitude A B a.1)

def noise (μ A B : ℝ) (a : Sample d) : Space d :=
  EuclideanSpace.single 0 (μ - (if a.1 then A else 0)) + liftNuisance (pulse A B a)

def loss (μ A B : ℝ) (a : Sample d) : Space d → ℝ :=
  sampleLoss μ (if a.1 then A else 0) (pulse A B a)

def grad (μ A B : ℝ) (a : Sample d) : Space d → Space d :=
  sampleGrad μ (if a.1 then A else 0) (pulse A B a)

lemma additive_noise (μ A B : ℝ) (a : Sample d) (x : Space d) :
    grad μ A B a x - populationGrad μ x = noise μ A B a :=
  sampleGrad_sub_population μ (if a.1 then A else 0) (pulse A B a) x

lemma pulse_norm (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (a : Sample d) :
    ‖pulse A B a‖ = amplitude A B a.1 := by
  have hr : 0 ≤ amplitude A B a.1 := by cases a.1 <;> simp [amplitude, hA, hB]
  simp only [pulse, EuclideanSpace.norm_single, Real.norm_eq_abs]
  split_ifs <;> simp [abs_of_nonneg hr]

lemma pulse_orthogonal (A B : ℝ) (a b : Sample d) (hab : a.2.1 ≠ b.2.1) :
    ⟪pulse A B a, pulse A B b⟫_ℝ = 0 := by
  simp [pulse, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hab, Ne.symm hab]

lemma noise_norm_rpow_le (μ A B p : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp0 : 0 ≤ p) (hp2 : p ≤ 2) (a : Sample d) :
    ‖noise μ A B a‖ ^ p ≤ |μ - (if a.1 then A else 0)| ^ p + (amplitude A B a.1) ^ p := by
  have hn : ‖noise μ A B a‖ ^ 2 =
      |μ - (if a.1 then A else 0)| ^ 2 + (amplitude A B a.1) ^ 2 := by
    rw [noise, noise_norm_sq, pulse_norm A B hA hB]
    rw [sq_abs]
  have hr : 0 ≤ amplitude A B a.1 := by cases a.1 <;> simp [amplitude, hA, hB]
  calc
    _ = (‖noise μ A B a‖ ^ 2) ^ (p / 2) := by
      rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
      congr 1
      norm_num
      ring
    _ = (|μ - (if a.1 then A else 0)| ^ 2 + (amplitude A B a.1) ^ 2) ^ (p / 2) := by rw [hn]
    _ ≤ (|μ - (if a.1 then A else 0)| ^ 2) ^ (p / 2) +
        ((amplitude A B a.1) ^ 2) ^ (p / 2) :=
      Real.rpow_add_le_add_rpow (sq_nonneg _) (sq_nonneg _) (by linarith) (by linarith)
    _ = _ := by
      rw [← Real.rpow_natCast_mul (abs_nonneg _) 2, ← Real.rpow_natCast_mul hr 2]
      congr 2 <;> ring

lemma integral_bernoulli_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Bool → E) :
    (∫ b, f b ∂ClippedSGD.Lower.bernoulliLaw q hq1) =
      (1 - q) • f false + q • f true := by
  unfold ClippedSGD.Lower.bernoulliLaw
  rw [PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply, ENNReal.toReal_sub_of_le
    (ENNReal.ofReal_le_one.mpr hq1) ENNReal.one_ne_top, ENNReal.toReal_ofReal hq0, add_comm]

lemma sign_mean (μ A B : ℝ) (b : Bool) (j : Fin (d + 1)) :
    (∫ s, noise μ A B (b, (j, s))
      ∂ClippedSGD.Lower.bernoulliLaw (1 / 2) (by norm_num)) =
      EuclideanSpace.single 0 (μ - (if b then A else 0)) := by
  rw [integral_bernoulli_vector (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [noise, liftNuisance, coordinateVector, EuclideanSpace.single_apply]
    ring
  · simp [noise, pulse, liftNuisance, coordinateVector, EuclideanSpace.single_apply]
    split_ifs <;> ring

/-- The noise has mean zero under the sample law. -/
theorem mean_zero (μ A B π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hm : π * A = μ) :
    (∫ a : Sample d, noise μ A B a ∂sampleLaw d π hπ1) = 0 := by
  unfold sampleLaw
  rw [integral_prod _ (Integrable.of_finite)]
  have hinner (b : Bool) :
      (∫ a : Fin (d + 1) × Bool, noise μ A B (b, a)
        ∂(coordinateLaw d).prod (ClippedSGD.Lower.bernoulliLaw (1 / 2) (by norm_num))) =
      EuclideanSpace.single 0 (μ - (if b then A else 0)) := by
    rw [integral_prod _ (Integrable.of_finite)]
    simp_rw [sign_mean]
    simp
  simp_rw [hinner]
  rw [integral_bernoulli_vector hπ0 hπ1]
  apply PiLp.ext
  intro i
  simp [EuclideanSpace.single_apply]
  split_ifs <;> simp_all
  nlinarith

lemma integrate_rare_function (d : ℕ) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (f : Bool → ℝ) :
    (∫ a : Sample d, f a.1 ∂sampleLaw d π hπ1) = (1 - π) * f false + π * f true := by
  unfold sampleLaw
  rw [integral_prod _ (Integrable.of_finite)]
  simp only [integral_const, measureReal_univ_eq_one, one_smul]
  exact ClippedSGD.Lower.integral_bernoulliLaw hπ0 hπ1 f

lemma moment_bound (μ A B π p κ : ℝ) (hμ0 : 0 ≤ μ) (hA : 0 ≤ A) (hμA : μ ≤ A)
    (hB0 : 0 ≤ B) (hπ0 : 0 < π) (hπ1 : π ≤ 1) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hm : π * A = μ) (hκ : π * A ^ p = κ) :
    (∫ a : Sample d, ‖noise μ A B a‖ ^ p ∂sampleLaw d π hπ1) ≤ 3 * κ + B ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hπp : π ^ p ≤ π := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1 hp1
  have hμp : μ ^ p ≤ κ := by
    rw [← hm, Real.mul_rpow hπ0.le hA]
    exact (mul_le_mul_of_nonneg_right hπp (Real.rpow_nonneg hA p)).trans_eq hκ
  have hdiff : |μ - A| ^ p ≤ A ^ p := by
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp0
    rw [abs_of_nonpos (sub_nonpos.mpr hμA)]
    linarith
  have hκ0 : 0 ≤ κ := by rw [← hκ]; positivity
  calc
    _ ≤ ∫ a : Sample d, |μ - (if a.1 then A else 0)| ^ p + (amplitude A B a.1) ^ p
        ∂sampleLaw d π hπ1 :=
      integral_mono (Integrable.of_finite) (Integrable.of_finite)
        (noise_norm_rpow_le μ A B p hA hB0 hp0 hp2)
    _ = (1 - π) * (μ ^ p + B ^ p) + π * (|μ-A| ^ p + A ^ p) := by
      simpa [amplitude, abs_of_nonneg hμ0] using
        integrate_rare_function d π hπ0.le hπ1
          (fun b => |μ - (if b then A else 0)| ^ p + (amplitude A B b) ^ p)
    _ ≤ (μ ^ p + B ^ p) + π * (A ^ p + A ^ p) := by
      apply add_le_add
      · exact mul_le_of_le_one_left (by positivity) (by linarith)
      · exact mul_le_mul_of_nonneg_left (add_le_add_right hdiff _) hπ0.le
    _ ≤ 3 * κ + B ^ p := by nlinarith [hκ]

def rareAmplitude (μ p : ℝ) : ℝ := ((1 / 128 : ℝ) / μ) ^ (1 / (p - 1))
def rareProbability (μ p : ℝ) : ℝ := μ / rareAmplitude μ p

lemma rareAmplitude_pos {μ p : ℝ} (hμ : 0 < μ) : 0 < rareAmplitude μ p := by
  exact Real.rpow_pos_of_pos (by positivity) _

lemma rareAmplitude_ge_one {μ p : ℝ} (hμ : 0 < μ) (hμsmall : μ ≤ 1 / 128)
    (hp : 1 < p) : 1 ≤ rareAmplitude μ p := by
  apply Real.one_le_rpow
  · exact (le_div_iff₀ hμ).mpr (by linarith)
  · exact one_div_nonneg.mpr (by linarith)

lemma rareProbability_pos {μ p : ℝ} (hμ : 0 < μ) : 0 < rareProbability μ p := by
  exact div_pos hμ (rareAmplitude_pos hμ)

lemma rareProbability_le_one {μ p : ℝ} (hμ : 0 < μ) (hμsmall : μ ≤ 1 / 128)
    (hp : 1 < p) : rareProbability μ p ≤ 1 := by
  apply (div_le_one (rareAmplitude_pos hμ)).mpr
  have := rareAmplitude_ge_one hμ hμsmall hp
  linarith

lemma rare_centering {μ p : ℝ} (hμ : 0 < μ) :
    rareProbability μ p * rareAmplitude μ p = μ := by
  exact div_mul_cancel₀ μ (ne_of_gt (rareAmplitude_pos hμ))

lemma rare_moment_identity {μ p : ℝ} (hμ : 0 < μ) (hp : 1 < p) :
    rareProbability μ p * (rareAmplitude μ p) ^ p = 1 / 128 := by
  have hp0 : p - 1 ≠ 0 := by linarith
  have hbase : 0 < (1 / 128 : ℝ) / μ := by positivity
  have hpow : (rareAmplitude μ p) ^ (p - 1) = (1 / 128 : ℝ) / μ := by
    unfold rareAmplitude
    rw [← Real.rpow_mul hbase.le]
    simp [hp0]
  have hA : 0 < rareAmplitude μ p := rareAmplitude_pos hμ
  have hpowp : (rareAmplitude μ p) ^ p = (rareAmplitude μ p) ^ (p - 1) * rareAmplitude μ p := by
    calc
      _ = (rareAmplitude μ p) ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := Real.rpow_add_one hA.ne' _
  rw [hpowp, hpow, rareProbability]
  field_simp
  ring

/-- For `μ ≤ 1/128`, the noise has mean zero and `p`th norm moment at most one. -/
theorem fixed_oracle_moments (d : ℕ) {μ p : ℝ}
    (hμ : 0 < μ) (hμsmall : μ ≤ 1 / 128) (hp : 1 < p) (hp2 : p ≤ 2) :
    let A := rareAmplitude μ p
    let π := rareProbability μ p
    let hπ := rareProbability_le_one hμ hμsmall hp
    (∫ a : Sample d, noise μ A (1 / 16) a ∂sampleLaw d π hπ) = 0 ∧
    (∫ a : Sample d, ‖noise μ A (1 / 16) a‖ ^ p ∂sampleLaw d π hπ) ≤ 1 := by
  dsimp
  have hA : 0 ≤ rareAmplitude μ p := (rareAmplitude_pos hμ).le
  have hμA : μ ≤ rareAmplitude μ p := by
    have := rareAmplitude_ge_one hμ hμsmall hp
    linarith
  constructor
  · exact mean_zero μ _ _ _ (rareProbability_pos hμ).le _ (rare_centering hμ)
  · have hb : (1 / 16 : ℝ) ^ p ≤ (1 / 16 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 / 16 : ℝ) ≤ 1) hp.le
    have hm := moment_bound (d := d) μ (rareAmplitude μ p) (1 / 16)
      (rareProbability μ p) p (1 / 128) hμ.le hA hμA (by norm_num)
      (rareProbability_pos hμ) (rareProbability_le_one hμ hμsmall hp)
      hp.le hp2 (rare_centering hμ) (rare_moment_identity hμ hp)
    linarith

end
end ClippedSGD.MomentumOracle
