import BerryEsseen.EffectiveClusterJitter
import BerryEsseen.BinomialExpansion

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem effective_binomial_parameters (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    p ∈ Ioo 0 1 ∧ (0.48 : ℝ) ≤ Real.sqrt (p * (1 - p)) ∧
      Real.sqrt (p * (1 - p)) ≤ 1 / 2 ∧ p ^ 2 + (1 - p) ^ 2 ∈ Icc (1 / 2) 0.52 := by
  have hv : (0.24 : ℝ) ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hvu : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hs := Real.sq_sqrt (by linarith : 0 ≤ p * (1 - p))
  have hs0 := Real.sqrt_nonneg (p * (1 - p))
  refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · constructor <;> nlinarith

/-- The appendix atom bound, now proved by Fourier inversion; the legacy
published-bound parameter is retained only for API compatibility. -/
theorem effective_binomial_mass_upper (_B : PublishedBernoulliBound) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n k : ℕ) (hn : 1 ≤ n) :
    binomialWeight p n k ≤ 2 / Real.sqrt (n : ℝ) := by
  exact manuscript_effective_binomial_mass_upper p hp n k hn

theorem effective_binomial_jitter (S : PublishedSignedSmoothing) (p T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hT : 10 ≤ T)
    (n : ℕ) (hn : 1000000 ≤ n) (x : ℝ) :
    Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter 1) x -
      edgeworthCDF n (signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1))
        ((x - (n : ℝ) * p) / (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))| ≤
      effectiveClusterError n 0 T := by
  have h0 : ∀ᵐ x ∂CenteredFourthLaw.zero.measure, |x| ≤ (0 : ℝ) := by simp [CenteredFourthLaw.zero]
  have h := effective_cluster_jitter_pointwise S CenteredFourthLaw.zero CenteredFourthLaw.zero p 0 T
    hp (effective_binomial_parameters p hp).1 (by norm_num) hT (by positivity) h0 h0 n hn x
  simpa only [twoCluster_zero_noise, zero_clusterVariance, standardizedBernoulliLaw, binomialMeasure] using h

theorem effective_binomial_shift_constant (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    edgeworthShiftConstant (Real.sqrt (p * (1 - p)))⁻¹ ≤ 4 := by
  have hs := (effective_binomial_parameters p hp).2.1
  have hs0 : 0 < Real.sqrt (p * (1 - p)) := by linarith
  have hh0 : 0 ≤ (Real.sqrt (p * (1 - p)))⁻¹ := inv_nonneg.mpr hs0.le
  have hh : (Real.sqrt (p * (1 - p)))⁻¹ ≤ 5 / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hs0]
    linarith
  unfold edgeworthShiftConstant
  rw [abs_of_nonneg hh0]
  have hpoly : 0 ≤ 3 * (Real.sqrt (p * (1 - p)))⁻¹ ^ 2 / 8 + 3 * (Real.sqrt (p * (1 - p)))⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le hpoly
  nlinarith [sq_nonneg ((5 / 2 : ℝ) - (Real.sqrt (p * (1 - p)))⁻¹), mul_nonneg hh0 (sub_nonneg.mpr hh)]

theorem effective_binomial_endpoint_expansion (S : PublishedSignedSmoothing) (p T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hT : 10 ≤ T)
    (n : ℕ) (hn : 1000000 ≤ n) (k : ℤ) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let h := (Real.sqrt (p * (1 - p)))⁻¹
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope h κ (binomialZ p n k)| ≤ effectiveClusterError n 0 T + 4 / Real.sqrt (n : ℝ)) ∧
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope (-h) κ (binomialZ p n k)| ≤ effectiveClusterError n 0 T + 4 / Real.sqrt (n : ℝ)) := by
  have hb := effective_binomial_parameters p hp
  have hpcc : p ∈ Icc 0 1 := ⟨hb.1.1.le, hb.1.2.le⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr := Real.sqrt_pos.mpr hn0
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith [hb.2.1]
  have hκ := (signedThirdMoment_abs_le (standardizedBernoulliLaw p hb.1)).trans
    (standardizedBernoulli_third_le_two p hb.1 ⟨hp.1, by linarith [hp.2]⟩)
  have hu := effective_binomial_jitter S p T hp hT n hn ((k : ℝ) + 1 / 2)
  have hl := effective_binomial_jitter S p T hp hT n hn ((k : ℝ) - 1 / 2)
  have heU := binomial_jitter_right_error p hpcc n k 1 (by norm_num)
  have heL := binomial_jitter_left_error p hpcc n k 1 (by norm_num)
  simp only [sub_self, abs_zero, zero_div, zero_mul] at heU heL
  have heU := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm heU (abs_nonneg _)))
  have heL := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm heL (abs_nonneg _)))
  rw [heU] at hu
  rw [heL] at hl
  have hzU : ((k : ℝ) + 1 / 2 - n * p) / (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)) =
      binomialZ p n k + (Real.sqrt (p * (1 - p)))⁻¹ / (2 * Real.sqrt (n : ℝ)) := by
    rw [binomialZ, mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le]
    field_simp
    <;> ring
  have hzL : ((k : ℝ) - 1 / 2 - n * p) / (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)) =
      binomialZ p n k + (-(Real.sqrt (p * (1 - p)))⁻¹) / (2 * Real.sqrt (n : ℝ)) := by
    rw [binomialZ, mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le]
    field_simp
    <;> ring
  rw [hzU] at hu
  rw [hzL] at hl
  have htU := edgeworthCDF_shift_remainder n hn1 _ (Real.sqrt (p * (1 - p)))⁻¹ (binomialZ p n k) hκ
  have htL := edgeworthCDF_shift_remainder n hn1 _ (-(Real.sqrt (p * (1 - p)))⁻¹) (binomialZ p n k) hκ
  have hc := div_le_div_of_nonneg_right (effective_binomial_shift_constant p hp) hr.le
  rw [edgeworthShiftConstant_neg] at htL
  have htU' := abs_le.mp (htU.trans hc)
  have htL' := abs_le.mp (htL.trans hc)
  have habs : ∀ a b : ℝ, Real.sqrt (n : ℝ) * |a| ≤ b → |Real.sqrt (n : ℝ) * a| ≤ b := by
    intro a b h
    simpa only [abs_mul, abs_of_pos hr] using h
  have hu'' := abs_le.mp (habs _ _ hu)
  have hl'' := abs_le.mp (habs _ _ hl)
  constructor <;> dsimp only <;> rw [abs_le] <;> constructor <;>
    nlinarith only [hu''.1, hu''.2, hl''.1, hl''.2, htU'.1, htU'.2, htL'.1, htL'.2]

theorem effective_binomial_root_lower (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    (10 : ℝ) ^ 50 ≤ Real.sqrt (n : ℝ) := by
  have hnR : (10 : ℝ) ^ 100 ≤ n := by exact_mod_cast hn
  apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg n)).mpr
  norm_num at hnR ⊢
  exact hnR

theorem effective_binomial_error_budget (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    effectiveClusterError n 0 ((10 : ℝ) ^ 50) + 4 / Real.sqrt (n : ℝ) ≤ 2 / (10 : ℝ) ^ 47 := by
  have hr := effective_binomial_root_lower n hn
  have hr0 : 0 < Real.sqrt (n : ℝ) := by linarith [show (0 : ℝ) < 10 ^ 50 by positivity]
  have hl : Real.log ((10 : ℝ) ^ 50) ≤ 450 := by
    rw [Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    norm_num at *
    linarith
  unfold effectiveClusterError
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero]
  have he : 4 * (1 + Real.log ((10 : ℝ) ^ 50)) / Real.sqrt (n : ℝ) + 4 / Real.sqrt (n : ℝ) ≤
      1808 / Real.sqrt (n : ℝ) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hr0.le
  have hd := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1808)
    (by positivity : (0 : ℝ) < 10 ^ 50) hr
  norm_num at hd ⊢
  linarith

theorem standardizedBernoulli_signed_third (p : ℝ) (hp : p ∈ Ioo 0 1) :
    signedThirdMoment (standardizedBernoulliLaw p hp) = (1 - 2 * p) / Real.sqrt (p * (1 - p)) := by
  rw [signedThirdMoment, integral_standardizedBernoulli]
  have hv := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hs := (Real.sqrt_pos.mpr hv).ne'
  field_simp
  rw [Real.sq_sqrt hv.le]
  ring

theorem phi0_effective_lower : (0.3989 : ℝ) < phi0 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hb : Real.sqrt (2 * Real.pi) < 10000 / 3989 := by nlinarith [Real.pi_lt_d4]
  unfold phi0
  apply (lt_div_iff₀ hs).mpr
  linarith

theorem effective_binomial_endpoint_error (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let h := (Real.sqrt (p * (1 - p)))⁻¹
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope h κ (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 47) ∧
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope (-h) κ (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 47) := by
  have h := effective_binomial_endpoint_expansion S p ((10 : ℝ) ^ 50) hp (by norm_num) n (by omega) k
  exact ⟨h.1.trans (effective_binomial_error_budget n hn), h.2.trans (effective_binomial_error_budget n hn)⟩

theorem effective_binomial_local_error (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℕ) (hk : k ≤ n) :
    |Real.sqrt (n : ℝ) * binomialWeight p n k -
      standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))| ≤ 4 / (10 : ℝ) ^ 47 := by
  have h := effective_binomial_endpoint_error S p hp n hn k
  have hb := effective_binomial_parameters p hp
  rw [binomialWeight_eq_cdf_jump p ⟨hb.1.1.le, hb.1.2.le⟩ n k hk]
  have hu := abs_le.mp h.1
  have hl := abs_le.mp h.2
  dsimp only [edgeworthEnvelope] at hu hl
  simp only [Int.cast_natCast] at hu hl
  rw [div_eq_mul_inv, abs_le]
  constructor <;> nlinarith only [hu.1, hu.2, hl.1, hl.2]

theorem standardNormalDensity_effective_central (z : ℝ) (hz : |z| ≤ 5) :
    (1 / (10 : ℝ) ^ 6) < standardNormalDensity z := by
  have hz2 : z ^ 2 ≤ 25 := by
    have h := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 5)).mpr hz
    norm_num [sq_abs] at h
    exact h
  have hExp : Real.exp (25 / 2) < 390000 := by
    have he : Real.exp (25 / 2) ^ 2 = Real.exp 1 ^ 25 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    have hb := pow_le_pow_left₀ (Real.exp_pos 1).le (show Real.exp 1 ≤ 11 / 4 by linarith [Real.exp_one_lt_d9]) 25
    rw [← he] at hb
    norm_num at hb
    nlinarith [Real.exp_pos (25 / 2)]
  rw [standardNormalDensity_formula]
  have he : Real.exp (-(25 / 2 : ℝ)) ≤ Real.exp (-z ^ 2 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hmin := mul_le_mul_of_nonneg_left he phi0_pos.le
  have hbound : (1 / (10 : ℝ) ^ 6) < phi0 * Real.exp (-(25 / 2 : ℝ)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [phi0_effective_lower]
  exact hbound.trans_le hmin

theorem standardNormalDensity_effective_wide (z : ℝ) (hz : |z| ≤ 11) :
    (1 / (10 : ℝ) ^ 30) < standardNormalDensity z := by
  have hz2 : z ^ 2 ≤ 121 := by
    have h := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 11)).mpr hz
    norm_num [sq_abs] at h
    exact h
  have hExp : Real.exp 61 < (3 : ℝ) ^ 61 := by
    have h : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num : 61 ≠ 0)
  rw [standardNormalDensity_formula]
  have he : Real.exp (-61) ≤ Real.exp (-z ^ 2 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hmin := mul_le_mul_of_nonneg_left he phi0_pos.le
  have hbound : (1 / (10 : ℝ) ^ 30) < phi0 * Real.exp (-61) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    norm_num at hExp ⊢
    linarith [phi0_effective_lower]
  exact hbound.trans_le hmin

theorem effective_binomial_central (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℕ) (hk : k ≤ n)
    (hz : |binomialZ p n k| ≤ 5) :
    (0.99 : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k /
      standardNormalDensity (binomialZ p n k) ∧
    Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k /
      standardNormalDensity (binomialZ p n k) ≤ 1.01 ∧
    (1 / (10 : ℝ) ^ 6) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k := by
  have he := effective_binomial_local_error S p hp n hn k hk
  have hb := effective_binomial_parameters p hp
  have hf := standardNormalDensity_effective_central _ hz
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith [hb.2.1]
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have he' := mul_le_mul_of_nonneg_left he hs.le
  rw [← abs_of_pos hs, ← abs_mul] at he'
  rw [abs_of_pos hs] at he'
  have hid : Real.sqrt (p * (1 - p)) * (Real.sqrt (n : ℝ) * binomialWeight p n k -
      standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))) =
      Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k - standardNormalDensity (binomialZ p n k) := by
    rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n)]
    field_simp
    <;> ring
  rw [hid] at he'
  have he'' := abs_le.mp he'
  have hf0 := standardNormalDensity_pos (binomialZ p n k)
  refine ⟨(le_div_iff₀ hf0).mpr ?_, (div_le_iff₀ hf0).mpr ?_, (div_le_iff₀ hr).mpr ?_⟩
  · nlinarith [hb.2.2.1]
  · nlinarith [hb.2.2.1]
  · have hscale : 2 * standardNormalDensity (binomialZ p n k) ≤ standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p)) := by
      apply (le_div_iff₀ hs).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb.2.2.1 hf0.le]
    have he0 := abs_le.mp he
    nlinarith only [hscale, he0.1, hf]

theorem effective_binomial_wide (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℕ) (hk : k ≤ n)
    (hz : |binomialZ p n k| ≤ 11) :
    Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k := by
  have he := abs_le.mp (effective_binomial_local_error S p hp n hn k hk)
  have hb := effective_binomial_parameters p hp
  have hf := standardNormalDensity_effective_wide _ hz
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith [hb.2.1]
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hscale : 2 * standardNormalDensity (binomialZ p n k) ≤ standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p)) := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb.2.2.1 (standardNormalDensity_pos (binomialZ p n k)).le]
  have hexp : Real.exp (-100) ≤ 1 / (10 : ℝ) ^ 30 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have he2 : (2 : ℝ) ^ 100 ≤ Real.exp 100 := by
      simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
        (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 100
    norm_num at he2 ⊢
    linarith
  apply (div_le_iff₀ hr).mpr
  nlinarith only [he.1, hscale, hf, hexp]

def binomialUpperBranch (p : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * Real.sqrt (n : ℝ) *
    (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k))

def binomialLowerBranch (p : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * Real.sqrt (n : ℝ) *
    (normalCDF (binomialZ p n k) - cdf (binomialMeasure p n) ((k : ℝ) - 1))

def binomialUpperEnvelope (p z : ℝ) : ℝ :=
  standardNormalDensity z / (6 * (p ^ 2 + (1 - p) ^ 2)) * (3 + (1 - 2 * p) - (1 - 2 * p) * z ^ 2)

def binomialLowerEnvelope (p z : ℝ) : ℝ :=
  standardNormalDensity z / (6 * (p ^ 2 + (1 - p) ^ 2)) * (3 - (1 - 2 * p) + (1 - 2 * p) * z ^ 2)

theorem binomial_branch_envelope_identities (p : ℝ) (hp : p ∈ Ioo 0 1) (z : ℝ) :
    binomialUpperEnvelope p z = Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) *
      edgeworthEnvelope (Real.sqrt (p * (1 - p)))⁻¹ (signedThirdMoment (standardizedBernoulliLaw p hp)) z ∧
    binomialLowerEnvelope p z = -(Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) *
      edgeworthEnvelope (-(Real.sqrt (p * (1 - p)))⁻¹) (signedThirdMoment (standardizedBernoulliLaw p hp)) z) := by
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  rw [standardizedBernoulli_signed_third]
  unfold binomialUpperEnvelope binomialLowerEnvelope edgeworthEnvelope
  constructor <;> field_simp <;> ring

theorem effective_binomial_branches (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ) :
    |binomialUpperBranch p n k - binomialUpperEnvelope p (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10 ∧
    |binomialLowerBranch p n k - binomialLowerEnvelope p (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10 := by
  have hb := effective_binomial_parameters p hp
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by linarith [hb.2.2.2.1]
  have hA0 : 0 ≤ Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) := by positivity
  have hA1 : Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) ≤ 1 := by
    apply (div_le_one hτ).mpr
    linarith [hb.2.2.1, hb.2.2.2.1]
  have he := effective_binomial_endpoint_error S p hp n hn k
  have hE := binomial_branch_envelope_identities p hb.1 (binomialZ p n k)
  have hu := mul_le_mul_of_nonneg_left he.1 hA0
  have hl := mul_le_mul_of_nonneg_left he.2 hA0
  have hbudget : Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * (2 / (10 : ℝ) ^ 47) ≤ 2 / (10 : ℝ) ^ 10 := by
    nlinarith only [hA1]
  have hidU : binomialUpperBranch p n k - binomialUpperEnvelope p (binomialZ p n k) =
      Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) *
        (Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k)) -
          edgeworthEnvelope (Real.sqrt (p * (1 - p)))⁻¹ (signedThirdMoment (standardizedBernoulliLaw p hb.1)) (binomialZ p n k)) := by
    rw [hE.1, binomialUpperBranch]
    ring
  have hidL : binomialLowerBranch p n k - binomialLowerEnvelope p (binomialZ p n k) =
      -(Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) *
        (Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)) -
          edgeworthEnvelope (-(Real.sqrt (p * (1 - p)))⁻¹) (signedThirdMoment (standardizedBernoulliLaw p hb.1)) (binomialZ p n k))) := by
    rw [hE.2, binomialLowerBranch]
    ring
  rw [hidU, hidL, abs_neg, abs_mul, abs_mul, abs_of_nonneg hA0]
  exact ⟨hu.trans hbudget, hl.trans hbudget⟩

theorem effective_binomial_nearest_z (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    |binomialZ p n (round ((n : ℝ) * p))| ≤ 0.001 := by
  have hb := effective_binomial_parameters p hp
  have hr := effective_binomial_root_lower n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith [hb.2.1]
  have hnr : (10000 : ℝ) ≤ Real.sqrt (n : ℝ) := by norm_num at hr; linarith
  have hprod := mul_le_mul hnr hb.2.1 (by norm_num : (0 : ℝ) ≤ 0.48) (Real.sqrt_nonneg _)
  rw [binomialZ, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le]
  apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hn0) hs)).mpr
  have hround : |(round ((n : ℝ) * p) : ℝ) - (n : ℝ) * p| ≤ 1 / 2 := by
    simpa only [abs_sub_comm] using abs_sub_round ((n : ℝ) * p)
  nlinarith only [hround, hprod]

theorem binomialUpperEnvelope_effective_near_zero (p z : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hz : |z| ≤ 0.001) :
    (0.395 : ℝ) < binomialUpperEnvelope p z := by
  have hb := effective_binomial_parameters p hp
  have hz2 : z ^ 2 ≤ 0.000001 := by
    have h := (sq_le_sq₀ (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 0.001)).mpr hz
    norm_num [sq_abs] at h ⊢
    exact h
  have hd : (0.3988 : ℝ) < standardNormalDensity z := by
    have he : (0.9999995 : ℝ) ≤ Real.exp (-z ^ 2 / 2) := by
      nlinarith [Real.add_one_le_exp (-z ^ 2 / 2)]
    have hm := mul_le_mul phi0_effective_lower.le he (by norm_num : (0 : ℝ) ≤ 0.9999995) phi0_pos.le
    rw [standardNormalDensity_formula]
    nlinarith only [hm]
  have hpoly : (3.099 : ℝ) ≤ 3 + (1 - 2 * p) - (1 - 2 * p) * z ^ 2 := by
    have hm := mul_le_mul (show 1 - 2 * p ≤ (0.2 : ℝ) by linarith [hp.1]) hz2 (sq_nonneg z) (by norm_num : (0 : ℝ) ≤ 0.2)
    nlinarith [hp.2]
  have hτ : 0 < 6 * (p ^ 2 + (1 - p) ^ 2) := by linarith [hb.2.2.2.1]
  have hm := mul_le_mul hd.le hpoly (by norm_num : (0 : ℝ) ≤ 3.099) (standardNormalDensity_pos z).le
  unfold binomialUpperEnvelope
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ hτ).mpr
  nlinarith [hb.2.2.2.2]

def binomialNormalizedConstant (p : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * binomialKolmogorov p n

theorem binomialUpperBranch_le_constant (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) (k : ℤ) :
    binomialUpperBranch p n k ≤ binomialNormalizedConstant p n := by
  have hd := (le_abs_self (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k))).trans
    (binomialDiscrepancy_le_Kolmogorov p ⟨hp.1.le, hp.2.le⟩ n k)
  have hA : 0 ≤ Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * Real.sqrt (n : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left hd hA
  unfold binomialUpperBranch binomialNormalizedConstant
  rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n)]
  convert h using 1 <;> ring

theorem effective_binomial_constant_lower (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    (0.39 : ℝ) < binomialNormalizedConstant p n := by
  let k := round ((n : ℝ) * p)
  have he := abs_le.mp (effective_binomial_branches S p hp n hn k).1
  have hA := binomialUpperEnvelope_effective_near_zero p (binomialZ p n k) hp (effective_binomial_nearest_z p hp n hn)
  have hB := binomialUpperBranch_le_constant p (effective_binomial_parameters p hp).1 n k
  nlinarith only [he.1, hA, hB]

theorem binomialNormalizedConstant_lt_cE (B : PublishedBernoulliBound) (p : ℝ)
    (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) :
    binomialNormalizedConstant p n < cE := by
  have hs : 0 < Real.sqrt ((n : ℝ) * p * (1 - p)) := Real.sqrt_pos.mpr
    (mul_pos (mul_pos (by exact_mod_cast (by omega : 0 < n)) hp.1) (sub_pos.mpr hp.2))
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  have h := mul_lt_mul_of_pos_left (B.strict_bound p hp n hn) (div_pos hs hτ)
  unfold binomialNormalizedConstant
  convert h using 1
  field_simp

theorem binomialNormalizedConstant_eq_sup (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) :
    binomialNormalizedConstant p n =
      sSup (Set.range (normalizedDiscrepancy (standardizedBernoulliLaw p hp) n)) := by
  let a := Real.sqrt ((n : ℝ) * p * (1 - p))
  let c := a / (p ^ 2 + (1 - p) ^ 2)
  have ha : 0 < a := Real.sqrt_pos.mpr
    (mul_pos (mul_pos (by exact_mod_cast (by omega : 0 < n)) hp.1) (sub_pos.mpr hp.2))
  have hc : 0 ≤ c := by dsimp [c, a]; positivity
  have hsur : Function.Surjective (fun t : ℝ => (t - (n : ℝ) * p) / a) := by
    intro z
    refine ⟨a * z + n * p, ?_⟩
    field_simp
    <;> ring
  have hpoint : (fun t : ℝ => c * |cdf (binomialMeasure p n) t - normalCDF ((t - n * p) / a)|) =
      (normalizedDiscrepancy (standardizedBernoulliLaw p hp) n) ∘ (fun t => (t - n * p) / a) := by
    funext t
    exact (standardizedBernoulli_discrepancy p hp n hn t).symm
  change c * sSup (Set.range (fun t : ℝ => |cdf (binomialMeasure p n) t - normalCDF ((t - n * p) / a)|)) = _
  have hm := Real.smul_iSup_of_nonneg hc (fun t : ℝ => |cdf (binomialMeasure p n) t - normalCDF ((t - n * p) / a)|)
  change c * sSup (Set.range (fun t : ℝ => |cdf (binomialMeasure p n) t - normalCDF ((t - n * p) / a)|)) =
    sSup (Set.range (fun t : ℝ => c * |cdf (binomialMeasure p n) t - normalCDF ((t - n * p) / a)|)) at hm
  rw [hm, hpoint, Set.range_comp, hsur.range_eq, Set.image_univ]

def binomialIntegerWeight (p : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  if 0 ≤ k then binomialWeight p n k.toNat else 0

theorem effective_binomial_integer_mass (B : PublishedBernoulliBound) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 1 ≤ n) :
    sSup (Set.range (binomialIntegerWeight p n)) ≤ 2 / Real.sqrt (n : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k, rfl⟩
  unfold binomialIntegerWeight
  split_ifs
  · exact effective_binomial_mass_upper B p hp n k.toNat hn
  · positivity

theorem effective_binomial_central_index (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ) (hz : |binomialZ p n k| ≤ 11) :
    0 ≤ k ∧ k.toNat ≤ n := by
  have hb := effective_binomial_parameters p hp
  have hr := effective_binomial_root_lower n hn
  have hr0 := Real.sqrt_nonneg (n : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq := Real.sq_sqrt hn0.le
  have hnr : (100 : ℝ) ≤ Real.sqrt (n : ℝ) := by norm_num at hr; linarith
  have hv := mul_pos hb.1.1 (sub_pos.mpr hb.1.2)
  rw [binomialZ, abs_div, abs_of_pos (Real.sqrt_pos.mpr (mul_pos (mul_pos hn0 hb.1.1) (sub_pos.mpr hb.1.2))),
    mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le] at hz
  have hdist := (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hv))).mp hz
  have hscale := mul_le_mul_of_nonneg_left hb.2.2.1 hr0
  have hdist' : |(k : ℝ) - n * p| ≤ 11 / 2 * Real.sqrt (n : ℝ) := by nlinarith only [hdist, hscale]
  have hd := abs_le.mp hdist'
  have hlo := mul_le_mul_of_nonneg_left hp.1 hn0.le
  have hhi := mul_le_mul_of_nonneg_left hp.2 hn0.le
  have hroot := mul_nonneg hr0 (sub_nonneg.mpr hnr)
  have hk0 : (0 : ℝ) ≤ k := by nlinarith only [hd.1, hlo, hroot, hsq, hr0]
  have hkn : (k : ℝ) ≤ n := by nlinarith only [hd.2, hhi, hroot, hsq, hr0]
  have hk0I : (0 : ℤ) ≤ k := by exact_mod_cast hk0
  refine ⟨hk0I, ?_⟩
  have hknI : k ≤ (n : ℤ) := by exact_mod_cast hkn
  exact Int.toNat_le.mpr (by exact_mod_cast hknI)

theorem effective_binomial_integer_central (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ)
    (hz : |binomialZ p n k| ≤ 5) :
    (0.99 : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) ∧
    Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) ≤ 1.01 ∧
    (1 / (10 : ℝ) ^ 6) / Real.sqrt (n : ℝ) ≤ binomialIntegerWeight p n k := by
  have hk := effective_binomial_central_index p hp n hn k (by linarith)
  have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.1
  rw [binomialIntegerWeight, if_pos hk.1]
  have h := effective_binomial_central S p hp n hn k.toNat hk.2 (by rwa [he])
  simpa only [he] using h

theorem effective_binomial_integer_wide (S : PublishedSignedSmoothing) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ)
    (hz : |binomialZ p n k| ≤ 11) :
    Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialIntegerWeight p n k := by
  have hk := effective_binomial_central_index p hp n hn k hz
  have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.1
  rw [binomialIntegerWeight, if_pos hk.1]
  exact effective_binomial_wide S p hp n hn k.toNat hk.2 (by rwa [he])

theorem binomialIntegerWeight_eq_mass (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ) :
    binomialIntegerWeight p n k = (binomialMeasure p n).real {(k : ℝ)} := by
  classical
  have hsum : (binomialMeasure p n).real {(k : ℝ)} =
      ∑ j ∈ Finset.range (n + 1), if (j : ℝ) = (k : ℝ) then binomialWeight p n j else 0 := by
    rw [Measure.real, binomialMeasure_blocks p hp, Measure.finset_sum_apply]
    rw [ENNReal.toReal_sum (by
      intro j hj
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top (blockWeight_ne_top p n j) (by finiteness))]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, blockWeight_toReal p hp]
    by_cases h : (j : ℝ) = (k : ℝ)
    · rw [Measure.dirac_apply_of_mem (show (j : ℝ) ∈ {(k : ℝ)} from h)]
      simp [h, binomialWeight]
    · rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
      simp only [Set.indicator_of_notMem (show (j : ℝ) ∉ {(k : ℝ)} from h)]
      simp [h]
  rw [hsum, binomialIntegerWeight]
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    have hc : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    have he : ∀ j : ℕ, ((j : ℝ) = (k : ℝ)) ↔ j = k.toNat := by
      intro j
      rw [← hc]
      exact Nat.cast_inj
    simp_rw [he]
    by_cases hkn : k.toNat ≤ n
    · simp [hkn, Nat.lt_succ_iff]
    · simp [hkn, Nat.lt_succ_iff, binomialWeight, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn)]
  · rw [if_neg hk]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hne : (j : ℝ) ≠ (k : ℝ) := by
      have hkR : (k : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hk)
      exact ne_of_gt (hkR.trans_le (Nat.cast_nonneg j))
    simp [hne]

end BerryEsseen
