import BerryEsseen.ManuscriptBinomialFourier
import BerryEsseen.GeneralBinomialConsequences

/-! Original cutoffs and the original Taylor coefficient in the effective
binomial lemma. The smoothing estimate is connected separately: these
numerical estimates do not assert an unproved smoothing interface. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_binomial_cutoff_twelve_budget (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    effectiveClusterError n 0 ((10 : ℝ) ^ 12) < 1 / (10 : ℝ) ^ 10 := by
  have hr := effective_binomial_root_lower n hn
  have hr0 : 0 < Real.sqrt (n : ℝ) := by linarith [show (0 : ℝ) < 10 ^ 50 by positivity]
  have hl : Real.log ((10 : ℝ) ^ 12) ≤ 108 := by
    rw [Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    norm_num at *
    linarith
  unfold effectiveClusterError
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero]
  have h1 := div_le_div_of_nonneg_right (show 4 * (1 + Real.log ((10 : ℝ) ^ 12)) ≤ 436 by linarith) hr0.le
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 436)
    (by positivity : (0 : ℝ) < 10 ^ 50) hr
  norm_num at h2 ⊢
  linarith

theorem manuscript_exp_two_hundred_lower : (10 : ℝ) ^ 60 ≤ Real.exp 200 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he 200
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp ⊢
  linarith

theorem manuscript_binomial_cutoff_exp_budget (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    effectiveClusterError n 0 (Real.exp 200) < 1 / (10 : ℝ) ^ 47 := by
  have hr := effective_binomial_root_lower n hn
  unfold effectiveClusterError
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero, Real.log_exp]
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 804)
    (by positivity : (0 : ℝ) < 10 ^ 50) hr
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 50)
    (by positivity : (0 : ℝ) < 10 ^ 60) manuscript_exp_two_hundred_lower
  norm_num at h1 h2 ⊢
  linarith

theorem manuscript_gaussianCDF_first_remainder (x a : ℝ) :
    |normalCDF (x + a) - normalCDF x - a * standardNormalDensity x| ≤ a ^ 2 / 8 := by
  have hb : ∀ u, |-u * standardNormalDensity u| ≤ 1 / 4 := by
    intro u
    simpa only [neg_mul, abs_neg] using gaussian_first_monomial_effective u
  convert taylor_second_global normalCDF standardNormalDensity
    (fun u => -u * standardNormalDensity u) (1 / 4) normalCDF_hasDerivAt
    standardNormalDensity_hasDerivAt hb x a using 1 <;> simp only [sq_abs] <;> ring

theorem manuscript_gaussian_second_polynomial_lipschitz (x y : ℝ) :
    |(1 - y ^ 2) * standardNormalDensity y - (1 - x ^ 2) * standardNormalDensity x| ≤
      (5 / 4) * |y - x| := by
  have hb : ∀ t, ‖(t ^ 3 - 3 * t) * standardNormalDensity t‖ ≤ 5 / 4 := by
    intro t
    rw [Real.norm_eq_abs, show t ^ 3 - 3 * t = -(3 * t - t ^ 3) by ring, neg_mul, abs_neg]
    exact gaussian_third_derivative_effective t
  simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (gaussian_x_density_second_hasDerivAt t).hasDerivWithinAt)
    (fun t _ => hb t) (mem_univ x) (mem_univ y)

theorem manuscript_edgeworthCDF_shift_remainder (n : ℕ) (hn : 1 ≤ n) (κ b x : ℝ) :
    |Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + b / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope b κ x| ≤ (b ^ 2 / 32 + 5 * |κ| * |b| / 48) / Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  let a := b / (2 * s)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  let A := normalCDF (x + a) - normalCDF x - a * standardNormalDensity x
  let B := (1 - (x + a) ^ 2) * standardNormalDensity (x + a) - (1 - x ^ 2) * standardNormalDensity x
  have hA : |A| ≤ a ^ 2 / 8 := manuscript_gaussianCDF_first_remainder x a
  have hB : |B| ≤ (5 / 4) * |a| := by
    simpa only [add_sub_cancel_left] using manuscript_gaussian_second_polynomial_lipschitz x (x + a)
  have he : s * (edgeworthCDF n κ (x + a) - normalCDF x) - edgeworthEnvelope b κ x =
      s * (A + κ / (6 * s) * B) := by
    dsimp [A, B, edgeworthCDF, edgeworthEnvelope, a, s]
    field_simp [hs.ne']
    <;> ring
  change |s * (edgeworthCDF n κ (x + a) - normalCDF x) - edgeworthEnvelope b κ x| ≤ _
  rw [he, abs_mul, abs_of_pos hs]
  have hbnd : |A + κ / (6 * s) * B| ≤ a ^ 2 / 8 + |κ| / (6 * s) * ((5 / 4) * |a|) := by
    calc
      _ ≤ |A| + |κ / (6 * s)| * |B| := by simpa only [abs_mul] using abs_add_le A (κ / (6 * s) * B)
      _ ≤ _ := by
        rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
        exact add_le_add hA (mul_le_mul_of_nonneg_left hB (by positivity))
  calc
    _ ≤ s * (a ^ 2 / 8 + |κ| / (6 * s) * ((5 / 4) * |a|)) := mul_le_mul_of_nonneg_left hbnd hs.le
    _ = _ := by
      change _ = (b ^ 2 / 32 + 5 * |κ| * |b| / 48) / s
      dsimp [a]
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      field_simp [hs.ne']
      <;> ring

theorem manuscript_binomial_shift_coefficient (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let b := (Real.sqrt (p * (1 - p)))⁻¹
    b ^ 2 / 32 + 5 * |κ| * |b| / 48 ≤ 1 / 4 := by
  have hv : (6 / 25 : ℝ) ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hv0 : 0 < p * (1 - p) := by linarith
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hv0
  have hd : 0 ≤ 1 - 2 * p := by linarith [hp.2]
  dsimp only
  rw [standardizedBernoulli_signed_third, abs_div, abs_of_nonneg hd, abs_of_pos hs,
    abs_of_pos (inv_pos.mpr hs)]
  have he : (Real.sqrt (p * (1 - p)))⁻¹ ^ 2 / 32 +
      5 * ((1 - 2 * p) / Real.sqrt (p * (1 - p))) * (Real.sqrt (p * (1 - p)))⁻¹ / 48 =
      (1 / 32 + 5 * (1 - 2 * p) / 48) / (p * (1 - p)) := by
    have hsq := Real.sq_sqrt hv0.le
    field_simp [hs.ne', hv0.ne']
    rw [hsq]
    exact (eq_div_iff hv0.ne').mpr (by ring)
  rw [he]
  apply (div_le_iff₀ hv0).mpr
  linarith [hp.1]

theorem manuscript_binomial_shift_remainder (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let b := (Real.sqrt (p * (1 - p)))⁻¹
    (|Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + b / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope b κ x| ≤ 1 / (4 * Real.sqrt (n : ℝ))) ∧
    (|Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + (-b) / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope (-b) κ x| ≤ 1 / (4 * Real.sqrt (n : ℝ))) := by
  let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
  let b := (Real.sqrt (p * (1 - p)))⁻¹
  have hc : b ^ 2 / 32 + 5 * |κ| * |b| / 48 ≤ 1 / 4 := manuscript_binomial_shift_coefficient p hp
  have hbound := div_le_div_of_nonneg_right hc (Real.sqrt_nonneg (n : ℝ))
  have hu := manuscript_edgeworthCDF_shift_remainder n hn κ b x
  have hl := manuscript_edgeworthCDF_shift_remainder n hn κ (-b) x
  rw [neg_sq, abs_neg] at hl
  refine ⟨?_, ?_⟩
  · convert hu.trans hbound using 1 <;> ring
  · convert hl.trans hbound using 1 <;> ring

/-- Exact endpoint consequence of a concrete jitter error. This is an internal
implication, not a literature premise or an asserted jitter estimate. -/
theorem manuscript_binomial_endpoint_of_jitter (p E : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 1 ≤ n)
    (hJ : ∀ x : ℝ, Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter 1) x -
      edgeworthCDF n (signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1))
        ((x - (n : ℝ) * p) / (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))| ≤ E)
    (k : ℤ) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let h := (Real.sqrt (p * (1 - p)))⁻¹
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope h κ (binomialZ p n k)| ≤ E + 1 / (4 * Real.sqrt (n : ℝ))) ∧
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope (-h) κ (binomialZ p n k)| ≤ E + 1 / (4 * Real.sqrt (n : ℝ))) := by
  have hb := effective_binomial_parameters p hp
  have hpcc : p ∈ Icc 0 1 := ⟨hb.1.1.le, hb.1.2.le⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := Real.sqrt_pos.mpr hn0
  have hu := hJ ((k : ℝ) + 1 / 2)
  have hl := hJ ((k : ℝ) - 1 / 2)
  rw [(binomial_unit_jitter_endpoints p hpcc n k).1] at hu
  rw [(binomial_unit_jitter_endpoints p hpcc n k).2] at hl
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
  have ht := manuscript_binomial_shift_remainder p hp n hn (binomialZ p n k)
  have htU := abs_le.mp ht.1
  have htL := abs_le.mp ht.2
  have hu' : |Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k -
      edgeworthCDF n (signedThirdMoment (standardizedBernoulliLaw p hb.1))
        (binomialZ p n k + (Real.sqrt (p * (1 - p)))⁻¹ / (2 * Real.sqrt (n : ℝ))))| ≤ E := by
    simpa only [abs_mul, abs_of_pos hr] using hu
  have hl' : |Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) -
      edgeworthCDF n (signedThirdMoment (standardizedBernoulliLaw p hb.1))
        (binomialZ p n k + (-(Real.sqrt (p * (1 - p)))⁻¹) / (2 * Real.sqrt (n : ℝ))))| ≤ E := by
    simpa only [abs_mul, abs_of_pos hr] using hl
  have hu'' := abs_le.mp hu'
  have hl'' := abs_le.mp hl'
  constructor <;> dsimp only <;> rw [abs_le] <;> constructor <;>
    nlinarith only [hu''.1, hu''.2, hl''.1, hl''.2, htU.1, htU.2, htL.1, htL.2]

def manuscriptBinomialJitterError (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter 1) x -
    edgeworthCDF n (signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1))
      ((x - (n : ℝ) * p) / (Real.sqrt (p * (1 - p)) * Real.sqrt (n : ℝ)))|

theorem manuscript_binomial_endpoint_error_twelve_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12))
    (k : ℤ) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let h := (Real.sqrt (p * (1 - p)))⁻¹
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope h κ (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10) ∧
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope (-h) κ (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10) := by
  have h := manuscript_binomial_endpoint_of_jitter p _ hp n (by omega) hJ k
  have hE := manuscript_binomial_cutoff_twelve_budget n hn
  have hr := effective_binomial_root_lower n hn
  have ht := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : (0 : ℝ) < 4 * 10 ^ 50) (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4))
  have hb : effectiveClusterError n 0 ((10 : ℝ) ^ 12) + 1 / (4 * Real.sqrt (n : ℝ)) ≤ 2 / (10 : ℝ) ^ 10 := by
    norm_num at ht hE ⊢
    linarith
  exact ⟨h.1.trans hb, h.2.trans hb⟩

theorem manuscript_binomial_endpoint_error_exp_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 (Real.exp 200))
    (k : ℤ) :
    let κ := signedThirdMoment (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1)
    let h := (Real.sqrt (p * (1 - p)))⁻¹
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) k - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope h κ (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 47) ∧
    (|Real.sqrt (n : ℝ) * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)) -
      edgeworthEnvelope (-h) κ (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 47) := by
  have h := manuscript_binomial_endpoint_of_jitter p _ hp n (by omega) hJ k
  have hE := manuscript_binomial_cutoff_exp_budget n hn
  have hr := effective_binomial_root_lower n hn
  have ht := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : (0 : ℝ) < 4 * 10 ^ 50) (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4))
  have hb : effectiveClusterError n 0 (Real.exp 200) + 1 / (4 * Real.sqrt (n : ℝ)) ≤ 2 / (10 : ℝ) ^ 47 := by
    norm_num at ht hE ⊢
    linarith
  exact ⟨h.1.trans hb, h.2.trans hb⟩

theorem manuscript_binomial_local_error_exp_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 (Real.exp 200))
    (k : ℕ) (hk : k ≤ n) :
    |Real.sqrt (n : ℝ) * binomialWeight p n k -
      standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))| ≤ 4 / (10 : ℝ) ^ 47 := by
  have h := manuscript_binomial_endpoint_error_exp_of_jitter p hp n hn hJ k
  have hb := effective_binomial_parameters p hp
  rw [binomialWeight_eq_cdf_jump p ⟨hb.1.1.le, hb.1.2.le⟩ n k hk]
  have hu := abs_le.mp h.1
  have hl := abs_le.mp h.2
  dsimp only [edgeworthEnvelope] at hu hl
  simp only [Int.cast_natCast] at hu hl
  rw [div_eq_mul_inv, abs_le]
  constructor <;> nlinarith only [hu.1, hu.2, hl.1, hl.2]

theorem manuscript_gaussian_density_wide (z : ℝ) (hz : |z| ≤ 11) :
    Real.exp (-62) < standardNormalDensity z := by
  have hz2 : z ^ 2 ≤ 121 := by nlinarith [sq_abs z, (abs_le.mp hz).1, (abs_le.mp hz).2]
  have hp0 : Real.exp (-(3 / 2 : ℝ)) < phi0 := by
    rw [Real.exp_neg, ← one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    have he := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith [phi0_effective_lower]
  rw [standardNormalDensity_formula]
  have he : Real.exp (-62) = Real.exp (-(3 / 2 : ℝ)) * Real.exp (-(121 / 2 : ℝ)) := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  apply (mul_lt_mul_of_pos_right hp0 (Real.exp_pos _)).trans_le
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) phi0_pos.le

theorem manuscript_binomial_wide_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 (Real.exp 200))
    (k : ℕ) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 11) :
    Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k := by
  have he := abs_le.mp (manuscript_binomial_local_error_exp_of_jitter p hp n hn hJ k hk)
  have hb := effective_binomial_parameters p hp
  have hf := manuscript_gaussian_density_wide _ hz
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith [hb.2.1]
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hscale : 2 * standardNormalDensity (binomialZ p n k) ≤
      standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p)) := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb.2.2.1 (standardNormalDensity_pos (binomialZ p n k)).le]
  have hExp62 : Real.exp 62 ≤ (10 : ℝ) ^ 30 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le (show Real.exp 1 ≤ 3 by linarith [Real.exp_one_lt_d9]) 62
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  have hsmall : 4 / (10 : ℝ) ^ 47 ≤ Real.exp (-62) := by
    rw [Real.exp_neg, ← one_div]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hm := mul_le_mul_of_nonneg_left hExp62 (by norm_num : (0 : ℝ) ≤ 4 / 10 ^ 47)
    norm_num at hm ⊢
    linarith
  have hExp := Real.exp_le_exp.mpr (by norm_num : (-100 : ℝ) ≤ -62)
  apply (div_le_iff₀ hr).mpr
  nlinarith only [he.1, hf, hscale, hsmall, hExp]

theorem manuscript_binomial_local_error_twelve_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12))
    (k : ℕ) (hk : k ≤ n) :
    |Real.sqrt (n : ℝ) * binomialWeight p n k -
      standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))| ≤ 4 / (10 : ℝ) ^ 10 := by
  have h := manuscript_binomial_endpoint_error_twelve_of_jitter p hp n hn hJ k
  have hb := effective_binomial_parameters p hp
  rw [binomialWeight_eq_cdf_jump p ⟨hb.1.1.le, hb.1.2.le⟩ n k hk]
  have hu := abs_le.mp h.1
  have hl := abs_le.mp h.2
  dsimp only [edgeworthEnvelope] at hu hl
  simp only [Int.cast_natCast] at hu hl
  rw [div_eq_mul_inv, abs_le]
  constructor <;> nlinarith only [hu.1, hu.2, hl.1, hl.2]

theorem manuscript_binomial_central_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12))
    (k : ℕ) (hk : k ≤ n)
    (hz : |binomialZ p n k| ≤ 5) :
    (0.99 : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k /
      standardNormalDensity (binomialZ p n k) ∧
    Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k /
      standardNormalDensity (binomialZ p n k) ≤ 1.01 ∧
    (1 / (10 : ℝ) ^ 6) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k := by
  have he := manuscript_binomial_local_error_twelve_of_jitter p hp n hn hJ k hk
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

theorem manuscript_binomial_branches_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12))
    (k : ℤ) :
    |binomialUpperBranch p n k - binomialUpperEnvelope p (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10 ∧
    |binomialLowerBranch p n k - binomialLowerEnvelope p (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10 := by
  have hb := effective_binomial_parameters p hp
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by linarith [hb.2.2.2.1]
  have hA0 : 0 ≤ Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) := by positivity
  have hA1 : Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) ≤ 1 := by
    apply (div_le_one hτ).mpr
    linarith [hb.2.2.1, hb.2.2.2.1]
  have he := manuscript_binomial_endpoint_error_twelve_of_jitter p hp n hn hJ k
  have hE := binomial_branch_envelope_identities p hb.1 (binomialZ p n k)
  have hu := mul_le_mul_of_nonneg_left he.1 hA0
  have hl := mul_le_mul_of_nonneg_left he.2 hA0
  have hbudget : Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * (2 / (10 : ℝ) ^ 10) ≤ 2 / (10 : ℝ) ^ 10 := by
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


theorem manuscript_binomial_nearest_z (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    |binomialZ p n (round ((n : ℝ) * p))| ≤ 1 / (10 : ℝ) ^ 5 := by
  have hb := effective_binomial_parameters p hp
  have hr := effective_binomial_root_lower n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith [hb.2.1]
  have hnr : (1000000 : ℝ) ≤ Real.sqrt (n : ℝ) := by norm_num at hr; linarith
  have hprod := mul_le_mul hnr hb.2.1 (by norm_num : (0 : ℝ) ≤ 0.48) (Real.sqrt_nonneg _)
  rw [binomialZ, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le]
  apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hn0) hs)).mpr
  have hround : |(round ((n : ℝ) * p) : ℝ) - (n : ℝ) * p| ≤ 1 / 2 := by
    simpa only [abs_sub_comm] using abs_sub_round ((n : ℝ) * p)
  nlinarith only [hround, hprod]

theorem manuscript_binomial_envelope_quadratic_lower (p z : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    binomialCentralLimit p - z ^ 2 ≤ binomialUpperEnvelope p z := by
  have hb := effective_binomial_parameters p hp
  have hd0 : 0 ≤ 1 - 2 * p := by linarith [hp.2]
  have hd1 : 1 - 2 * p ≤ (1 / 5 : ℝ) := by linarith [hp.1]
  have hf0 := (standardNormalDensity_pos z).le
  have hf1 := standardNormalDensity_le_phi0 z
  have hf2 : standardNormalDensity z ≤ (2 / 5 : ℝ) := hf1.trans phi0_lt_two_fifths.le
  have hD : phi0 - standardNormalDensity z ≤ z ^ 2 / 5 := by
    have hg := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-z ^ 2 / 2)) phi0_pos.le
    have hm := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le (sq_nonneg z)
    rw [← standardNormalDensity_formula] at hg
    nlinarith only [hg, hm]
  have hm1 := mul_le_mul hD (show 3 + (1 - 2 * p) ≤ (16 / 5 : ℝ) by linarith)
    (by linarith : 0 ≤ 3 + (1 - 2 * p)) (by positivity : (0 : ℝ) ≤ z ^ 2 / 5)
  have hm2 := mul_le_mul hf2 hd1 hd0 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hm3 := mul_le_mul_of_nonneg_right hm2 (sq_nonneg z)
  have hm4 := mul_le_mul_of_nonneg_right hb.2.2.2.1 (sq_nonneg z)
  have hτ : 0 < 6 * (p ^ 2 + (1 - p) ^ 2) := by linarith [hb.2.2.2.1]
  have hnum : phi0 * (3 + (1 - 2 * p)) - (6 * (p ^ 2 + (1 - p) ^ 2)) * z ^ 2 ≤
      standardNormalDensity z * (3 + (1 - 2 * p) - (1 - 2 * p) * z ^ 2) := by
    nlinarith only [hm1, hm3, hm4, sq_nonneg z]
  calc
    binomialCentralLimit p - z ^ 2 =
        (phi0 * (3 + (1 - 2 * p)) - (6 * (p ^ 2 + (1 - p) ^ 2)) * z ^ 2) /
          (6 * (p ^ 2 + (1 - p) ^ 2)) := by
      unfold binomialCentralLimit
      have hv : p ^ 2 + (1 - p) ^ 2 ≠ 0 := by linarith [hb.2.2.2.1]
      field_simp [hv]
      <;> ring
    _ ≤ (standardNormalDensity z * (3 + (1 - 2 * p) - (1 - 2 * p) * z ^ 2)) /
          (6 * (p ^ 2 + (1 - p) ^ 2)) := div_le_div_of_nonneg_right hnum hτ.le
    _ = binomialUpperEnvelope p z := by unfold binomialUpperEnvelope; ring

theorem manuscript_binomial_central_limit_lower (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    (0.396 : ℝ) < binomialCentralLimit p := by
  have hb := effective_binomial_parameters p hp
  have hprod := mul_le_mul phi0_effective_lower.le
    (show (1.55 : ℝ) ≤ 2 - p by linarith [hp.2])
    (by norm_num : (0 : ℝ) ≤ 1.55) phi0_pos.le
  have hτ : 0 < 3 * (p ^ 2 + (1 - p) ^ 2) := by linarith [hb.2.2.2.1]
  unfold binomialCentralLimit
  apply (lt_div_iff₀ hτ).mpr
  nlinarith only [hprod, hb.2.2.2.2]

theorem manuscript_binomial_constant_lower_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12)) :
    binomialCentralLimit p - 3 / (10 : ℝ) ^ 10 ≤ binomialNormalizedConstant p n ∧
    (0.39 : ℝ) < binomialNormalizedConstant p n := by
  let k := round ((n : ℝ) * p)
  have he := (abs_le.mp (manuscript_binomial_branches_of_jitter p hp n hn hJ k).1).1
  have hz := manuscript_binomial_nearest_z p hp n hn
  have hz2 : (binomialZ p n k) ^ 2 ≤ 1 / (10 : ℝ) ^ 10 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / 10 ^ 5)).mpr hz
    norm_num [sq_abs] at h ⊢
    exact h
  have hA := manuscript_binomial_envelope_quadratic_lower p (binomialZ p n k) hp
  have hB := binomialUpperBranch_le_constant p (effective_binomial_parameters p hp).1 n k
  have hbound : binomialCentralLimit p - 3 / (10 : ℝ) ^ 10 ≤ binomialNormalizedConstant p n := by
    nlinarith only [he, hz2, hA, hB]
  refine ⟨hbound, ?_⟩
  have hg := manuscript_binomial_central_limit_lower p hp
  nlinarith only [hbound, hg]

theorem manuscript_binomial_integer_central_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12)) (k : ℤ)
    (hz : |binomialZ p n k| ≤ 5) :
    (0.99 : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) ∧
    Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) ≤ 1.01 ∧
    (1 / (10 : ℝ) ^ 6) / Real.sqrt (n : ℝ) ≤ binomialIntegerWeight p n k := by
  have hk := effective_binomial_central_index p hp n hn k (by linarith)
  have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.1
  rw [binomialIntegerWeight, if_pos hk.1]
  have h := manuscript_binomial_central_of_jitter p hp n hn hJ k.toNat hk.2 (by rwa [he])
  simpa only [he] using h

theorem manuscript_binomial_integer_wide_of_jitter (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hJ : ∀ x, manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 (Real.exp 200)) (k : ℤ)
    (hz : |binomialZ p n k| ≤ 11) :
    Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialIntegerWeight p n k := by
  have hk := effective_binomial_central_index p hp n hn k hz
  have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.1
  rw [binomialIntegerWeight, if_pos hk.1]
  exact manuscript_binomial_wide_of_jitter p hp n hn hJ k.toNat hk.2 (by rwa [he])


end BerryEsseen
