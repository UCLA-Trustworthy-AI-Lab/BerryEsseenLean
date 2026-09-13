import BerryEsseen.ManuscriptEffectiveContact
import BerryEsseen.EffectiveContactSaturation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_contactTailPolynomial_bound (P : StandardizedLaw) (hβ : thirdMoment P ≤ 2)
    (y : ℝ) (hy : |y| ≤ 6) :
    |(|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1))| ≤ 341 := by
  have hy2 : y ^ 2 ≤ 36 := by nlinarith [pow_le_pow_left₀ (abs_nonneg y) hy 2, sq_abs y]
  have hy3 : |y| ^ 3 ≤ 216 := by convert pow_le_pow_left₀ (abs_nonneg y) hy 3 using 1 <;> norm_num
  have hys : |y ^ 2 - 1| ≤ 35 := abs_le.mpr ⟨by nlinarith [sq_nonneg y], by linarith⟩
  have hlin : |3 * signedSecondMoment P * y| ≤ 18 := by
    rw [abs_mul, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h := mul_le_mul (signedSecondMoment_abs_le_one P) hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h]
  have hquad : |3 / 2 * thirdMoment P * (y ^ 2 - 1)| ≤ 105 := by
    rw [abs_mul, abs_mul, abs_of_pos (thirdMoment_pos P)]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have h := mul_le_mul hβ hys (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h]
  have h1 := abs_sub (|y| ^ 3) (thirdMoment P)
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg y) 3), abs_of_pos (thirdMoment_pos P)] at h1
  have h2 := abs_sub (|y| ^ 3 - thirdMoment P) (3 * signedSecondMoment P * y)
  have h3 := abs_sub (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y)
    (3 / 2 * thirdMoment P * (y ^ 2 - 1))
  linarith only [hy3, hβ, hlin, hquad, h1, h2, h3]

theorem manuscript_gaussianH_six_bound (n : ℕ) (hN : appendixNConf ≤ n) (z y : ℝ)
    (hz : z ^ 2 ≤ Real.exp (-5 * appendixA)) (hy : |y| ≤ 6) :
    |gaussianHn n z y| < 17 := by
  have hn := (appendix_sample_size_bounds n (appendix_conf_sample_size n hN).1).1
  have hroot := effective_binomial_root_lower n hn
  have hr : 0 < Real.sqrt (n : ℝ) := by norm_num at hroot; linarith
  have hsmall : 1 / Real.sqrt (n : ℝ) ≤ 1 / (10 : ℝ) ^ 12 :=
    one_div_le_one_div_of_le (by positivity) (by norm_num at hroot ⊢; linarith)
  have hz' : z ^ 2 ≤ 1 / (10 : ℝ) ^ 12 := hz.trans
    ((Real.exp_le_exp.mpr (by norm_num [appendixA] : -5 * appendixA ≤ -appendixA)).trans appendix_noise_and_cutoff_bounds.1)
  have h := manuscript_gaussianHn_effective_local_remainder n (by omega) z y hy
  have hpoly : |phi0 / 6 * (y ^ 3 - 3 * y)| ≤ 15.6 := by
    rw [abs_mul, abs_of_pos (div_pos phi0_pos (by norm_num))]
    have ha := abs_sub (y ^ 3) (3 * y)
    rw [abs_pow, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ha
    have hy3 := pow_le_pow_left₀ (abs_nonneg y) hy 3
    have hp := mul_le_mul_of_nonneg_left (show |y ^ 3 - 3 * y| ≤ 234 by nlinarith only [ha, hy3, hy]) (div_pos phi0_pos (by norm_num : (0 : ℝ) < 6)).le
    nlinarith only [hp, phi0_lt_two_fifths]
  have ht := abs_sub_le (gaussianHn n z y) (phi0 / 6 * (y ^ 3 - 3 * y)) 0
  simp only [sub_zero] at ht
  linarith only [h, ht, hpoly, hz', hsmall]

theorem manuscript_contactCorrection_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hN : appendixNConf ≤ n + 1) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hz : (t / Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ Real.exp (-5 * appendixA))
    (y : ℝ) (hy : |y| ≤ 6) : |contactCorrection P n t y| ≤ 187.5 := by
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hR : |signedRatio P n t| ≤ 1 / 2 := by
    rw [hattain, abs_of_pos (cE_pos.trans hv)]
    linarith [(extremalConstant_bounds H (n + 1) (by omega)).1]
  have hc := manuscript_contactTailPolynomial_bound P hβ y hy
  have hmul := mul_le_mul hR hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : contactCorrection P n t y =
      gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y -
      signedRatio P n t * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1)) := by
    unfold contactCorrection; ring
  rw [he]
  have hg := manuscript_gaussianH_six_bound (n + 1) hN (t / Real.sqrt (n + 1 : ℝ)) y hz hy
  simp only [gaussianHn, Nat.cast_add, Nat.cast_one] at hg
  have hb := abs_sub (gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y)
    (signedRatio P n t * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1)))
  rw [abs_mul] at hb
  linarith only [hb, hmul, hg]

theorem manuscript_contact_saturation_scalar (q R c C u : ℝ) (hq : q ∈ Icc 0 1)
    (hu : 0 ≤ u) (hqu : 1 - q ≤ u) (hR : R ∈ Icc 0 1) (hc : c ≤ R) (hC : C ≤ 187.5) :
    c - 200 * u ≤ q * (R - C * u) := by
  have hm := mul_le_mul hqu hR.2 hR.1 hu
  have hC' := mul_le_mul_of_nonneg_left hC (mul_nonneg hq.1 hu)
  have hq' := mul_le_mul_of_nonneg_right hq.2 hu
  nlinarith only [hm, hC', hq', hc, hu]

theorem manuscript_contact_previous_discrepancy (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (hN : appendixNConf ≤ n + 1) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hz : (t / Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ Real.exp (-5 * appendixA))
    (y : ℝ) (hy : y ∈ P.measure.support) (hyb : |y| ≤ 6) :
    cE * thirdMoment P - 200 / (n + 1 : ℝ) ≤
      Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n) (t - y) - normalCDF ((t - y) / Real.sqrt (n : ℝ))) := by
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hR0 : 0 ≤ signedRatio P n t := by rw [hattain]; exact (cE_pos.trans hv).le
  have hRb : signedRatio P n t ≤ 1 / 2 := by rw [hattain]; linarith [(extremalConstant_bounds H (n + 1) (by omega)).1]
  have hR : signedRatio P n t * thirdMoment P ∈ Icc 0 1 :=
    ⟨mul_nonneg hR0 (thirdMoment_pos P).le, by nlinarith [mul_le_mul hRb hβ (thirdMoment_pos P).le (by norm_num : (0 : ℝ) ≤ 1 / 2)]⟩
  have hc : cE * thirdMoment P ≤ signedRatio P n t * thirdMoment P := by
    rw [hattain]
    exact mul_le_mul_of_nonneg_right hv.le (thirdMoment_pos P).le
  have hq := sqrt_predecessor_ratio_effective n hn
  have h := manuscript_contact_saturation_scalar (Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ))
    (signedRatio P n t * thirdMoment P) (cE * thirdMoment P) (contactCorrection P n t y) (1 / (n + 1 : ℝ))
    hq.1 (by positivity) hq.2 hR hc ((le_abs_self _).trans (manuscript_contactCorrection_bound H P n hN t hattain hv hz y hyb))
  have hex := contact_scaled_cdf_exact H P n hn t hattain hv y hy
  have he : Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n) (t - y) - normalCDF ((t - y) / Real.sqrt (n : ℝ))) =
      Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) * (signedRatio P n t * thirdMoment P - contactCorrection P n t y / (n + 1 : ℝ)) := by
    rw [← hex]
    field_simp
  rw [he]
  convert h using 1 <;> ring

end BerryEsseen
