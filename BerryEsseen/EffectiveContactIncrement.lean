import BerryEsseen.EffectiveContactSaturation
import BerryEsseen.SupportSeparation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem gaussian_density_effective_local_lower (z : ℝ) (hz : z ^ 2 ≤ 0.01) :
    0.39 ≤ standardNormalDensity z := by
  have he : (0.995 : ℝ) ≤ Real.exp (-z ^ 2 / 2) := by linarith [Real.add_one_le_exp (-z ^ 2 / 2)]
  have hm := mul_le_mul phi0_effective_lower.le he (by norm_num : (0 : ℝ) ≤ 0.995) phi0_pos.le
  rw [standardNormalDensity_formula]
  nlinarith only [hm]

theorem contactEquationRemainder_effective_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1000000 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (y : ℝ) (hy : |y| ≤ 6) :
    |contactEquationRemainder P n t y| ≤ 5 := by
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hR : |signedRatio P n t| ≤ 1 / 2 := by
    rw [hattain, abs_of_pos (cE_pos.trans hv)]
    linarith [(extremalConstant_bounds H (n + 1) (by omega)).1]
  have hr : (1000 : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    have hn' : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [hn']
  have hr0 : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hy2 : y ^ 2 ≤ 36 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at h
    exact h
  have hys : |y ^ 2 - 1| ≤ 37 := abs_le.mpr ⟨by nlinarith [sq_nonneg y], by linarith⟩
  have hfirst : |-(t / Real.sqrt (n + 1 : ℝ) * standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) / 2) * (y ^ 2 - 1)| ≤ 37 / 8 := by
    rw [abs_mul, abs_neg, abs_div]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := mul_le_mul (gaussian_first_monomial_effective (t / Real.sqrt (n + 1 : ℝ))) hys (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [h]
  have hsmall : |signedRatio P n t| / Real.sqrt (n + 1 : ℝ) ≤ 1 / 2000 :=
    (div_le_iff₀ hr0).mpr (by nlinarith only [hR, hr])
  have hsecond : |signedRatio P n t / Real.sqrt (n + 1 : ℝ) *
      (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1))| ≤ 343 / 2000 := by
    rw [abs_mul, abs_div, abs_of_pos hr0]
    have h := mul_le_mul hsmall (contactTailPolynomial_bound P hβ y hy) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2000)
    nlinarith only [h]
  unfold contactEquationRemainder
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans (by norm_num))

theorem sqrt_predecessor_ratio_nine_tenths (n : ℕ) (hn : 1000000 ≤ n) :
    0.9 ≤ Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) := by
  have h := (sqrt_predecessor_ratio_effective n (by omega)).2
  have hN : (10 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (show 10 ≤ n + 1 by omega)
  have hi : 1 / (n + 1 : ℝ) ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) hN
  linarith only [h, hi]

theorem contact_increment_scalar_lower (q φ d e r : ℝ) (hq : q ∈ Icc 0 1)
    (hq0 : 0.9 ≤ q) (hφ : 0.39 ≤ φ) (hd : 0 ≤ d) (he : -10 ≤ e) (hr : 0 < r) :
    d / 3 - 10 / r ≤ q * (φ * d + e / r) := by
  have hprod : 1 / 3 ≤ q * φ := by
    have h := mul_le_mul hq0 hφ (by norm_num : (0 : ℝ) ≤ 0.39) hq.1
    nlinarith only [h]
  have hmain := mul_le_mul_of_nonneg_right hprod hd
  have he' := div_le_div_of_nonneg_right he hr.le
  have her := mul_le_mul_of_nonneg_left he' hq.1
  have hqr := mul_le_mul_of_nonneg_right hq.2 (show 0 ≤ 10 / r by positivity)
  simp only [div_eq_mul_inv] at hmain her hqr ⊢
  nlinarith only [hmain, her, hqr]

theorem extremizer_effective_increment_lower (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1000000 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hz : (t / Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ 0.01)
    (x y : ℝ) (hx : x ∈ P.measure.support) (hy : y ∈ P.measure.support)
    (hxb : |x| ≤ 6) (hyb : |y| ≤ 6) (hxy : x ≤ y) :
    (y - x) / 3 - 10 / Real.sqrt (n + 1 : ℝ) ≤
      Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n) (t - x) - cdf (iidSumLaw P.measure n) (t - y)) := by
  rw [contact_cdf_increment_exact H P n t x y hattain hv hx hy]
  apply contact_increment_scalar_lower _ _ _ _ _ (sqrt_predecessor_ratio_effective n (by omega)).1
    (sqrt_predecessor_ratio_nine_tenths n hn) (gaussian_density_effective_local_lower _ hz)
    (sub_nonneg.mpr hxy) _ (by positivity)
  have h1 := abs_le.mp (contactEquationRemainder_effective_bound H P n hn t hattain hv x hxb)
  have h2 := abs_le.mp (contactEquationRemainder_effective_bound H P n hn t hattain hv y hyb)
  linarith only [h1.1, h2.2]

end BerryEsseen
