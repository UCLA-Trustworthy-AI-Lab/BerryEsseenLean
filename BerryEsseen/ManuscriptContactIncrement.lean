import BerryEsseen.ManuscriptContactSaturation
import BerryEsseen.EffectiveContactIncrement

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_contact_remainder_difference_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (x y : ℝ) (hx : |x| ≤ 6) (hy : |y| ≤ 6) :
    |contactEquationRemainder P n t x - contactEquationRemainder P n t y| ≤
      4.5 + 341 / Real.sqrt (n + 1 : ℝ) := by
  let r := Real.sqrt (n + 1 : ℝ)
  let z := t / r
  let poly := fun v : ℝ => |v| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * v -
    3 / 2 * thirdMoment P * (v ^ 2 - 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hR : |signedRatio P n t| ≤ 1 / 2 := by
    rw [hattain, abs_of_pos (cE_pos.trans hv)]
    linarith [(extremalConstant_bounds H (n + 1) (by omega)).1]
  have hx2 : x ^ 2 ≤ 36 := by
    have hb := pow_le_pow_left₀ (abs_nonneg x) hx 2
    norm_num [sq_abs] at hb
    exact hb
  have hy2 : y ^ 2 ≤ 36 := by
    have hb := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at hb
    exact hb
  have hdiff : |y ^ 2 - x ^ 2| ≤ 36 := abs_le.mpr ⟨by nlinarith [sq_nonneg y], by nlinarith [sq_nonneg x]⟩
  have hfirst : |z * standardNormalDensity z / 2 * (y ^ 2 - x ^ 2)| ≤ 4.5 := by
    rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hf := div_le_div_of_nonneg_right (gaussian_first_monomial_effective z) (by norm_num : (0 : ℝ) ≤ 2)
    have hb := mul_le_mul hf hdiff (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ (1 / 4) / 2)
    norm_num at hb
    norm_num only [show (4.5 : ℝ) = 9 / 2 by norm_num, abs_mul]
    exact hb
  have hp : |poly x - poly y| ≤ 682 := by
    have htri : |poly x - poly y| ≤ |poly x| + |poly y| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (poly x) 0 (poly y)
    have hpx : |poly x| ≤ 341 := manuscript_contactTailPolynomial_bound P hβ x hx
    have hpy : |poly y| ≤ 341 := manuscript_contactTailPolynomial_bound P hβ y hy
    linarith only [htri, hpx, hpy]
  have hsecond : |signedRatio P n t / r * (poly x - poly y)| ≤ 341 / r := by
    rw [abs_mul, abs_div, abs_of_pos hr]
    have hb := mul_le_mul (div_le_div_of_nonneg_right hR hr.le) hp (abs_nonneg _) (by positivity : 0 ≤ (1 / 2 : ℝ) / r)
    convert hb using 1 <;> ring
  have he : contactEquationRemainder P n t x - contactEquationRemainder P n t y =
      z * standardNormalDensity z / 2 * (y ^ 2 - x ^ 2) + signedRatio P n t / r * (poly x - poly y) := by
    dsimp [contactEquationRemainder, poly, z, r]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem manuscript_contact_increment_error_budget (n : ℕ) (hn : 1000000 ≤ n) :
    4.5 / Real.sqrt (n + 1 : ℝ) + 341 / (n + 1 : ℝ) ≤ 30 / Real.sqrt (n + 1 : ℝ) := by
  have hnR : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
  have hs : (1000 : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := by nlinarith only [hnR, hr2, hr.le]
  have he : 4.5 / Real.sqrt (n + 1 : ℝ) + 341 / (n + 1 : ℝ) =
      (4.5 + 341 / Real.sqrt (n + 1 : ℝ)) / Real.sqrt (n + 1 : ℝ) := by
    nth_rw 2 [← hr2]
    field_simp
    <;> ring
  rw [he]
  apply div_le_div_of_nonneg_right ?_ hr.le
  have hb : 341 / Real.sqrt (n + 1 : ℝ) ≤ 25.5 := (div_le_iff₀ hr).mpr (by nlinarith only [hs])
  linarith only [hb]

theorem manuscript_extremizer_effective_increment_lower (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1000000 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hz : (t / Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ 0.01)
    (x y : ℝ) (hx : x ∈ P.measure.support) (hy : y ∈ P.measure.support)
    (hxb : |x| ≤ 6) (hyb : |y| ≤ 6) (hxy : x ≤ y) :
    (y - x) / 3 - 30 / Real.sqrt (n + 1 : ℝ) ≤
      Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n) (t - x) - cdf (iidSumLaw P.measure n) (t - y)) := by
  let r := Real.sqrt (n + 1 : ℝ)
  let q := Real.sqrt (n : ℝ) / r
  have hr : 0 < r := by dsimp [r]; positivity
  have hr2 : r ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hq := (sqrt_predecessor_ratio_effective n (by omega)).1
  change q ∈ Icc 0 1 at hq
  have hq0 : 0.9 ≤ q := sqrt_predecessor_ratio_nine_tenths n hn
  have hφ := gaussian_density_effective_local_lower _ hz
  have hcoeff : 1 / 3 ≤ q * standardNormalDensity (t / r) := by
    have hb := mul_le_mul hq0 hφ (by norm_num : (0 : ℝ) ≤ 0.39) hq.1
    nlinarith only [hb]
  have hmain := mul_le_mul_of_nonneg_right hcoeff (sub_nonneg.mpr hxy)
  have he := (abs_le.mp (manuscript_contact_remainder_difference_bound H P n t hattain hv x y hxb hyb)).1
  have he' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he hr.le) hq.1
  have hqb := mul_le_mul_of_nonneg_right hq.2 (show 0 ≤ (4.5 + 341 / r) / r by positivity)
  have hbudget := manuscript_contact_increment_error_budget n hn
  have hid : (4.5 + 341 / r) / r = 4.5 / r + 341 / (n + 1 : ℝ) := by rw [← hr2]; field_simp <;> ring
  change 4.5 / r + 341 / (n + 1 : ℝ) ≤ 30 / r at hbudget
  rw [← hid] at hbudget
  rw [contact_cdf_increment_exact H P n t x y hattain hv hx hy]
  change (y - x) / 3 - 30 / r ≤ q * (_ * (y - x) + _ / r)
  simp only [div_eq_mul_inv] at hmain he' hqb hbudget ⊢
  nlinarith only [hmain, he', hqb, hbudget]

end BerryEsseen
