import BerryEsseen.EffectiveContactBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem gaussianH_six_bound (n : ℕ) (hn : 1 ≤ n) (z y : ℝ) (hy : |y| ≤ 6) :
    |gaussianH (Real.sqrt (n + 1 : ℝ)) z y| ≤ 17 := by
  have hb := gaussianH_effective_global_bound (Real.sqrt (n + 1 : ℝ)) z y
    (by positivity) (by rw [Real.sq_sqrt (by positivity)]; exact_mod_cast (show 2 ≤ n + 1 by omega))
  have hy3 := pow_le_pow_left₀ (abs_nonneg y) hy 3
  norm_num at hy3
  have hp := mul_le_mul phi0_lt_two_fifths.le hy3 (pow_nonneg (abs_nonneg y) 3) (by norm_num : (0 : ℝ) ≤ 2 / 5)
  nlinarith only [hb, hp, hy]

theorem contactTailPolynomial_bound (P : StandardizedLaw) (hβ : thirdMoment P ≤ 2)
    (y : ℝ) (hy : |y| ≤ 6) :
    |(|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1))| ≤ 343 := by
  have hc := contact_polynomial_coefficient_bound (thirdMoment P) (signedSecondMoment P) y
    (by rwa [abs_of_pos (thirdMoment_pos P)]) (signedSecondMoment_abs_le_one P) hy
  have he : |y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1) =
      -(3 / 2 * thirdMoment P * y ^ 2 - |y| ^ 3 + 3 * signedSecondMoment P * y) + thirdMoment P / 2 := by ring
  rw [he]
  have h := abs_add_le (-(3 / 2 * thirdMoment P * y ^ 2 - |y| ^ 3 + 3 * signedSecondMoment P * y)) (thirdMoment P / 2)
  rw [abs_neg, abs_of_pos (div_pos (thirdMoment_pos P) (by norm_num))] at h
  linarith only [h, hc, hβ]

theorem contactCorrection_effective_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (y : ℝ) (hy : |y| ≤ 6) :
    |contactCorrection P n t y| ≤ 200 := by
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hR : |signedRatio P n t| ≤ 1 / 2 := by
    rw [hattain, abs_of_pos (cE_pos.trans hv)]
    linarith [(extremalConstant_bounds H (n + 1) (by omega)).1]
  have hc := contactTailPolynomial_bound P hβ y hy
  have hmul := mul_le_mul hR hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : contactCorrection P n t y =
      gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y -
      signedRatio P n t * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1)) := by
    unfold contactCorrection
    ring
  rw [he]
  have hb := abs_sub (gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y)
    (signedRatio P n t * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y - 3 / 2 * thirdMoment P * (y ^ 2 - 1)))
  rw [abs_mul] at hb
  linarith only [hb, hmul, gaussianH_six_bound n hn (t / Real.sqrt (n + 1 : ℝ)) y hy]

theorem sqrt_predecessor_ratio_effective (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) ∈ Icc 0 1 ∧
      1 - Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
  have hr := Real.sqrt_nonneg (n : ℝ)
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hn0 : 0 < (n + 1 : ℝ) := by positivity
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs2 := Real.sq_sqrt hn0.le
  have hrs : Real.sqrt (n : ℝ) ≤ Real.sqrt (n + 1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
  refine ⟨⟨by positivity, (div_le_one hs).mpr hrs⟩, ?_⟩
  apply (le_div_iff₀ hn0).mpr
  have hm := mul_le_mul_of_nonneg_left hrs hr
  have hid : (1 - Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ)) * (n + 1 : ℝ) =
      (n + 1 : ℝ) - Real.sqrt (n : ℝ) * Real.sqrt (n + 1 : ℝ) := by
    calc
      _ = (n + 1 : ℝ) - Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) * (n + 1 : ℝ) := by ring
      _ = (n + 1 : ℝ) - Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) ^ 2 := by rw [hs2]
      _ = _ := by field_simp
  rw [hid]
  nlinarith only [hm, hr2]

theorem contact_saturation_scalar (q R c C u : ℝ) (hq : q ∈ Icc 0 1)
    (hu : 0 ≤ u) (hqu : 1 - q ≤ u) (hR : R ∈ Icc 0 1) (hc : c ≤ R) (hC : C ≤ 200) :
    c - 201 * u ≤ q * (R - C * u) := by
  have hm := mul_le_mul hqu hR.2 hR.1 hu
  have hC' := mul_le_mul_of_nonneg_left hC (mul_nonneg hq.1 hu)
  have hq' := mul_le_mul_of_nonneg_right hq.2 hu
  nlinarith only [hm, hC', hq', hc]

theorem contact_previous_discrepancy_effective (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (y : ℝ) (hy : y ∈ P.measure.support) (hyb : |y| ≤ 6) :
    cE * thirdMoment P - 201 / (n + 1 : ℝ) ≤
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
  have h := contact_saturation_scalar (Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ))
    (signedRatio P n t * thirdMoment P) (cE * thirdMoment P) (contactCorrection P n t y) (1 / (n + 1 : ℝ))
    hq.1 (by positivity) hq.2 hR hc ((le_abs_self _).trans (contactCorrection_effective_bound H P n hn t hattain hv y hyb))
  have hex := contact_scaled_cdf_exact H P n hn t hattain hv y hy
  have he : Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n) (t - y) - normalCDF ((t - y) / Real.sqrt (n : ℝ))) =
      Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) * (signedRatio P n t * thirdMoment P - contactCorrection P n t y / (n + 1 : ℝ)) := by
    rw [← hex]
    field_simp
  rw [he]
  convert h using 1 <;> ring

end BerryEsseen
