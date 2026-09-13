import BerryEsseen.VariationalExtremizer
import BerryEsseen.GaussianCancellation

/-! From the actual variational condition to uniform support bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem raw_signed_cdf_bound (H : ClassicalBerryEsseenBounds) (P : StandardizedLaw)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    cdf (iidSumLaw P.measure n) t - normalCDF (t / Real.sqrt (n : ℝ)) ≤
      extremalConstant n * thirdMoment P / Real.sqrt (n : ℝ) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  have h := normalizedDiscrepancy_le_extremalConstant H P n hn (t / Real.sqrt (n : ℝ))
  unfold normalizedDiscrepancy discrepancy at h
  rw [mul_div_cancel₀ t hs.ne'] at h
  have hb := (div_le_iff₀ (thirdMoment_pos P)).1 h
  apply (le_div_iff₀ hs).2
  rw [cdf_eq_real]
  have ha := le_abs_self ((iidSumLaw P.measure n).real (Iic t) - normalCDF (t / Real.sqrt (n : ℝ)))
  have hm := mul_le_mul_of_nonneg_left ha hs.le
  dsimp [Measure.real] at hm ⊢
  nlinarith

theorem extremizer_thirdMoment_cutoff (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ) (hviol : cE < signedRatio P n t) :
    thirdMoment P < momentCutoff := by
  apply normalized_violation_momentCutoff H P (n + 1) (by omega) (t / Real.sqrt (n + 1 : ℝ))
  rw [← abs_signedRatio_eq_normalized]
  exact hviol.trans_le (le_abs_self _)

theorem gaussian_predecessor_argument (n : ℕ) (hn : 1 ≤ n) (t y : ℝ) :
    (t / Real.sqrt (n + 1 : ℝ) - y / Real.sqrt (n + 1 : ℝ)) /
      Real.sqrt (1 - 1 / Real.sqrt (n + 1 : ℝ) ^ 2) = (t - y) / Real.sqrt (n : ℝ) := by
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have he : 1 - 1 / Real.sqrt (n + 1 : ℝ) ^ 2 = (n : ℝ) / Real.sqrt (n + 1 : ℝ) ^ 2 := by
    field_simp
    nlinarith [hs2]
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hs.le]
  field_simp

theorem sqrt_step_ratio_bound (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n + 1 : ℝ) ^ 3 / Real.sqrt (n : ℝ) ≤ (n + 1 : ℝ) + 1 := by
  have hr : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hs : 1 ≤ Real.sqrt (n + 1 : ℝ) := Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hrp : 0 < Real.sqrt (n : ℝ) := by linarith
  have hsp : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hr2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hprod : 1 ≤ Real.sqrt (n : ℝ) * Real.sqrt (n + 1 : ℝ) := by nlinarith
  apply (div_le_iff₀ hrp).2
  apply (mul_le_mul_iff_right₀ (add_pos hsp hrp)).1
  linear_combination hprod - ((n + 1 : ℝ) + 1) * hr2 +
    (Real.sqrt (n + 1 : ℝ) ^ 2 + Real.sqrt (n : ℝ) * Real.sqrt (n + 1 : ℝ) +
      (n + 1 : ℝ)) * hs2

theorem influenceNumerator_gaussian_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t y : ℝ) :
    influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
      (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
      (signedRatio P n t) y ≤
    gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y +
      thirdMoment P * (Real.sqrt (n + 1 : ℝ) ^ 3 / Real.sqrt (n : ℝ) * extremalConstant n -
        (n + 1 : ℝ) * signedRatio P n t) +
      3 / 2 * signedRatio P n t * thirdMoment P * (y ^ 2 - 1) -
      signedRatio P n t * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y) := by
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hF : cdf (iidSumLaw P.measure (n + 1)) t - normalCDF (t / Real.sqrt (n + 1 : ℝ)) =
      signedRatio P n t * thirdMoment P / Real.sqrt (n + 1 : ℝ) := by
    unfold signedRatio
    field_simp [(thirdMoment_pos P).ne']
  have hG := raw_signed_cdf_bound H P n hn (t - y)
  have hG' := mul_le_mul_of_nonneg_left hG (pow_nonneg hs.le 3)
  unfold influenceNumerator gaussianH
  rw [gaussian_predecessor_argument n hn t y]
  have hF' : Real.sqrt (n + 1 : ℝ) ^ 3 *
      (cdf (iidSumLaw P.measure (n + 1)) t - normalCDF (t / Real.sqrt (n + 1 : ℝ))) =
      (n + 1 : ℝ) * signedRatio P n t * thirdMoment P := by
    rw [hF]
    field_simp
    rw [hs2]
  linear_combination hG' - hF'

theorem phi0_lt_two_fifths : phi0 < 2 / 5 := by
  have hp : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hr : (5 / 2 : ℝ) < Real.sqrt (2 * Real.pi) := by
    nlinarith [Real.pi_gt_d2]
  unfold phi0
  apply (div_lt_iff₀ hp).2
  linarith

theorem extremalConstant_nonneg (H : ClassicalBerryEsseenBounds) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ extremalConstant n :=
  (normalizedDiscrepancy_nonneg rademacher n 0).trans
    (normalizedDiscrepancy_le_extremalConstant H rademacher n hn 0)

theorem predecessor_remainder_bound (H : ClassicalBerryEsseenBounds)
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) :
    Real.sqrt (n + 1 : ℝ) ^ 3 / Real.sqrt (n : ℝ) * extremalConstant n - (n + 1 : ℝ) * R ≤
      (n + 1 : ℝ) * max (extremalConstant n - R) 0 + 0.4690 := by
  have hs := mul_le_mul_of_nonneg_right (sqrt_step_ratio_bound n hn) (extremalConstant_nonneg H n hn)
  have hd := mul_le_mul_of_nonneg_left (le_max_left (extremalConstant n - R) 0)
    (show 0 ≤ (n + 1 : ℝ) by positivity)
  linarith [(extremalConstant_bounds H n hn).1]

theorem influence_cubic_budget (β R M y d : ℝ) (hβ : 0 ≤ β) (hβb : β ≤ 1.84)
    (hR : cE ≤ R) (hRb : R ≤ 0.4690) (hM : |M| ≤ 1) (hd : 0 ≤ d) :
    phi0 / 6 * |y| ^ 3 + 9 * phi0 * (1 + |y|) + β * (d + 0.4690) +
      3 / 2 * R * β * (y ^ 2 - 1) - R * (|y| ^ 3 - β - 3 * M * y) ≤
      -(|y| ^ 3) / 3 + 3 / 2 * y ^ 2 + 6 * |y| + 5 + 2 * d := by
  have hRp : 0 ≤ R := cE_pos.le.trans hR
  have hprod : 0 ≤ R * β := mul_nonneg hRp hβ
  have hprodb : R * β ≤ 1 := by nlinarith
  have hMy : M * y ≤ |y| := by
    calc M * y ≤ |M * y| := le_abs_self _
         _ = |M| * |y| := abs_mul _ _
         _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hM (abs_nonneg y)
         _ = |y| := one_mul _
  have hc : (1 / 3 : ℝ) ≤ R - phi0 / 6 := by
    linarith [cE_numeric_bounds.1, phi0_lt_two_fifths]
  have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg y) 3)
  have hq := mul_le_mul_of_nonneg_right hprodb (sq_nonneg y)
  have hl := mul_le_mul_of_nonneg_left hMy (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hRp)
  have hl' : 9 * phi0 + 3 * R ≤ 6 := by linarith [phi0_lt_two_fifths]
  have hl'' := mul_le_mul_of_nonneg_right hl' (abs_nonneg y)
  have hdb := mul_le_mul_of_nonneg_right hβb hd
  nlinarith [phi0_lt_two_fifths]

/-- An explicit support certificate for the qualitative proof. This is not
the sharper radius 6 asserted in the quantitative appendix. -/
theorem support_cubic_ten (r d : ℝ) (hr : 10 ≤ r) (hd : d ≤ 1) :
    -(r ^ 3) / 3 + 3 / 2 * r ^ 2 + 6 * r + 5 + 2 * d < 0 := by
  have h1 : 0 ≤ r - 10 := by linarith
  have h2 := sq_nonneg (r - 10)
  have h3 := pow_nonneg h1 3
  nlinarith

theorem extremizer_support_subset_ten (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hviol : cE < signedRatio P n t)
    (hdrop : scaledDrop extremalConstant (n + 1) ≤ 1) :
    P.measure.support ⊆ Ioo (-10) 10 := by
  have hRp : 0 ≤ signedRatio P n t := (cE_pos.trans hviol).le
  have hRb : signedRatio P n t ≤ 0.4690 := by
    rw [hattain]
    exact (extremalConstant_bounds H (n + 1) (by omega)).1
  have hβ : thirdMoment P ≤ 1.84 :=
    ((extremizer_thirdMoment_cutoff H P n t hviol).trans momentCutoff_bounds.2).le
  intro y hy
  have hc := influence_contact_at_extremizer H P n t hattain hRp y hy
  have hb := influenceNumerator_gaussian_bound H P n hn t y
  rw [hc] at hb
  have hg := gaussianH_global_bound (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y
    (Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    (by rw [Real.sq_sqrt (by positivity)]; exact_mod_cast (show 2 ≤ n + 1 by omega))
  have hd := predecessor_remainder_bound H n hn (signedRatio P n t)
  have hdeq : (n + 1 : ℝ) * max (extremalConstant n - signedRatio P n t) 0 =
      scaledDrop extremalConstant (n + 1) := by
    simp only [scaledDrop, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hattain]
  rw [hdeq] at hd
  have hd' := mul_le_mul_of_nonneg_left hd (thirdMoment_pos P).le
  have hbudget := influence_cubic_budget (thirdMoment P) (signedRatio P n t)
    (signedSecondMoment P) y (scaledDrop extremalConstant (n + 1))
    (thirdMoment_pos P).le hβ hviol.le hRb (signedSecondMoment_abs_le_one P)
    (scaledDrop_nonneg _ _)
  have hbfinal : 0 ≤ -(|y| ^ 3) / 3 + 3 / 2 * y ^ 2 + 6 * |y| + 5 +
      2 * scaledDrop extremalConstant (n + 1) := by
    linarith [le_abs_self (gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y)]
  have hay : |y| < 10 := by
    by_contra h
    have hf := support_cubic_ten |y| (scaledDrop extremalConstant (n + 1)) (le_of_not_gt h) hdrop
    rw [sq_abs] at hf
    linarith
  exact abs_lt.1 hay

theorem selected_extremizers_eventually_bounded (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : ∀ j, 1 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hviol : ∀ j, cE < signedRatio (P j) (n j) (t j))
    (hdrop : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, (P j).measure.support ⊆ Ioo (-10) 10 := by
  filter_upwards [hdrop.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
  exact extremizer_support_subset_ten H (P j) (n j) (hn j) (t j) (hattain j) (hviol j) hj.le

end BerryEsseen
