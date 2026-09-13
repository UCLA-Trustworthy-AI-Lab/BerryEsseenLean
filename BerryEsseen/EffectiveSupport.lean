import BerryEsseen.EffectiveGaussianBounds
import BerryEsseen.ContactAlgebra

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem gaussianScaleSecond_effective_bound (u ell : ℝ) (hell : ell ∈ Icc 0 (1 / 2)) :
    |gaussianScaleSecond u ell| ≤ (5 / 4 : ℝ) := by
  have ha : 0 < 1 - ell := by linarith [hell.2]
  have hb : 1 ≤ 4 * (1 - ell) ^ 2 := by nlinarith [hell.2]
  rw [gaussianScaleSecond, abs_div, abs_of_pos (by positivity : 0 < 4 * (1 - ell) ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 - ell) ^ 2)).2
  have h := gaussian_third_derivative_effective (gaussianScaleArgument u ell)
  have hp := phi0_pos
  nlinarith

theorem gaussian_scale_effective_remainder (u d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    |normalCDF (u / Real.sqrt (1 - d)) - normalCDF u -
      d * u * standardNormalDensity u / 2| ≤ (5 / 8 : ℝ) * d ^ 2 := by
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : d * t ∈ Icc 0 (1 / 2) :=
    ⟨mul_nonneg hd.1 ht.1, (mul_le_mul_of_nonneg_left ht.2 hd.1).trans (by simpa using hd.2)⟩
  have hlt (t : ℝ) (ht : t ∈ Icc 0 1) : d * t < 1 := by linarith [(hmem t ht).2]
  have h₁ (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun v => normalCDF (gaussianScaleArgument u (d * v)))
        (d * gaussianScaleFirst u (d * t)) t := by
    convert (gaussianScale_hasDerivAt u (d * t) (hlt t ht)).comp t
      ((hasDerivAt_id t).const_mul d) using 1 <;> (dsimp; ring)
  have h₂ (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun v => d * gaussianScaleFirst u (d * v))
        (d ^ 2 * gaussianScaleSecond u (d * t)) t := by
    convert ((gaussianScaleFirst_hasDerivAt u (d * t) (hlt t ht)).comp t
      ((hasDerivAt_id t).const_mul d)).const_mul d using 1 <;> (dsimp; ring)
  have hb (t : ℝ) (ht : t ∈ Icc 0 1) :
      |d ^ 2 * gaussianScaleSecond u (d * t)| ≤ d ^ 2 * ((5 / 4 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
    exact mul_le_mul_of_nonneg_left (gaussianScaleSecond_effective_bound u (d * t) (hmem t ht)) (sq_nonneg d)
  have h := taylor_second_abs _ _ _ (d ^ 2 * ((5 / 4 : ℝ))) h₁ h₂ hb
  simp only [mul_one, mul_zero, gaussianScaleArgument, sub_zero, Real.sqrt_one, div_one,
    gaussianScaleFirst] at h
  convert h using 1
  · congr 1; ring
  · ring

theorem gaussianScalePart_effective_bound (s z y : ℝ) (hs : 0 < s) (hs2 : 2 ≤ s ^ 2) :
    |gaussianScalePart s z y| ≤ (5 / 8 : ℝ) / s := by
  have hd : (1 / s ^ 2 : ℝ) ∈ Icc 0 (1 / 2) :=
    ⟨by positivity, (div_le_iff₀ (sq_pos_of_pos hs)).2 (by linarith)⟩
  have hb := mul_le_mul_of_nonneg_left (gaussian_scale_effective_remainder (z - y / s) (1 / s ^ 2) hd)
    (pow_nonneg hs.le 3)
  rw [gaussianScalePart, abs_mul, abs_of_pos (pow_pos hs 3)]
  convert hb using 1
  field_simp <;> ring


theorem gaussianH_effective_global_bound (s z y : ℝ) (hs : 0 < s) (hs2 : 2 ≤ s ^ 2) :
    |gaussianH s z y| ≤ phi0 / 6 * |y| ^ 3 + |y| / 5 + 1 / 2 := by
  rw [gaussianH_decomposition s z y hs.ne']
  have hb := (abs_add_three (gaussianTranslationPart s z y) (gaussianScalePart s z y)
    (gaussianDensityPart s z y)).trans
    (add_le_add (add_le_add (gaussianTranslationPart_bound s z y hs)
      (gaussianScalePart_effective_bound s z y hs hs2)) (gaussianDensityPart_bound s z y hs))
  have hsf : (5 / 4 : ℝ) ≤ s := by nlinarith
  have hscale : (5 / 8 : ℝ) / s ≤ 1 / 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hden : phi0 / 2 * |y| ≤ |y| / 5 := by
    nlinarith [mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le (abs_nonneg y)]
  linarith

theorem influence_effective_cubic_budget (β R M y d : ℝ) (hβ : 0 ≤ β) (hβb : β ≤ 1.84)
    (hR : cE ≤ R) (hRb : R ≤ 0.4690) (hM : |M| ≤ 1) (hd : 0 ≤ d) :
    phi0 / 6 * |y| ^ 3 + |y| / 5 + 1 / 2 + β * (d + 0.4690) +
      3 / 2 * R * β * (y ^ 2 - 1) - R * (|y| ^ 3 - β - 3 * M * y) ≤
      -(|y| ^ 3) / 3 + 3 / 2 * y ^ 2 + 17 * |y| / 10 + 3 / 2 + 2 * d := by
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
  have hl' : (1 / 5 : ℝ) + 3 * R ≤ 17 / 10 := by linarith [phi0_lt_two_fifths]
  have hl'' := mul_le_mul_of_nonneg_right hl' (abs_nonneg y)
  have hdb := mul_le_mul_of_nonneg_right hβb hd
  nlinarith [phi0_lt_two_fifths]

theorem extremizer_support_subset_six (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hviol : cE < signedRatio P n t)
    (hdrop : scaledDrop extremalConstant (n + 1) ≤ 1) :
    P.measure.support ⊆ Ioo (-6) 6 := by
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
  have hg := gaussianH_effective_global_bound (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y
    (by positivity)
    (by rw [Real.sq_sqrt (by positivity)]; exact_mod_cast (show 2 ≤ n + 1 by omega))
  have hd := predecessor_remainder_bound H n hn (signedRatio P n t)
  have hdeq : (n + 1 : ℝ) * max (extremalConstant n - signedRatio P n t) 0 =
      scaledDrop extremalConstant (n + 1) := by
    simp only [scaledDrop, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hattain]
  rw [hdeq] at hd
  have hd' := mul_le_mul_of_nonneg_left hd (thirdMoment_pos P).le
  have hbudget := influence_effective_cubic_budget (thirdMoment P) (signedRatio P n t)
    (signedSecondMoment P) y (scaledDrop extremalConstant (n + 1))
    (thirdMoment_pos P).le hβ hviol.le hRb (signedSecondMoment_abs_le_one P)
    (scaledDrop_nonneg _ _)
  have hbfinal : 0 ≤ -(|y| ^ 3) / 3 + 3 / 2 * y ^ 2 + 17 * |y| / 10 + 3 / 2 +
      2 * scaledDrop extremalConstant (n + 1) := by
    linarith [le_abs_self (gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y)]
  have hay : |y| < 6 := by
    by_contra h
    have hf := effective_support_cubic_negative |y| (scaledDrop extremalConstant (n + 1)) (le_of_not_gt h) hdrop
    rw [sq_abs] at hf
    linarith
  exact abs_lt.1 hay


end BerryEsseen
