import BerryEsseen.EffectiveGaussianBounds
import BerryEsseen.GaussianCancellation

/-! Exact numerical steps in the manuscript's equation
`eq:effective-H-local`.  The translation, scale and density errors are
67.5/s, 0.625/s and 11.25/s, and the last replacement costs 78 z². -/
noncomputable section
open Set
namespace BerryEsseen

theorem manuscript_gaussian_translation_fourth_bound (z h : ℝ) :
    |normalCDF (z + h) - normalCDF z - h * standardNormalDensity z +
      h ^ 2 * z * standardNormalDensity z / 2 -
      h ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6| ≤
        (5 / 96 : ℝ) * |h| ^ 4 := by
  convert taylor_fourth_global normalCDF standardNormalDensity (fun x => -x * standardNormalDensity x)
    (fun x => (x ^ 2 - 1) * standardNormalDensity x)
    (fun x => (3 * x - x ^ 3) * standardNormalDensity x) (5 / 4) normalCDF_hasDerivAt
    standardNormalDensity_hasDerivAt standardNormalDensity_second_hasDerivAt
    standardNormalDensity_third_hasDerivAt gaussian_third_derivative_effective z h using 1
  · congr 1; ring
  · ring

theorem manuscript_gaussian_translation_remainder (s z y : ℝ) (hs : 0 < s)
    (hy : |y| ≤ 6) :
    |gaussianTranslationPart s z y + y ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6| ≤
      67.5 / s := by
  have hb := mul_le_mul_of_nonneg_left (manuscript_gaussian_translation_fourth_bound z (-y / s))
    (pow_nonneg hs.le 3)
  rw [← abs_of_pos (pow_pos hs 3), ← abs_mul] at hb
  have he : s ^ 3 * (normalCDF (z + -y / s) - normalCDF z -
      (-y / s) * standardNormalDensity z + (-y / s) ^ 2 * z * standardNormalDensity z / 2 -
      (-y / s) ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6) =
      gaussianTranslationPart s z y + y ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6 := by
    unfold gaussianTranslationPart
    rw [show z + -y / s = z - y / s by ring]
    field_simp <;> ring
  rw [he, abs_of_pos (pow_pos hs 3)] at hb
  have hright : s ^ 3 * ((5 / 96 : ℝ) * |-y / s| ^ 4) =
      (5 / 96 : ℝ) * |y| ^ 4 / s := by
    rw [abs_div, abs_neg, abs_of_pos hs]
    field_simp <;> ring
  rw [hright] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ hs.le
  have h4 := pow_le_pow_left₀ (abs_nonneg y) hy 4
  norm_num at h4 ⊢
  linarith

theorem manuscript_gaussianScaleSecond_bound (u ell : ℝ) (hell : ell ∈ Icc 0 (1 / 2)) :
    |gaussianScaleSecond u ell| ≤ 5 / 4 := by
  have ha : 0 < 1 - ell := by linarith [hell.2]
  have hb : 1 ≤ 4 * (1 - ell) ^ 2 := by nlinarith [hell.2]
  rw [gaussianScaleSecond, abs_div, abs_of_pos (by positivity : 0 < 4 * (1 - ell) ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 - ell) ^ 2)).2
  have h := gaussian_third_derivative_effective (gaussianScaleArgument u ell)
  nlinarith

theorem manuscript_gaussian_scale_remainder (u d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
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
      |d ^ 2 * gaussianScaleSecond u (d * t)| ≤ d ^ 2 * (5 / 4) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
    exact mul_le_mul_of_nonneg_left (manuscript_gaussianScaleSecond_bound u (d * t) (hmem t ht)) (sq_nonneg d)
  have h := taylor_second_abs _ _ _ (d ^ 2 * (5 / 4)) h₁ h₂ hb
  simp only [mul_one, mul_zero, gaussianScaleArgument, sub_zero, Real.sqrt_one, div_one,
    gaussianScaleFirst] at h
  convert h using 1
  · congr 1; ring
  · ring

theorem manuscript_gaussian_scale_part_bound (s z y : ℝ) (hs : 0 < s) (hs2 : 2 ≤ s ^ 2) :
    |gaussianScalePart s z y| ≤ 0.625 / s := by
  have hd : (1 / s ^ 2 : ℝ) ∈ Icc 0 (1 / 2) :=
    ⟨by positivity, (div_le_iff₀ (sq_pos_of_pos hs)).2 (by linarith)⟩
  have hb := mul_le_mul_of_nonneg_left (manuscript_gaussian_scale_remainder (z - y / s) (1 / s ^ 2) hd)
    (pow_nonneg hs.le 3)
  rw [gaussianScalePart, abs_mul, abs_of_pos (pow_pos hs 3)]
  convert hb using 1
  field_simp <;> ring

theorem manuscript_gaussian_x_density_translation_bound (z h : ℝ) :
    |(z + h) * standardNormalDensity (z + h) - z * standardNormalDensity z -
      h * (1 - z ^ 2) * standardNormalDensity z| ≤ (5 / 8 : ℝ) * |h| ^ 2 := by
  have hb (x : ℝ) : |(x ^ 3 - 3 * x) * standardNormalDensity x| ≤ 5 / 4 := by
    rw [show (x ^ 3 - 3 * x) * standardNormalDensity x =
      -((3 * x - x ^ 3) * standardNormalDensity x) by ring, abs_neg]
    exact gaussian_third_derivative_effective x
  convert taylor_second_global (fun x => x * standardNormalDensity x)
    (fun x => (1 - x ^ 2) * standardNormalDensity x)
    (fun x => (x ^ 3 - 3 * x) * standardNormalDensity x) (5 / 4)
    gaussian_x_density_hasDerivAt gaussian_x_density_second_hasDerivAt hb z h using 1
  · congr 1; ring
  · ring

theorem manuscript_gaussian_density_remainder (s z y : ℝ) (hs : 0 < s) (hy : |y| ≤ 6) :
    |gaussianDensityPart s z y - y * (z ^ 2 - 1) * standardNormalDensity z / 2| ≤
      11.25 / s := by
  have hb := mul_le_mul_of_nonneg_left (manuscript_gaussian_x_density_translation_bound z (-y / s))
    (by positivity : 0 ≤ s / 2)
  rw [← abs_of_pos (by positivity : 0 < s / 2), ← abs_mul] at hb
  have he : s / 2 * ((z + -y / s) * standardNormalDensity (z + -y / s) -
      z * standardNormalDensity z - (-y / s) * (1 - z ^ 2) * standardNormalDensity z) =
      gaussianDensityPart s z y - y * (z ^ 2 - 1) * standardNormalDensity z / 2 := by
    unfold gaussianDensityPart
    rw [show z + -y / s = z - y / s by ring]
    field_simp <;> ring
  rw [he, abs_of_pos (by positivity : 0 < s / 2)] at hb
  have hr : s / 2 * ((5 / 8 : ℝ) * |-y / s| ^ 2) = (5 / 16 : ℝ) * |y| ^ 2 / s := by
    rw [abs_div, abs_neg, abs_of_pos hs]
    field_simp <;> ring
  rw [hr] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ hs.le
  have h2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  norm_num at h2 ⊢
  linarith

theorem manuscript_gaussian_fourth_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => (3 * t - t ^ 3) * standardNormalDensity t)
      ((x ^ 4 - 6 * x ^ 2 + 3) * standardNormalDensity x) x := by
  convert (((hasDerivAt_id x).const_mul 3).sub ((hasDerivAt_id x).pow 3)).mul
    (standardNormalDensity_hasDerivAt x) using 1
  dsimp; ring

theorem manuscript_gaussian_fourth_bound (x : ℝ) :
    |(x ^ 4 - 6 * x ^ 2 + 3) * standardNormalDensity x| ≤
      phi0 * (16 * Real.exp (-2) + 12 * Real.exp (-1) + 3) := by
  have htwo := Real.mul_exp_neg_le_exp_neg_one (x ^ 2 / 2)
  rw [show -(x ^ 2 / 2) = -x ^ 2 / 2 by ring] at htwo
  have hfour := pow_le_pow_left₀
    (by positivity : 0 ≤ (x ^ 2 / 4) * Real.exp (-(x ^ 2 / 4)))
    (Real.mul_exp_neg_le_exp_neg_one (x ^ 2 / 4)) 2
  have he : ((x ^ 2 / 4) * Real.exp (-(x ^ 2 / 4))) ^ 2 =
      x ^ 4 * Real.exp (-x ^ 2 / 2) / 16 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * -(x ^ 2 / 4) = -x ^ 2 / 2 by ring]
    ring
  have he' : Real.exp (-1 : ℝ) ^ 2 = Real.exp (-2) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [he, he'] at hfour
  have h0 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hab : |x ^ 4 - 6 * x ^ 2 + 3| ≤ x ^ 4 + 6 * x ^ 2 + 3 := by
    have h := (abs_add_le (x ^ 4 - 6 * x ^ 2) 3).trans (add_le_add (abs_sub (x ^ 4) (6 * x ^ 2)) le_rfl)
    simpa only [abs_of_nonneg (by positivity : 0 ≤ x ^ 4), abs_of_nonneg (by positivity : 0 ≤ 6 * x ^ 2), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] using h
  have hm := mul_le_mul_of_nonneg_right hab (Real.exp_pos (-x ^ 2 / 2)).le
  have hb : |x ^ 4 - 6 * x ^ 2 + 3| * Real.exp (-x ^ 2 / 2) ≤
      16 * Real.exp (-2) + 12 * Real.exp (-1) + 3 := by
    have htwo' : x ^ 2 * Real.exp (-x ^ 2 / 2) ≤ 2 * Real.exp (-1) := by
      nlinarith only [htwo]
    nlinarith only [hm, hfour, htwo', h0]
  rw [abs_mul, abs_of_pos (standardNormalDensity_pos x), standardNormalDensity_formula]
  nlinarith only [mul_le_mul_of_nonneg_left hb phi0_pos.le]

theorem manuscript_gaussian_fourth_constant_lt_four :
    phi0 * (16 * Real.exp (-2) + 12 * Real.exp (-1) + 3) < 4 := by
  have he : Real.exp (-2 : ℝ) ≤ 9 / 64 := by
    have h := pow_le_pow_left₀ (Real.exp_pos (-1 : ℝ)).le exp_neg_one_le_three_eighths 2
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  have hsum : 16 * Real.exp (-2 : ℝ) + 12 * Real.exp (-1) + 3 ≤ 39 / 4 := by
    linarith [exp_neg_one_le_three_eighths]
  have hm := mul_le_mul_of_nonneg_left hsum phi0_pos.le
  nlinarith only [hm, phi0_lt_two_fifths]

theorem manuscript_gaussian_second_at_zero (z : ℝ) :
    |(z ^ 2 - 1) * standardNormalDensity z + phi0| ≤ 2 * z ^ 2 := by
  have hb (x : ℝ) : |(x ^ 4 - 6 * x ^ 2 + 3) * standardNormalDensity x| ≤ 4 :=
    (manuscript_gaussian_fourth_bound x).trans manuscript_gaussian_fourth_constant_lt_four.le
  have h := taylor_second_global (fun x => (x ^ 2 - 1) * standardNormalDensity x)
    (fun x => (3 * x - x ^ 3) * standardNormalDensity x)
    (fun x => (x ^ 4 - 6 * x ^ 2 + 3) * standardNormalDensity x) 4
    standardNormalDensity_third_hasDerivAt manuscript_gaussian_fourth_hasDerivAt hb 0 z
  norm_num only [zero_add, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_pow (by norm_num : (3 : ℕ) ≠ 0),
    zero_sub, neg_one_mul, standardNormalDensity_zero, mul_zero, sub_self, zero_mul, sub_zero,
    sub_neg_eq_add, sq_abs] at h ⊢
  exact h

theorem manuscript_gaussian_limit_replacement (z y : ℝ) (hy : |y| ≤ 6) :
    |(z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6) -
      phi0 / 6 * (y ^ 3 - 3 * y)| ≤ 78 * z ^ 2 := by
  have hcoef : |y / 2 - y ^ 3 / 6| ≤ 39 := by
    convert gaussian_limit_polynomial_bound y 6 hy using 1 <;> norm_num
  have he : (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6) -
      phi0 / 6 * (y ^ 3 - 3 * y) =
      ((z ^ 2 - 1) * standardNormalDensity z + phi0) * (y / 2 - y ^ 3 / 6) := by ring
  rw [he, abs_mul]
  have hm := mul_le_mul (manuscript_gaussian_second_at_zero z) hcoef (abs_nonneg _)
    (by positivity : 0 ≤ 2 * z ^ 2)
  linarith only [hm]

theorem manuscript_gaussianHn_effective_local_remainder (n : ℕ) (hn : 2 ≤ n)
    (z y : ℝ) (hy : |y| ≤ 6) :
    |gaussianHn n z y - phi0 / 6 * (y ^ 3 - 3 * y)| ≤
      100 * (z ^ 2 + 1 / Real.sqrt (n : ℝ)) := by
  let s := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hs2 : 2 ≤ s ^ 2 := by
    dsimp only [s]
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    exact_mod_cast hn
  have ht := manuscript_gaussian_translation_remainder s z y hs hy
  have hsc := manuscript_gaussian_scale_part_bound s z y hs hs2
  have hd := manuscript_gaussian_density_remainder s z y hs hy
  have he : gaussianH s z y - (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6) =
      (gaussianTranslationPart s z y + y ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6) +
      gaussianScalePart s z y +
      (gaussianDensityPart s z y - y * (z ^ 2 - 1) * standardNormalDensity z / 2) := by
    rw [gaussianH_decomposition s z y hs.ne']
    ring
  have hsum := (abs_add_three _ _ _).trans (add_le_add (add_le_add ht hsc) hd)
  rw [← he] at hsum
  have hfinal := (abs_sub_le (gaussianH s z y)
    ((z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6))
    (phi0 / 6 * (y ^ 3 - 3 * y))).trans
      (add_le_add hsum (manuscript_gaussian_limit_replacement z y hy))
  change |gaussianH s z y - _| ≤ 100 * (z ^ 2 + 1 / s)
  simp only [div_eq_mul_inv] at hfinal ⊢
  nlinarith only [hfinal, sq_nonneg z, inv_nonneg.mpr hs.le]

end BerryEsseen
