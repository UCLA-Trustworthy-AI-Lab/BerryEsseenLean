import BerryEsseen.GaussianPrimitives
import BerryEsseen.TaylorBounds

/-! Global Gaussian derivative bounds and sharp translation remainders. -/
noncomputable section
open Set
namespace BerryEsseen

theorem standardNormalDensity_pos (x : ℝ) : 0 < standardNormalDensity x := by
  rw [standardNormalDensity_formula]
  exact mul_pos phi0_pos (Real.exp_pos _)

theorem gaussian_polynomial_bound (p x B : ℝ)
    (h : |p| ≤ B * Real.exp (x ^ 2 / 2)) : |p * standardNormalDensity x| ≤ B * phi0 := by
  have hd : |p| / Real.exp (x ^ 2 / 2) ≤ B := (div_le_iff₀ (Real.exp_pos _)).2 h
  have hm := mul_le_mul_of_nonneg_left hd phi0_pos.le
  rw [standardNormalDensity_formula, abs_mul, abs_mul, abs_of_pos phi0_pos,
    abs_of_pos (Real.exp_pos _), show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring, Real.exp_neg]
  convert hm using 1 <;> ring

theorem standardNormalDensity_le_phi0 (x : ℝ) : standardNormalDensity x ≤ phi0 := by
  have h := gaussian_polynomial_bound 1 x 1 (by
    simpa using Real.one_le_exp (by positivity : 0 ≤ x ^ 2 / 2))
  simpa only [one_mul, abs_of_pos (standardNormalDensity_pos x)] using h

/-- The exact bound needed to retain the coefficient phi(0)/6. -/
theorem gaussian_second_derivative_bound (x : ℝ) :
    |(x ^ 2 - 1) * standardNormalDensity x| ≤ phi0 := by
  have hh : |x ^ 2 - 1| ≤ Real.exp (x ^ 2 / 2) := by
    by_cases hx : x ^ 2 ≤ 1
    · rw [abs_of_nonpos (by linarith : x ^ 2 - 1 ≤ 0)]
      nlinarith [Real.one_le_exp (by positivity : 0 ≤ x ^ 2 / 2), sq_nonneg x]
    · rw [abs_of_nonneg (by linarith : 0 ≤ x ^ 2 - 1)]
      nlinarith [Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ x ^ 2 / 2),
        sq_nonneg (x ^ 2 - 2)]
  simpa using gaussian_polynomial_bound (x ^ 2 - 1) x 1 (by simpa using hh)

theorem gaussian_first_monomial_bound (x : ℝ) : |x * standardNormalDensity x| ≤ 3 * phi0 := by
  apply gaussian_polynomial_bound
  have he := Real.add_one_le_exp (x ^ 2 / 2)
  have h1 := Real.one_le_exp (by positivity : 0 ≤ x ^ 2 / 2)
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

theorem gaussian_third_monomial_bound (x : ℝ) : |x ^ 3 * standardNormalDensity x| ≤ 9 * phi0 := by
  apply gaussian_polynomial_bound
  have he := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ x ^ 2 / 2)
  have h1 := Real.one_le_exp (by positivity : 0 ≤ x ^ 2 / 2)
  have hp : |x| ^ 3 ≤ 1 + x ^ 4 := by
    by_cases hx : |x| ≤ 1
    · have h : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
      nlinarith [sq_nonneg (x ^ 2)]
    · have h := mul_nonneg (by linarith : 0 ≤ |x| - 1) (pow_nonneg (abs_nonneg x) 3)
      have h4 : |x| ^ 4 = x ^ 4 := by
        calc |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
             _ = (x ^ 2) ^ 2 := by rw [sq_abs]
             _ = x ^ 4 := by ring
      nlinarith [h4]
  rw [abs_pow]
  nlinarith [sq_nonneg x]

theorem gaussian_third_derivative_bound (x : ℝ) :
    |(3 * x - x ^ 3) * standardNormalDensity x| ≤ 18 * phi0 := by
  calc
    |(3 * x - x ^ 3) * standardNormalDensity x| =
        |3 * (x * standardNormalDensity x) - x ^ 3 * standardNormalDensity x| := by congr 1; ring
    _ ≤ |3 * (x * standardNormalDensity x)| + |x ^ 3 * standardNormalDensity x| := abs_sub _ _
    _ ≤ 18 * phi0 := by
      rw [abs_mul]
      norm_num
      have h1 := gaussian_first_monomial_bound x
      have h3 := gaussian_third_monomial_bound x
      simp only [abs_mul, abs_pow] at h1 h3
      linarith

theorem gaussian_translation_bound (z h : ℝ) :
    |normalCDF (z + h) - normalCDF z - h * standardNormalDensity z +
      h ^ 2 * z * standardNormalDensity z / 2| ≤ phi0 / 6 * |h| ^ 3 := by
  convert taylor_third_global normalCDF standardNormalDensity (fun x => -x * standardNormalDensity x)
    (fun x => (x ^ 2 - 1) * standardNormalDensity x) phi0 normalCDF_hasDerivAt
    standardNormalDensity_hasDerivAt standardNormalDensity_second_hasDerivAt
    gaussian_second_derivative_bound z h using 1
  congr 1
  ring

theorem gaussian_translation_fourth_bound (z h : ℝ) :
    |normalCDF (z + h) - normalCDF z - h * standardNormalDensity z +
      h ^ 2 * z * standardNormalDensity z / 2 -
      h ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6| ≤
        (3 / 4 : ℝ) * phi0 * |h| ^ 4 := by
  convert taylor_fourth_global normalCDF standardNormalDensity (fun x => -x * standardNormalDensity x)
    (fun x => (x ^ 2 - 1) * standardNormalDensity x)
    (fun x => (3 * x - x ^ 3) * standardNormalDensity x) (18 * phi0) normalCDF_hasDerivAt
    standardNormalDensity_hasDerivAt standardNormalDensity_second_hasDerivAt
    standardNormalDensity_third_hasDerivAt gaussian_third_derivative_bound z h using 1
  · congr 1; ring
  · ring

theorem gaussian_x_density_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => t * standardNormalDensity t)
      ((1 - x ^ 2) * standardNormalDensity x) x := by
  convert (standardNormalDensity_second_hasDerivAt x).neg using 1
  · funext t; dsimp; ring
  · ring

theorem gaussian_x_density_lipschitz (x y : ℝ) :
    |y * standardNormalDensity y - x * standardNormalDensity x| ≤ phi0 * |y - x| := by
  have hb (t : ℝ) : ‖(1 - t ^ 2) * standardNormalDensity t‖ ≤ phi0 := by
    rw [Real.norm_eq_abs, show (1 - t ^ 2) * standardNormalDensity t =
      -((t ^ 2 - 1) * standardNormalDensity t) by ring, abs_neg]
    exact gaussian_second_derivative_bound t
  simpa only [Real.norm_eq_abs] using
    convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (gaussian_x_density_hasDerivAt t).hasDerivWithinAt)
      (fun t _ => hb t) (mem_univ x) (mem_univ y)

theorem gaussian_x_density_second_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => (1 - t ^ 2) * standardNormalDensity t)
      ((x ^ 3 - 3 * x) * standardNormalDensity x) x := by
  convert (standardNormalDensity_third_hasDerivAt x).neg using 1
  · funext t; dsimp; ring
  · ring

theorem gaussian_x_density_translation_bound (z h : ℝ) :
    |(z + h) * standardNormalDensity (z + h) - z * standardNormalDensity z -
      h * (1 - z ^ 2) * standardNormalDensity z| ≤ 9 * phi0 * |h| ^ 2 := by
  have hb (x : ℝ) : |(x ^ 3 - 3 * x) * standardNormalDensity x| ≤ 18 * phi0 := by
    rw [show (x ^ 3 - 3 * x) * standardNormalDensity x =
      -((3 * x - x ^ 3) * standardNormalDensity x) by ring, abs_neg]
    exact gaussian_third_derivative_bound x
  convert taylor_second_global (fun x => x * standardNormalDensity x)
    (fun x => (1 - x ^ 2) * standardNormalDensity x)
    (fun x => (x ^ 3 - 3 * x) * standardNormalDensity x) (18 * phi0)
    gaussian_x_density_hasDerivAt gaussian_x_density_second_hasDerivAt hb z h using 1
  · congr 1; ring
  · ring

end BerryEsseen
