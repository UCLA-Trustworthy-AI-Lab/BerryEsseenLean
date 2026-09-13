import BerryEsseen.EffectiveGaussianBounds
import BerryEsseen.EdgeworthDensityFourier

noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem edgeworthDensity_effective_bound (n : ℕ) (hn : 1 ≤ n) (κ : ℝ) (hκ : |κ| ≤ 1.84) (x : ℝ) :
    |edgeworthDensity n κ x| ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hcoef : |κ / (6 * Real.sqrt (n : ℝ))| ≤ (1.84 : ℝ) / 6 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    exact (div_le_div_of_nonneg_right hκ (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1.84) (by norm_num : (0 : ℝ) < 6) (by linarith : 6 ≤ 6 * Real.sqrt (n : ℝ)))
  have hH : |gaussianHermiteThree x| ≤ 5 / 4 := by
    have hh := gaussian_third_derivative_effective x
    simpa only [gaussianHermiteThree, show x ^ 3 - 3 * x = -(3 * x - x ^ 3) by ring,
      neg_mul, abs_neg] using hh
  calc
    _ ≤ |standardNormalDensity x| + |κ / (6 * Real.sqrt (n : ℝ))| * |gaussianHermiteThree x| := by
      simpa only [edgeworthDensity, abs_mul] using abs_add_le (standardNormalDensity x)
        (κ / (6 * Real.sqrt (n : ℝ)) * gaussianHermiteThree x)
    _ ≤ phi0 + ((1.84 : ℝ) / 6) * (5 / 4) := by
      rw [abs_of_pos (standardNormalDensity_pos x)]
      exact add_le_add (standardNormalDensity_le_phi0 x)
        (mul_le_mul hcoef hH (abs_nonneg _) (by norm_num))
    _ ≤ 1 := by linarith [phi0_lt_two_fifths]

end BerryEsseen
