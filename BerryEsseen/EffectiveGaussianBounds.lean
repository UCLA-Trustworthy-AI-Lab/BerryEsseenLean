import BerryEsseen.ExtremizerSupport
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem exp_neg_one_le_three_eighths : Real.exp (-1 : ℝ) ≤ 3 / 8 := by
  rw [Real.exp_neg]
  apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 3 / 8)).mpr
  norm_num
  linarith [Real.exp_one_gt_d9]

theorem gaussian_monomial_square (k : ℕ) (x : ℝ) :
    |x ^ k * standardNormalDensity x| ^ 2 = phi0 ^ 2 * (x ^ k) ^ 2 * Real.exp (-x ^ 2) := by
  rw [sq_abs, mul_pow, standardNormalDensity_formula, mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-x ^ 2 / 2) = -x ^ 2 by ring]
  ring

theorem gaussian_first_monomial_effective (x : ℝ) : |x * standardNormalDensity x| ≤ 1 / 4 := by
  have hbase : x ^ 2 * Real.exp (-x ^ 2) ≤ 3 / 8 :=
    (Real.mul_exp_neg_le_exp_neg_one (x ^ 2)).trans exp_neg_one_le_three_eighths
  have hp2 : phi0 ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith [phi0_pos, phi0_lt_two_fifths]
  have hm := mul_le_mul hp2 hbase (by positivity : 0 ≤ x ^ 2 * Real.exp (-x ^ 2)) (by norm_num : (0 : ℝ) ≤ 4 / 25)
  have he := gaussian_monomial_square 1 x
  simp only [pow_one] at he
  nlinarith only [hm, he, abs_nonneg (x * standardNormalDensity x)]

theorem gaussian_third_monomial_effective (x : ℝ) : |x ^ 3 * standardNormalDensity x| ≤ 1 / 2 := by
  have hbase : (x ^ 2 / 3) * Real.exp (-(x ^ 2 / 3)) ≤ 3 / 8 :=
    (Real.mul_exp_neg_le_exp_neg_one (x ^ 2 / 3)).trans exp_neg_one_le_three_eighths
  have hcube := pow_le_pow_left₀ (by positivity : 0 ≤ (x ^ 2 / 3) * Real.exp (-(x ^ 2 / 3))) hbase 3
  have he : ((x ^ 2 / 3) * Real.exp (-(x ^ 2 / 3))) ^ 3 =
      (x ^ 3) ^ 2 * Real.exp (-x ^ 2) / 27 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (3 : ℝ) * -(x ^ 2 / 3) = -x ^ 2 by ring]
    ring
  rw [he] at hcube
  have hb : (x ^ 3) ^ 2 * Real.exp (-x ^ 2) ≤ (729 / 512 : ℝ) := by nlinarith only [hcube]
  have hp2 : phi0 ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith [phi0_pos, phi0_lt_two_fifths]
  have hm := mul_le_mul hp2 hb (by positivity : 0 ≤ (x ^ 3) ^ 2 * Real.exp (-x ^ 2)) (by norm_num : (0 : ℝ) ≤ 4 / 25)
  have he := gaussian_monomial_square 3 x
  nlinarith only [hm, he, abs_nonneg (x ^ 3 * standardNormalDensity x)]

theorem gaussian_third_derivative_effective (x : ℝ) :
    |(3 * x - x ^ 3) * standardNormalDensity x| ≤ 5 / 4 := by
  have h := abs_sub (3 * (x * standardNormalDensity x)) (x ^ 3 * standardNormalDensity x)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h
  have he : (3 * x - x ^ 3) * standardNormalDensity x =
      3 * (x * standardNormalDensity x) - x ^ 3 * standardNormalDensity x := by ring
  rw [he]
  linarith [gaussian_first_monomial_effective x, gaussian_third_monomial_effective x]

end BerryEsseen
