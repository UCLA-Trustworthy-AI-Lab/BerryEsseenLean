import BerryEsseen.EffectiveGlobalJitter
import BerryEsseen.ContactSaturation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem gaussian_second_at_zero_quadratic (z : ℝ) :
    |(z ^ 2 - 1) * standardNormalDensity z + phi0| ≤ (3 / 5) * z ^ 2 := by
  let e := Real.exp (-z ^ 2 / 2)
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  have he2 : 1 - e ≤ z ^ 2 / 2 := by
    have h := Real.add_one_le_exp (-z ^ 2 / 2)
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left he1 (sq_nonneg z)
  have hb : 1 - e + z ^ 2 * e ≤ (3 / 2) * z ^ 2 := by nlinarith only [he2, hmul]
  have hb0 : 0 ≤ 1 - e + z ^ 2 * e := add_nonneg (sub_nonneg.mpr he1) (mul_nonneg (sq_nonneg z) he0.le)
  have hp := mul_le_mul phi0_lt_two_fifths.le hb hb0 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have he : (z ^ 2 - 1) * standardNormalDensity z + phi0 = phi0 * (1 - e + z ^ 2 * e) := by
    rw [standardNormalDensity_formula]
    dsimp [e]
    ring
  rw [he, abs_of_nonneg (mul_nonneg phi0_pos.le hb0)]
  nlinarith only [hp]

theorem gaussianHn_effective_local_remainder (n : ℕ) (hn : 2 ≤ n) (z y : ℝ) (hy : |y| ≤ 6) :
    |gaussianHn n z y - phi0 / 6 * (y ^ 3 - 3 * y)| ≤
      500 / Real.sqrt (n : ℝ) + 24 * z ^ 2 := by
  have hn0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hbase := gaussianHn_uniform_remainder n hn z y 6 hy
  have hC : gaussianRemainderConstant 6 ≤ 500 := by
    unfold gaussianRemainderConstant
    nlinarith only [phi0_lt_two_fifths]
  have hbound := div_le_div_of_nonneg_right hC hn0.le
  have hy3 := pow_le_pow_left₀ (abs_nonneg y) hy 3
  have hcoef : |y / 2 - y ^ 3 / 6| ≤ 39 := by
    have ht := abs_sub (y / 2) (y ^ 3 / 6)
    rw [abs_div, abs_div, abs_pow] at ht
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by norm_num : (0 : ℝ) < 6)] at ht
    nlinarith only [ht, hy, hy3]
  have hdiff : |(z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6) -
      phi0 / 6 * (y ^ 3 - 3 * y)| ≤ 24 * z ^ 2 := by
    have he : (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6) -
        phi0 / 6 * (y ^ 3 - 3 * y) =
        ((z ^ 2 - 1) * standardNormalDensity z + phi0) * (y / 2 - y ^ 3 / 6) := by ring
    rw [he, abs_mul]
    have hm := mul_le_mul (gaussian_second_at_zero_quadratic z) hcoef (abs_nonneg _) (by positivity : 0 ≤ (3 / 5 : ℝ) * z ^ 2)
    nlinarith only [hm, sq_nonneg z]
  have ht := abs_sub_le (gaussianHn n z y)
    ((z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6))
    (phi0 / 6 * (y ^ 3 - 3 * y))
  linarith only [hbase, hbound, hdiff, ht]

end BerryEsseen
