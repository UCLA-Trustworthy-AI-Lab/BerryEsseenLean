import BerryEsseen.CharacteristicTaylor
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

def projectedUnitExp (w : ℂ) (k : ℕ) (t : ℝ) : ℝ :=
  (w * Complex.I ^ k * Complex.exp ((t : ℂ) * Complex.I)).re

theorem projectedUnitExp_hasDerivAt (w : ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (projectedUnitExp w k) (projectedUnitExp w (k + 1) t) t := by
  have h := (((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).mul_const Complex.I)).const_mul (w * Complex.I ^ k)).real_of_complex
  convert h using 1
  unfold projectedUnitExp
  congr 1
  simp only [one_mul, pow_succ]
  ring

theorem projectedUnitExp_abs_le (w : ℂ) (k : ℕ) (t : ℝ) : |projectedUnitExp w k t| ≤ ‖w‖ := by
  have h := Complex.abs_re_le_norm (w * Complex.I ^ k * Complex.exp ((t : ℂ) * Complex.I))
  simpa only [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_exp_ofReal_mul_I] using h

theorem projected_cubic_remainder_bound (w : ℂ) (y : ℝ) :
    |(w * charCubicRemainder y).re| ≤ ‖w‖ * |y| ^ 4 / 24 := by
  have h := taylor_fourth_global (projectedUnitExp w 0) (projectedUnitExp w 1) (projectedUnitExp w 2)
    (projectedUnitExp w 3) (projectedUnitExp w 4) ‖w‖
    (projectedUnitExp_hasDerivAt w 0) (projectedUnitExp_hasDerivAt w 1)
    (projectedUnitExp_hasDerivAt w 2) (projectedUnitExp_hasDerivAt w 3)
    (projectedUnitExp_abs_le w 4) 0 y
  convert h using 1
  · congr 1
    simp only [projectedUnitExp, charCubicRemainder, zero_add, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      pow_zero, mul_one, pow_one]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_sq, pow_succ]
    ring
  · ring

theorem charCubicRemainder_sharp_fourth_bound (y : ℝ) :
    ‖charCubicRemainder y‖ ≤ |y| ^ 4 / 24 := by
  let z := charCubicRemainder y
  have h := projected_cubic_remainder_bound (conj z) y
  change |(conj z * z).re| ≤ ‖conj z‖ * |y| ^ 4 / 24 at h
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _), Complex.norm_conj] at h
  have hr := norm_nonneg z
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ ≤ _
    rw [hz]
    positivity
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne hr (Ne.symm hz)
    nlinarith


theorem projected_linear_remainder_bound (w : ℂ) (y : ℝ) :
    |(w * (Complex.exp ((y : ℂ) * Complex.I) - 1 - (y : ℂ) * Complex.I)).re| ≤ ‖w‖ * y ^ 2 / 2 := by
  have h := taylor_second_global (projectedUnitExp w 0) (projectedUnitExp w 1) (projectedUnitExp w 2) ‖w‖
    (projectedUnitExp_hasDerivAt w 0) (projectedUnitExp_hasDerivAt w 1) (projectedUnitExp_abs_le w 2) 0 y
  convert h using 1
  · congr 1
    simp [projectedUnitExp, Complex.mul_re, Complex.mul_im, pow_succ]
    ring
  · rw [sq_abs]
    ring

theorem unitExp_linear_remainder_sharp (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I) - 1 - (y : ℂ) * Complex.I‖ ≤ y ^ 2 / 2 := by
  let z := Complex.exp ((y : ℂ) * Complex.I) - 1 - (y : ℂ) * Complex.I
  have h := projected_linear_remainder_bound (conj z) y
  change |(conj z * z).re| ≤ ‖conj z‖ * y ^ 2 / 2 at h
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (sq_nonneg _), Complex.norm_conj] at h
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ ≤ _
    rw [hz]
    positivity
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    nlinarith

theorem charFun_cubic_sharp_fourth_bound (P : StandardizedLaw) (u : ℝ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) P.measure) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤
      (∫ x, |x| ^ 4 ∂P.measure) / 24 * |u| ^ 4 := by
  rw [charFun_cubic_remainder_identity]
  calc
    _ ≤ ∫ x, ‖charCubicRemainder (u * x)‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|u| ^ 4 / 24) * |x| ^ 4 ∂P.measure := by
      apply integral_mono (integrable_charCubicRemainder P u).norm (h4.const_mul _)
      intro x
      simpa only [abs_mul, mul_pow, div_mul_eq_mul_div] using charCubicRemainder_sharp_fourth_bound (u * x)
    _ = _ := by rw [integral_const_mul]; ring

theorem effective_charFun_cubic_bound (P : StandardizedLaw) (hβ : thirdMoment P ≤ 1.84)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) (u : ℝ) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤ (0.46 : ℝ) * |u| ^ 4 := by
  have h4 := bounded_fourth_moment P 6 (by norm_num) hb
  apply (charFun_cubic_sharp_fourth_bound P u h4.1).trans
  have hM : (∫ x, |x| ^ 4 ∂P.measure) / 24 ≤ (0.46 : ℝ) := by linarith [h4.2]
  exact mul_le_mul_of_nonneg_right hM (pow_nonneg (abs_nonneg u) 4)

end BerryEsseen
