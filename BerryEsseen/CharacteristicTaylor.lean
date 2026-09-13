import BerryEsseen.TaylorBounds
import BerryEsseen.Statement
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem cos_cubic_remainder (y : ℝ) :
    |Real.cos y - 1 + y ^ 2 / 2| ≤ |y| ^ 3 / 6 := by
  simpa [div_eq_mul_inv, mul_comm] using taylor_third_global Real.cos (fun x => -Real.sin x)
    (fun x => -Real.cos x) Real.sin 1 Real.hasDerivAt_cos
    (fun x => (Real.hasDerivAt_sin x).neg)
    (fun x => by simpa using (Real.hasDerivAt_cos x).neg)
    Real.abs_sin_le_one 0 y

theorem sin_cubic_remainder (y : ℝ) :
    |Real.sin y - y| ≤ |y| ^ 3 / 6 := by
  simpa [div_eq_mul_inv, mul_comm] using taylor_third_global Real.sin Real.cos (fun x => -Real.sin x)
    (fun x => -Real.cos x) 1 Real.hasDerivAt_sin Real.hasDerivAt_cos
    (fun x => (Real.hasDerivAt_sin x).neg)
    (fun x => by simpa using Real.abs_cos_le_one x) 0 y

theorem cos_fourth_remainder (y : ℝ) :
    |Real.cos y - 1 + y ^ 2 / 2| ≤ |y| ^ 4 / 24 := by
  simpa [div_eq_mul_inv, mul_comm] using taylor_fourth_global Real.cos (fun x => -Real.sin x)
    (fun x => -Real.cos x) Real.sin Real.cos 1 Real.hasDerivAt_cos
    (fun x => (Real.hasDerivAt_sin x).neg)
    (fun x => by simpa using (Real.hasDerivAt_cos x).neg)
    Real.hasDerivAt_sin Real.abs_cos_le_one 0 y

theorem sin_fourth_remainder (y : ℝ) :
    |Real.sin y - y + y ^ 3 / 6| ≤ |y| ^ 4 / 24 := by
  simpa [div_eq_mul_inv, mul_comm] using taylor_fourth_global Real.sin Real.cos (fun x => -Real.sin x)
    (fun x => -Real.cos x) Real.sin 1 Real.hasDerivAt_sin Real.hasDerivAt_cos
    (fun x => (Real.hasDerivAt_sin x).neg)
    (fun x => by simpa using (Real.hasDerivAt_cos x).neg)
    Real.abs_sin_le_one 0 y

def charCubicRemainder (y : ℝ) : ℂ :=
  Complex.exp ((y : ℂ) * Complex.I) - 1 - (y : ℂ) * Complex.I +
    (y : ℂ) ^ 2 / 2 + (y : ℂ) ^ 3 * Complex.I / 6

theorem charCubicRemainder_re (y : ℝ) :
    (charCubicRemainder y).re = Real.cos y - 1 + y ^ 2 / 2 := by
  simp [charCubicRemainder, ← Complex.ofReal_pow]

theorem charCubicRemainder_im (y : ℝ) :
    (charCubicRemainder y).im = Real.sin y - y + y ^ 3 / 6 := by
  simp [charCubicRemainder, ← Complex.ofReal_pow]

theorem charCubicRemainder_fourth_bound (y : ℝ) :
    ‖charCubicRemainder y‖ ≤ |y| ^ 4 / 12 := by
  have h := Complex.norm_le_abs_re_add_abs_im (charCubicRemainder y)
  rw [charCubicRemainder_re, charCubicRemainder_im] at h
  linarith [cos_fourth_remainder y, sin_fourth_remainder y]

theorem charCubicRemainder_cubic_bound (y : ℝ) :
    ‖charCubicRemainder y‖ ≤ |y| ^ 3 / 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im (charCubicRemainder y)
  rw [charCubicRemainder_re, charCubicRemainder_im] at h
  have hi := abs_add_le (Real.sin y - y) (y ^ 3 / 6)
  rw [abs_div, abs_pow] at hi
  norm_num at hi
  linarith [cos_cubic_remainder y, sin_cubic_remainder y]

theorem charCubicRemainder_modulus_bound (y : ℝ) :
    ‖charCubicRemainder y‖ ≤ |y| ^ 3 * min |y| 1 := by
  by_cases hy : |y| ≤ 1
  · rw [min_eq_left hy]
    nlinarith [charCubicRemainder_fourth_bound y, pow_nonneg (abs_nonneg y) 4]
  · rw [min_eq_right (le_of_not_ge hy)]
    nlinarith [charCubicRemainder_cubic_bound y, pow_nonneg (abs_nonneg y) 3]

def signedThirdMoment (P : StandardizedLaw) : ℝ := ∫ x, x ^ 3 ∂P.measure

theorem signedThirdMoment_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x ^ 3) P.measure := by
  apply P.third_integrable.mono (by fun_prop)
  exact ae_of_all _ (fun x => by simp [Real.norm_eq_abs, abs_pow])

theorem signedThirdMoment_abs_le (P : StandardizedLaw) :
    |signedThirdMoment P| ≤ thirdMoment P := by
  calc
    _ ≤ ∫ x : ℝ, ‖x ^ 3‖ ∂P.measure := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change ‖(x ^ 3 : ℝ)‖ = |x| ^ 3
        rw [Real.norm_eq_abs, abs_pow])

theorem integrable_charCubicRemainder (P : StandardizedLaw) (u : ℝ) :
    Integrable (fun x => charCubicRemainder (u * x)) P.measure := by
  apply (P.third_integrable.const_mul (|u| ^ 3 / 2)).mono (by
    unfold charCubicRemainder
    fun_prop)
  apply ae_of_all
  intro x
  have h := charCubicRemainder_cubic_bound (u * x)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [abs_mul, mul_pow, mul_div_assoc, div_mul_eq_mul_div] using h

theorem charFun_cubic_remainder_identity (P : StandardizedLaw) (u : ℝ) :
    charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6 =
      ∫ x, charCubicRemainder (u * x) ∂P.measure := by
  have he : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I)) P.measure := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [Complex.norm_exp_ofReal_mul_I]
      norm_num)
  have h1 : Integrable (fun x : ℝ => (x : ℂ) * ((u : ℂ) * Complex.I)) P.measure :=
    P.first_integrable.ofReal.mul_const _
  have h2 : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) * ((u : ℂ) ^ 2 / 2)) P.measure :=
    P.second_integrable.ofReal.mul_const _
  have h3 : Integrable (fun x : ℝ => ((x ^ 3 : ℝ) : ℂ) * ((u : ℂ) ^ 3 * Complex.I / 6)) P.measure :=
    (signedThirdMoment_integrable P).ofReal.mul_const _
  have hf : (fun x => charCubicRemainder (u * x)) = fun x : ℝ =>
      Complex.exp ((u * x : ℝ) * Complex.I) - 1 -
      (x : ℂ) * ((u : ℂ) * Complex.I) +
      ((x ^ 2 : ℝ) : ℂ) * ((u : ℂ) ^ 2 / 2) +
      ((x ^ 3 : ℝ) : ℂ) * ((u : ℂ) ^ 3 * Complex.I / 6) := by
    funext x
    simp only [charCubicRemainder, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have he0 : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1) P.measure :=
    he.sub (integrable_const _)
  have he1 : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1 -
      (x : ℂ) * ((u : ℂ) * Complex.I)) P.measure := he0.sub h1
  have he2 : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1 -
      (x : ℂ) * ((u : ℂ) * Complex.I) +
      ((x ^ 2 : ℝ) : ℂ) * ((u : ℂ) ^ 2 / 2)) P.measure := he1.add h2
  rw [hf]
  rw [integral_add he2 h3, integral_add he1 h2,
    integral_sub he0 h1, integral_sub he (integrable_const (1 : ℂ))]
  simp only [integral_mul_const, integral_complex_ofReal, P.mean_zero, P.second_one,
    Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, sub_zero,
    integral_const, probReal_univ, one_smul]
  have hxInt : (∫ x : ℝ, (x : ℂ) ∂P.measure) = 0 := by
    simpa [P.mean_zero] using
      (integral_complex_ofReal (f := fun x : ℝ => x) (μ := P.measure))
  rw [hxInt, zero_mul, sub_zero, charFun_apply_real]
  simp only [Complex.ofReal_mul]
  change _ = _ - 1 + _ + (signedThirdMoment P : ℂ) * _
  ring

theorem charFun_cubic_modulus_bound (P : StandardizedLaw) (u : ℝ) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤
      |u| ^ 3 * ∫ x, |x| ^ 3 * min (|u| * |x|) 1 ∂P.measure := by
  have hg : Integrable (fun x : ℝ => |x| ^ 3 * min (|u| * |x|) 1) P.measure := by
    apply P.third_integrable.mono (by fun_prop)
    apply ae_of_all
    intro x
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ |x| ^ 3 * min (|u| * |x|) 1 by positivity),
      abs_of_nonneg (pow_nonneg (abs_nonneg x) 3)]
    exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) 3) (min_le_right _ _)
  rw [charFun_cubic_remainder_identity]
  calc
    _ ≤ ∫ x, ‖charCubicRemainder (u * x)‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |u| ^ 3 * (|x| ^ 3 * min (|u| * |x|) 1) ∂P.measure := by
      apply integral_mono (integrable_charCubicRemainder P u).norm (hg.const_mul _)
      intro x
      simpa [abs_mul, mul_pow, mul_assoc] using charCubicRemainder_modulus_bound (u * x)
    _ = _ := integral_const_mul _ _

theorem bounded_fourth_moment (P : StandardizedLaw) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ L) :
    Integrable (fun x : ℝ => |x| ^ 4) P.measure ∧
      (∫ x, |x| ^ 4 ∂P.measure) ≤ L * thirdMoment P := by
  have hpoint : ∀ᵐ x ∂P.measure, |x| ^ 4 ≤ L * |x| ^ 3 := by
    filter_upwards [hb] with x hx
    nlinarith [mul_le_mul_of_nonneg_right hx (pow_nonneg (abs_nonneg x) 3)]
  have hi : Integrable (fun x : ℝ => |x| ^ 4) P.measure := by
    apply (P.third_integrable.const_mul L).mono (by fun_prop)
    filter_upwards [hpoint] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg x) 4),
      abs_of_nonneg (mul_nonneg hL (pow_nonneg (abs_nonneg x) 3))] using hx
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi (P.third_integrable.const_mul L) hpoint
  simpa only [integral_const_mul, thirdMoment] using h

theorem charFun_cubic_fourth_bound (P : StandardizedLaw) (u : ℝ)
    (h4 : Integrable (fun x : ℝ => |x| ^ 4) P.measure) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤
      (∫ x, |x| ^ 4 ∂P.measure) / 12 * |u| ^ 4 := by
  rw [charFun_cubic_remainder_identity]
  calc
    _ ≤ ∫ x, ‖charCubicRemainder (u * x)‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|u| ^ 4 / 12) * |x| ^ 4 ∂P.measure := by
      apply integral_mono (integrable_charCubicRemainder P u).norm (h4.const_mul _)
      intro x
      have h := charCubicRemainder_fourth_bound (u * x)
      simpa only [abs_mul, mul_pow, div_mul_eq_mul_div] using h
    _ = _ := by rw [integral_const_mul]; ring

theorem charFun_cubic_bounded_support (P : StandardizedLaw) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ L) (u : ℝ) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤
      L * thirdMoment P / 12 * |u| ^ 4 := by
  obtain ⟨hi, hle⟩ := bounded_fourth_moment P L hL hb
  exact (charFun_cubic_fourth_bound P u hi).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hle (by norm_num)) (by positivity))

end BerryEsseen
