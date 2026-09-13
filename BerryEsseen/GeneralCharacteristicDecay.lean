import BerryEsseen.LowFrequencyExpansion

noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem charFun_cubic_third_moment_bound (P : StandardizedLaw) (u : ℝ) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤
      thirdMoment P / 2 * |u| ^ 3 := by
  rw [charFun_cubic_remainder_identity]
  calc
    _ ≤ ∫ x, ‖charCubicRemainder (u * x)‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|u| ^ 3 / 2) * |x| ^ 3 ∂P.measure := by
      apply integral_mono (integrable_charCubicRemainder P u).norm (P.third_integrable.const_mul _)
      intro x
      simpa only [abs_mul, mul_pow, div_mul_eq_mul_div] using charCubicRemainder_cubic_bound (u * x)
    _ = _ := by rw [integral_const_mul]; unfold thirdMoment; ring

theorem general_low_frequency_parameters (B u : ℝ) (hB : 1 ≤ B)
    (hu : |u| ≤ 1 / (100 * B)) :
    |u| ≤ 1 / 100 ∧ B * |u| ≤ 1 / 100 ∧ u ^ 2 ≤ 1 / 10000 := by
  have hB0 : 0 < B := by linarith only [hB]
  have hmul := (le_div_iff₀ (mul_pos (by norm_num) hB0)).mp hu
  have hsmall : |u| ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_right hB (abs_nonneg u)
    nlinarith only [hmul, h]
  refine ⟨hsmall, by nlinarith only [hmul], ?_⟩
  have hsq := pow_le_pow_left₀ (abs_nonneg u) hsmall 2
  norm_num only [sq_abs] at hsq ⊢
  norm_num at hsq
  exact hsq

theorem complex_gaussian_decay_of_small_cubic (z : ℂ) (u κ : ℝ)
    (hu : |u| ≤ 1 / 100) (huκ : |u| * |κ| ≤ 1 / 100)
    (hz : ‖z - 1 + (u : ℂ) ^ 2 / 2 + (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6‖ ≤ u ^ 2 / 100) :
    ‖z‖ ≤ Real.exp (-u ^ 2 / 4) := by
  let r := z - 1 + (u : ℂ) ^ 2 / 2 + (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6
  have hre : |z.re - 1 + u ^ 2 / 2| ≤ u ^ 2 / 100 := by
    have h := (Complex.abs_re_le_norm r).trans hz
    simpa [r, ← Complex.ofReal_pow] using h
  have him : |z.im + u ^ 3 * κ / 6| ≤ u ^ 2 / 100 := by
    have h := (Complex.abs_im_le_norm r).trans hz
    simpa [r, ← Complex.ofReal_pow] using h
  have hu2 : u ^ 2 ≤ 1 / 10000 := by nlinarith [sq_abs u, abs_nonneg u]
  have hr : |z.re| ≤ 1 - u ^ 2 / 3 := by
    have h := abs_le.mp hre
    exact abs_le.mpr ⟨by nlinarith only [h.1, hu2], by nlinarith only [h.2, sq_nonneg u]⟩
  have hi : |z.im| ≤ u ^ 2 / 3 := by
    have h := abs_sub (z.im + u ^ 3 * κ / 6) (u ^ 3 * κ / 6)
    rw [add_sub_cancel_right] at h
    have hk : |u ^ 3 * κ / 6| ≤ u ^ 2 / 600 := by
      rw [abs_div, abs_mul, abs_pow]
      norm_num only [show |(6 : ℝ)| = 6 by norm_num]
      have hmul := mul_le_mul_of_nonneg_right huκ (sq_nonneg u)
      have hid : |u| ^ 3 * |κ| = |u| * |κ| * u ^ 2 := by rw [← sq_abs u]; ring
      rw [hid]
      nlinarith only [hmul]
    nlinarith only [h, him, hk, sq_nonneg u]
  have hr2 : z.re ^ 2 ≤ (1 - u ^ 2 / 3) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.re) hr 2
  have hi2 : z.im ^ 2 ≤ (u ^ 2 / 3) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z.im) hi 2
  have hn : ‖z‖ ^ 2 ≤ 1 - u ^ 2 / 2 := by
    have hn := Complex.sq_norm_sub_sq_re z
    nlinarith [mul_le_mul_of_nonneg_right hu2 (sq_nonneg u)]
  have he := Real.add_one_le_exp (-u ^ 2 / 2)
  have heq : Real.exp (-u ^ 2 / 4) ^ 2 = Real.exp (-u ^ 2 / 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.exp_pos (-u ^ 2 / 4), norm_nonneg z]

theorem charFun_general_low_frequency_decay (P : StandardizedLaw) (B : ℝ)
    (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B) (u : ℝ)
    (hu : |u| ≤ 1 / (100 * B)) :
    ‖charFun P.measure u‖ ≤ Real.exp (-u ^ 2 / 4) := by
  have hpar := general_low_frequency_parameters B u hB hu
  have hk := mul_le_mul_of_nonneg_left ((signedThirdMoment_abs_le P).trans hβ) (abs_nonneg u)
  have huκ : |u| * |signedThirdMoment P| ≤ 1 / 100 := by nlinarith only [hk, hpar.2.1]
  apply complex_gaussian_decay_of_small_cubic _ u (signedThirdMoment P) hpar.1 huκ
  have hrem := charFun_cubic_third_moment_bound P u
  have hβu := mul_le_mul_of_nonneg_right hβ (abs_nonneg u)
  have hβu' : thirdMoment P * |u| ≤ 1 / 100 := hβu.trans hpar.2.1
  have hm := mul_le_mul_of_nonneg_right hβu' (sq_nonneg u)
  have hid : thirdMoment P / 2 * |u| ^ 3 = (thirdMoment P * |u| * u ^ 2) / 2 := by rw [← sq_abs u]; ring
  rw [hid] at hrem
  nlinarith only [hrem, hm, sq_nonneg u]

theorem cubicExponent_general_norm (u κ B : ℝ) (hB : 1 ≤ B)
    (hκ : |κ| ≤ B) (hu : |u| ≤ 1 / (100 * B)) :
    ‖cubicExponent u κ‖ ≤ u ^ 2 := by
  have h := norm_sub_le (-(u : ℂ) ^ 2 / 2) ((u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6)
  simp only [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, Complex.norm_I, mul_one] at h
  norm_num at h
  have hpar := general_low_frequency_parameters B u hB hu
  have hκu := mul_le_mul_of_nonneg_left hκ (abs_nonneg u)
  have hκu' : |u| * |κ| ≤ 1 / 100 := by nlinarith only [hκu, hpar.2.1]
  have hm := mul_le_mul_of_nonneg_right hκu' (sq_nonneg u)
  change ‖cubicExponent u κ‖ ≤ _ at h
  have hid : |u| ^ 3 * |κ| = |u| * |κ| * u ^ 2 := by rw [← sq_abs u]; ring
  rw [hid] at h
  nlinarith only [h, hm, sq_nonneg u]

theorem cubicExponent_exponential_decay (u κ : ℝ) :
    ‖Complex.exp (cubicExponent u κ)‖ ≤ Real.exp (-u ^ 2 / 4) := by
  rw [Complex.norm_exp, cubicExponent_re, Real.exp_le_exp]
  nlinarith only [sq_nonneg u]

theorem charFun_general_cubic_exponential_bound (P : StandardizedLaw) (B : ℝ)
    (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B) (u : ℝ)
    (hu : |u| ≤ 1 / (100 * B)) :
    ‖charFun P.measure u - Complex.exp (cubicExponent u (signedThirdMoment P))‖ ≤
      |u| ^ 3 * (∫ x, |x| ^ 3 * min (|u| * |x|) 1 ∂P.measure) + |u| ^ 4 := by
  let w := cubicExponent u (signedThirdMoment P)
  have hw : ‖w‖ ≤ u ^ 2 := cubicExponent_general_norm u _ B hB ((signedThirdMoment_abs_le P).trans hβ) hu
  have hu2 := (general_low_frequency_parameters B u hB hu).2.2
  have he := Complex.norm_exp_sub_one_sub_id_le (show ‖w‖ ≤ 1 by linarith only [hw, hu2])
  have hw2 : ‖w‖ ^ 2 ≤ |u| ^ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg w) hw 2
    convert h using 1
    rw [← sq_abs u]
    ring
  have hf : ‖charFun P.measure u - 1 - w‖ ≤
      |u| ^ 3 * (∫ x, |x| ^ 3 * min (|u| * |x|) 1 ∂P.measure) := by
    convert charFun_cubic_modulus_bound P u using 1
    congr 1
    dsimp [w, cubicExponent]
    ring
  have ht := norm_sub_le (charFun P.measure u - 1 - w) (Complex.exp w - 1 - w)
  rw [show charFun P.measure u - 1 - w - (Complex.exp w - 1 - w) =
    charFun P.measure u - Complex.exp w by ring] at ht
  nlinarith only [ht, hf, he, hw2]

theorem charFun_general_power_cubic_exponential_bound (P : StandardizedLaw) (B : ℝ)
    (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B) (u : ℝ)
    (hu : |u| ≤ 1 / (100 * B)) (k : ℕ) :
    ‖charFun P.measure u ^ (k + 1) -
      Complex.exp ((k + 1 : ℂ) * cubicExponent u (signedThirdMoment P))‖ ≤
      (k + 1 : ℝ) *
        (|u| ^ 3 * (∫ x, |x| ^ 3 * min (|u| * |x|) 1 ∂P.measure) + |u| ^ 4) *
        Real.exp (-(k : ℝ) * u ^ 2 / 4) := by
  have h := complex_pow_difference_bound (charFun P.measure u)
    (Complex.exp (cubicExponent u (signedThirdMoment P)))
    (Real.exp (-u ^ 2 / 4)) (Real.exp_pos _).le
    (charFun_general_low_frequency_decay P B hB hβ u hu)
    (cubicExponent_exponential_decay u (signedThirdMoment P)) k
  rw [← Complex.exp_nat_mul] at h
  have heq : Real.exp (-u ^ 2 / 4) ^ k = Real.exp (-(k : ℝ) * u ^ 2 / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at h
  have hh := mul_le_mul_of_nonneg_left (charFun_general_cubic_exponential_bound P B hB hβ u hu)
    (show 0 ≤ (k + 1 : ℝ) * Real.exp (-(k : ℝ) * u ^ 2 / 4) by positivity)
  push_cast at h
  nlinarith only [h, hh]

end BerryEsseen
