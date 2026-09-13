import BerryEsseen.CharacteristicTaylor
import BerryEsseen.BoundedExtremizers

/-! Uniform low-frequency Gaussian decay for the actual extremizer class. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem charFun_cubic_bound_two (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10) (u : ℝ) :
    ‖charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6‖ ≤ 2 * |u| ^ 4 := by
  exact (charFun_cubic_bounded_support P 10 (by norm_num) hb u).trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem complex_gaussian_decay_of_cubic (z : ℂ) (u κ : ℝ) (hκ : |κ| ≤ 2)
    (hu : |u| ≤ 1 / 100)
    (hz : ‖z - 1 + (u : ℂ) ^ 2 / 2 + (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6‖ ≤
      2 * |u| ^ 4) : ‖z‖ ≤ Real.exp (-u ^ 2 / 4) := by
  let r := z - 1 + (u : ℂ) ^ 2 / 2 + (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6
  have hre : |z.re - 1 + u ^ 2 / 2| ≤ 2 * |u| ^ 4 := by
    have h := (Complex.abs_re_le_norm r).trans hz
    simpa [r, ← Complex.ofReal_pow] using h
  have him : |z.im + u ^ 3 * κ / 6| ≤ 2 * |u| ^ 4 := by
    have h := (Complex.abs_im_le_norm r).trans hz
    simpa [r, ← Complex.ofReal_pow] using h
  have hu0 := abs_nonneg u
  have hu2 : u ^ 2 ≤ 1 / 10000 := by nlinarith [sq_abs u]
  have hu4 : |u| ^ 4 ≤ u ^ 2 / 10000 := by
    have h := mul_le_mul_of_nonneg_right hu2 (sq_nonneg u)
    nlinarith [show |u| ^ 4 = (u ^ 2) ^ 2 by rw [← sq_abs u]; ring]
  have hr : |z.re| ≤ 1 - u ^ 2 / 3 := by
    apply abs_le.2
    have h := abs_le.1 hre
    constructor <;> nlinarith
  have hu3 : |u| ^ 3 ≤ u ^ 2 / 100 := by
    have h := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
    nlinarith [sq_abs u]
  have hi : |z.im| ≤ u ^ 2 / 3 := by
    have h := abs_sub (z.im + u ^ 3 * κ / 6) (u ^ 3 * κ / 6)
    rw [add_sub_cancel_right] at h
    have hk : |u ^ 3 * κ / 6| ≤ |u| ^ 3 / 3 := by
      rw [abs_div, abs_mul, abs_pow]
      norm_num
      nlinarith [mul_le_mul_of_nonneg_left hκ (pow_nonneg hu0 3)]
    nlinarith
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

theorem charFun_low_frequency_decay (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (u : ℝ) (hu : |u| ≤ 1 / 100) :
    ‖charFun P.measure u‖ ≤ Real.exp (-u ^ 2 / 4) :=
  complex_gaussian_decay_of_cubic _ u (signedThirdMoment P)
    ((signedThirdMoment_abs_le P).trans hβ) hu (charFun_cubic_bound_two P hβ hb u)

end BerryEsseen
