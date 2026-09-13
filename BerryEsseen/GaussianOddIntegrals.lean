import BerryEsseen.LowFrequencyIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Exact odd absolute Gaussian integrals used by effective Fourier estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem gaussian_polynomial_tendsto_zero (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) atTop (𝓝 0) := by
  have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (k : ℝ)).tendsto_zero_of_tendsto
    (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)))
  simpa only [Real.rpow_natCast] using h

theorem gaussian_cubic_integral_Ioi (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ 3 * Real.exp (-b * x ^ 2)) = 1 / (2 * b ^ 2) := by
  let F := fun x : ℝ => -(b * x ^ 2 + 1) * Real.exp (-b * x ^ 2) / (2 * b ^ 2)
  have hd (x : ℝ) : HasDerivAt F (x ^ 3 * Real.exp (-b * x ^ 2)) x := by
    have hp := ((hasDerivAt_pow 2 x).const_mul b).add_const 1
    have he := ((hasDerivAt_pow 2 x).const_mul (-b)).exp
    convert (hp.neg.mul he).div_const (2 * b ^ 2) using 1
    dsimp only [Pi.neg_apply, Pi.add_apply]
    norm_num
    field_simp [hb.ne']
    <;> ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h2 := (gaussian_polynomial_tendsto_zero 2 b hb).const_mul b
    have h0 := gaussian_polynomial_tendsto_zero 0 b hb
    have hh := (h2.add h0).neg.div_const (2 * b ^ 2)
    simp only [mul_zero, zero_add, neg_zero, zero_div] at hh
    convert hh using 1
    funext x
    dsimp only [F]
    ring
  have hint : IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-b * x ^ 2)) (Ioi 0) := by
    apply (gaussian_abs_pow_integrable 3 b hb).integrableOn.congr_fun
      (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hint hlim
  calc
    _ = 0 - F 0 := h
    _ = _ := by dsimp [F]; norm_num; ring

theorem gaussian_quintic_integral_Ioi (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x ^ 5 * Real.exp (-b * x ^ 2)) = 1 / b ^ 3 := by
  let F := fun x : ℝ => -(b ^ 2 * x ^ 4 + 2 * b * x ^ 2 + 2) * Real.exp (-b * x ^ 2) / (2 * b ^ 3)
  have hd (x : ℝ) : HasDerivAt F (x ^ 5 * Real.exp (-b * x ^ 2)) x := by
    have hp := (((hasDerivAt_pow 4 x).const_mul (b ^ 2)).add
      ((hasDerivAt_pow 2 x).const_mul (2 * b))).add_const 2
    have he := ((hasDerivAt_pow 2 x).const_mul (-b)).exp
    convert (hp.neg.mul he).div_const (2 * b ^ 3) using 1
    dsimp only [Pi.neg_apply, Pi.add_apply]
    norm_num
    field_simp [hb.ne']
    <;> ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h4 := (gaussian_polynomial_tendsto_zero 4 b hb).const_mul (b ^ 2)
    have h2 := (gaussian_polynomial_tendsto_zero 2 b hb).const_mul (2 * b)
    have h0 := (gaussian_polynomial_tendsto_zero 0 b hb).const_mul 2
    have hh := ((h4.add h2).add h0).neg.div_const (2 * b ^ 3)
    simp only [mul_zero, zero_add, neg_zero, zero_div] at hh
    convert hh using 1
    funext x
    dsimp only [F]
    ring
  have hint : IntegrableOn (fun x : ℝ => x ^ 5 * Real.exp (-b * x ^ 2)) (Ioi 0) := by
    apply (gaussian_abs_pow_integrable 5 b hb).integrableOn.congr_fun
      (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hint hlim
  calc
    _ = 0 - F 0 := h
    _ = _ := by dsimp [F]; norm_num; ring

theorem gaussian_abs_cubic_integral (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ 3 * Real.exp (-b * x ^ 2)) = 1 / b ^ 2 := by
  have h := integral_comp_abs (f := fun x : ℝ => x ^ 3 * Real.exp (-b * x ^ 2))
  simp only [sq_abs] at h
  rw [h, gaussian_cubic_integral_Ioi b hb]
  ring

theorem gaussian_abs_quintic_integral (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ 5 * Real.exp (-b * x ^ 2)) = 2 / b ^ 3 := by
  have h := integral_comp_abs (f := fun x : ℝ => x ^ 5 * Real.exp (-b * x ^ 2))
  simp only [sq_abs] at h
  rw [h, gaussian_quintic_integral_Ioi b hb]
  ring

end BerryEsseen
