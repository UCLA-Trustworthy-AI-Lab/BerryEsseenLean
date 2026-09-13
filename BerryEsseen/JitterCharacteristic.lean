import BerryEsseen.UniformJitter
import BerryEsseen.CharacteristicTaylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual characteristic functions of the jitter and of the iid sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem charFun_real_parts (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    (charFun μ u).re = ∫ x, Real.cos (u * x) ∂μ ∧
    (charFun μ u).im = ∫ x, Real.sin (u * x) ∂μ := by
  have he : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I)) μ := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    exact ae_of_all _ (fun x => by rw [Complex.norm_exp_ofReal_mul_I]; norm_num)
  have hcf : charFun μ u = ∫ x : ℝ, Complex.exp ((u * x : ℝ) * Complex.I) ∂μ := by
    rw [charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [hcf]
  constructor
  · simpa only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] using (integral_re he).symm
  · simpa only [RCLike.im_eq_complex_im, Complex.exp_ofReal_mul_I_im] using (integral_im he).symm

theorem charFun_uniformJitter (h : ℝ) (hh : 0 < h) (u : ℝ) :
    charFun (uniformJitter h) u = (Real.sinc (h * u / 2) : ℂ) := by
  letI := uniformJitter_probability hh
  by_cases hu : u = 0
  · simp [hu]
  obtain ⟨hre, him⟩ := charFun_real_parts (uniformJitter h) u
  rw [uniformJitter_integral h _ hh] at hre him
  have hneg : u * (-h / 2) = -(u * (h / 2)) := by ring
  rw [intervalIntegral.integral_comp_mul_left _ hu, integral_cos, hneg, Real.sin_neg] at hre
  rw [intervalIntegral.integral_comp_mul_left _ hu, integral_sin, hneg, Real.cos_neg, sub_self] at him
  have hhu : h * u / 2 ≠ 0 := div_ne_zero (mul_ne_zero hh.ne' hu) (by norm_num)
  apply Complex.ext
  · rw [Complex.ofReal_re, Real.sinc_of_ne_zero hhu, hre]
    rw [show u * (h / 2) = h * u / 2 by ring]
    simp only [smul_eq_mul]
    field_simp [hu]
    ring
  · simpa using him

/-- The convention at span zero is a point mass, as in the manuscript. -/
def spanJitter (h : ℝ) : Measure ℝ := if 0 < h then uniformJitter h else Measure.dirac 0

theorem spanJitter_probability (h : ℝ) : IsProbabilityMeasure (spanJitter h) := by
  unfold spanJitter
  split_ifs with hh
  · exact uniformJitter_probability hh
  · infer_instance

theorem charFun_spanJitter (h : ℝ) (hh : 0 ≤ h) (u : ℝ) :
    charFun (spanJitter h) u = (Real.sinc (h * u / 2) : ℂ) := by
  rcases eq_or_lt_of_le hh with hzero | hpos
  · subst h
    simp [spanJitter, charFun_dirac]
  · rw [spanJitter, if_pos hpos, charFun_uniformJitter h hpos]

theorem charFun_iidSumLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (u : ℝ) :
    charFun (iidSumLaw μ n) u = charFun μ u ^ n := by
  induction n with
  | zero => simp [iidSumLaw, charFun_dirac]
  | succ n ih =>
    change charFun (μ ∗ iidSumLaw μ n) u = _
    rw [charFun_conv, ih, pow_succ]
    ring

theorem charFun_jittered_iid_sum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (h : ℝ) (hh : 0 ≤ h) (u : ℝ) :
    charFun (iidSumLaw μ n ∗ spanJitter h) u =
      (Real.sinc (h * u / 2) : ℂ) * charFun μ u ^ n := by
  letI := spanJitter_probability h
  rw [charFun_conv, charFun_spanJitter h hh, charFun_iidSumLaw]
  ring

theorem sinc_quadratic_error (x : ℝ) : |Real.sinc x - 1| ≤ x ^ 2 / 6 := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx, div_sub_one hx, abs_div]
  have h := sin_cubic_remainder x
  apply (div_le_iff₀ (abs_pos.2 hx)).2
  convert h using 1
  rw [show |x| ^ 3 = x ^ 2 * |x| by rw [pow_succ, sq_abs]]
  ring

theorem sinc_integral_cos (x : ℝ) :
    Real.sinc x = ∫ t in (0 : ℝ)..1, Real.cos (x * t) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [intervalIntegral.integral_comp_mul_left _ hx, integral_cos, Real.sinc_of_ne_zero hx]
  simp [div_eq_mul_inv, mul_comm]

theorem sinc_lipschitz_half (x y : ℝ) :
    |Real.sinc x - Real.sinc y| ≤ |x - y| / 2 := by
  have hx : IntervalIntegrable (fun t => Real.cos (x * t)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos (x * t))).intervalIntegrable _ _
  have hy : IntervalIntegrable (fun t => Real.cos (y * t)) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos (y * t))).intervalIntegrable _ _
  rw [sinc_integral_cos, sinc_integral_cos, ← intervalIntegral.integral_sub hx hy]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |Real.cos (x * t) - Real.cos (y * t)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, |x - y| * t := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hx.sub hy).abs
        ((by fun_prop : Continuous (fun t : ℝ => |x - y| * t)).intervalIntegrable _ _)
      intro t ht
      have h := Real.abs_cos_sub_cos_le (x * t) (y * t)
      rw [← sub_mul, abs_mul, abs_of_nonneg ht.1] at h
      exact h
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; norm_num; ring

theorem spanJitter_multiplier_lipschitz (h u v : ℝ) (hh : 0 ≤ h) :
    |Real.sinc (h * u / 2) - Real.sinc (h * v / 2)| ≤ h / 4 * |u - v| := by
  have hbound := sinc_lipschitz_half (h * u / 2) (h * v / 2)
  have he : h * u / 2 - h * v / 2 = h / 2 * (u - v) := by ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / 2)] at hbound
  convert hbound using 1
  ring

theorem spanJitter_multiplier_resonance_zero (h : ℝ) (hh : 0 < h) (k : ℤ) (hk : k ≠ 0) :
    Real.sinc (h * (2 * Real.pi * (k : ℝ) / h) / 2) = 0 := by
  have he : h * (2 * Real.pi * (k : ℝ) / h) / 2 = (k : ℝ) * Real.pi := by
    field_simp
  rw [he, Real.sinc_of_ne_zero (mul_ne_zero (by exact_mod_cast hk) Real.pi_ne_zero),
    Real.sin_int_mul_pi, zero_div]

end BerryEsseen
