import BerryEsseen.ManuscriptSmoothingTriangleBase
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_affine_exp_primitive (a b c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((a + b * y) / c - b / c ^ 2) * Complex.exp (c * y))
      ((a + b * x) * Complex.exp (c * x)) x := by
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hpoly := (((hx.const_mul b).const_add a).div_const c).sub_const (b / c ^ 2)
  have hexp := (Complex.hasDerivAt_exp (c * x)).comp x (hx.const_mul c)
  convert hpoly.mul hexp using 1
  dsimp only [Function.comp_apply]
  field_simp
  ring

theorem manuscript_affine_exp_integral (a b c : ℂ) (hc : c ≠ 0) (L R : ℝ) :
    (∫ x in L..R, (a + b * (x : ℂ)) * Complex.exp (c * (x : ℂ))) =
      ((a + b * R) / c - b / c ^ 2) * Complex.exp (c * R) -
      ((a + b * L) / c - b / c ^ 2) * Complex.exp (c * L) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => manuscript_affine_exp_primitive a b c hc x)
  apply Continuous.intervalIntegrable
  fun_prop

theorem manuscript_triangle_fourier_halves (t : ℝ) (ht : t ≠ 0) :
    (∫ x in (-(1 / 2 : ℝ))..0, (2 + 4 * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) +
    (∫ x in (0 : ℝ)..(1 / 2), (2 - 4 * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) =
      (Real.sinc (t / 4) : ℂ) ^ 2 := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hc : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero htC Complex.I_ne_zero
  have hneg : (fun x : ℝ => (2 - 4 * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) =
      fun x : ℝ => (2 + (-4) * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by
    funext x
    ring
  rw [hneg, manuscript_affine_exp_integral 2 4 _ hc,
    manuscript_affine_exp_integral 2 (-4) _ hc]
  have heP : (t : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) = ((t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have heM : (t : ℂ) * Complex.I * ((-(1 / 2 : ℝ)) : ℂ) = ((-(t / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [Complex.ofReal_neg]
  rw [heP, heM]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.sinc_of_ne_zero (div_ne_zero ht (by norm_num))]
  have hcos : Real.cos (t / 2) = 1 - 2 * Real.sin (t / 4) ^ 2 := by
    have h := Real.sin_sq_eq_half_sub (t / 4)
    rw [show 2 * (t / 4) = t / 2 by ring] at h
    linarith
  rw [hcos]
  push_cast
  field_simp
  simp only [Complex.I_sq]
  ring

theorem manuscriptTriangle_fourier (t : ℝ) :
    densityFourier manuscriptTriangle t = (Real.sinc (t / 4) : ℂ) ^ 2 := by
  by_cases ht : t = 0
  · subst t
    simp only [densityFourier, realPhase, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one, zero_div, Real.sinc_zero, Complex.ofReal_one, one_pow]
    rw [integral_complex_ofReal, manuscriptTriangle_integral]
    norm_num
  let f : ℝ → ℂ := fun x => (manuscriptTriangle x : ℂ) * realPhase t x
  have hcont : Continuous f := by
    dsimp [f, realPhase]
    apply (Complex.continuous_ofReal.comp manuscriptTriangle_continuous).mul
    fun_prop
  have hs : Function.support f ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx
    apply manuscriptTriangle_support
    intro hz
    apply hx
    simp [f, hz]
  have hi : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), f x) = ∫ x : ℝ, f x := by
    rw [← integral_indicator measurableSet_Icc, indicator_eq_self.mpr hs]
  change (∫ x : ℝ, f x) = _
  rw [← hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-(1 / 2)) 0) (hcont.intervalIntegrable 0 (1 / 2))]
  have hl : (∫ x in (-(1 / 2 : ℝ))..0, f x) =
      ∫ x in (-(1 / 2 : ℝ))..0,
        (2 + 4 * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    dsimp [f]
    rw [manuscriptTriangle_left x hx]
    unfold realPhase
    push_cast
    congr 2
    ring
  have hr : (∫ x in (0 : ℝ)..(1 / 2), f x) =
      ∫ x in (0 : ℝ)..(1 / 2),
        (2 - 4 * (x : ℂ)) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    dsimp [f]
    rw [manuscriptTriangle_right x hx]
    unfold realPhase
    push_cast
    congr 2
    ring
  rw [hl, hr]
  exact manuscript_triangle_fourier_halves t ht

end BerryEsseen
