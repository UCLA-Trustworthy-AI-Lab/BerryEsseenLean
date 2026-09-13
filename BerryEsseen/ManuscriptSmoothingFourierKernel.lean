import BerryEsseen.ManuscriptSmoothingUniforms
import BerryEsseen.ManuscriptSmoothingDouble
import BerryEsseen.ManuscriptAngularInversion
import BerryEsseen.EdgeworthDensityFourier
import Mathlib.Analysis.Fourier.Convolution

noncomputable section
open MeasureTheory Set
open scoped FourierTransform Convolution
namespace BerryEsseen

theorem manuscriptDoubleTriangle_angular (t : ℝ) :
    manuscriptAngularFourier manuscriptDoubleTriangle t = (Real.sinc (t/4):ℂ)^4 :=
  manuscript_four_uniform_density_angular t

theorem manuscriptDoubleTriangle_angular_integrable :
    Integrable (manuscriptAngularFourier manuscriptDoubleTriangle) := by
  have h : Integrable (fun t : ℝ => ((8*Real.pi/3)*manuscriptSmoothingKernel t : ℝ)) :=
    manuscriptSmoothingKernel_integrable.const_mul _
  have he : manuscriptAngularFourier manuscriptDoubleTriangle =
      fun t : ℝ => (((8*Real.pi/3)*manuscriptSmoothingKernel t : ℝ):ℂ) := by
    funext t
    rw [manuscriptDoubleTriangle_angular]
    unfold manuscriptSmoothingKernel
    push_cast
    field_simp
  rw [he]
  exact h.ofReal

/-- Fourier inversion of the actual four-uniform convolution gives the
Fourier transform of the original sinc-fourth kernel. -/
theorem manuscriptSmoothingKernel_fourier (t : ℝ) :
    densityFourier manuscriptSmoothingKernel t = (3/4:ℂ)*manuscriptDoubleTriangle (-t) := by
  have hi := manuscriptAngularFourier_inversion manuscriptDoubleTriangle
    manuscriptDoubleTriangle_integrable manuscriptDoubleTriangle_continuous
    manuscriptDoubleTriangle_angular_integrable (-t)
  simp only [manuscriptDoubleTriangle_angular, neg_neg] at hi
  have he : densityFourier manuscriptSmoothingKernel t =
      ((3/(8*Real.pi):ℝ):ℂ) * ∫ u : ℝ, (Real.sinc (u/4):ℂ)^4 * realPhase t u := by
    unfold densityFourier manuscriptSmoothingKernel
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc, integral_const_mul]
  have hp (u : ℝ) : realPhase (-u) (-t) = realPhase t u := by
    unfold realPhase
    congr 2
    ring
  simp_rw [hp] at hi
  rw [he, hi]
  push_cast
  ring

theorem manuscriptSmoothingKernel_integral : (∫ x : ℝ, manuscriptSmoothingKernel x) = 1 := by
  have h := manuscriptSmoothingKernel_fourier 0
  rw [neg_zero, manuscriptDoubleTriangle_at_zero, densityFourier_zero] at h
  norm_num at h
  exact_mod_cast h

theorem manuscriptSmoothingKernel_fourier_zero (t : ℝ) (ht : 1 < |t|) :
    densityFourier manuscriptSmoothingKernel t = 0 := by
  rw [manuscriptSmoothingKernel_fourier,
    manuscriptDoubleTriangle_outside (-t) (by simpa using ht), mul_zero]

theorem manuscriptSmoothingKernel_fourier_integrable :
    Integrable (densityFourier manuscriptSmoothingKernel) := by
  have h := manuscriptDoubleTriangle_integrable.comp_neg.const_mul (3/4:ℂ)
  have he : densityFourier manuscriptSmoothingKernel =
      fun t => (3/4:ℂ)*manuscriptDoubleTriangle (-t) :=
    funext manuscriptSmoothingKernel_fourier
  rw [he]
  exact h

theorem manuscriptSmoothingKernel_inversion (y : ℝ) :
    (manuscriptSmoothingKernel y : ℂ) = ((1/(2*Real.pi):ℝ):ℂ) *
      ∫ t : ℝ, densityFourier manuscriptSmoothingKernel t * realPhase (-t) y :=
  manuscript_densityFourier_inversion manuscriptSmoothingKernel
    manuscriptSmoothingKernel_integrable manuscriptSmoothingKernel_continuous
    manuscriptSmoothingKernel_fourier_integrable y

theorem manuscriptSmoothingKernel_fourier_norm (t : ℝ) :
    ‖densityFourier manuscriptSmoothingKernel t‖ ≤ 1 := by
  calc
    _ ≤ ∫ x : ℝ, ‖(manuscriptSmoothingKernel x:ℂ)*realPhase t x‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, manuscriptSmoothingKernel x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [norm_mul, realPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (manuscriptSmoothingKernel_nonneg x)]
    _ = 1 := manuscriptSmoothingKernel_integral

end BerryEsseen
