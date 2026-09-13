import BerryEsseen.ManuscriptSmoothingTriangleBase
import Mathlib.Analysis.Convolution

noncomputable section
open MeasureTheory Set
open scoped Convolution Pointwise
namespace BerryEsseen

def manuscriptTriangleC (x : ℝ) : ℂ := manuscriptTriangle x

theorem manuscriptTriangleC_continuous : Continuous manuscriptTriangleC :=
  Complex.continuous_ofReal.comp manuscriptTriangle_continuous

theorem manuscriptTriangleC_support : Function.support manuscriptTriangleC ⊆
    Icc (-(1/2:ℝ)) (1/2) := by
  intro x hx
  apply manuscriptTriangle_support
  intro hz
  exact hx (by simp [manuscriptTriangleC, hz])

theorem manuscriptTriangleC_compact : HasCompactSupport manuscriptTriangleC :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc manuscriptTriangleC_support

theorem manuscriptTriangleC_integrable : Integrable manuscriptTriangleC :=
  manuscriptTriangle_integrable.ofReal

/-- Four uniform convolutions, grouped into two triangular densities. -/
def manuscriptDoubleTriangle : ℝ → ℂ :=
  manuscriptTriangleC ⋆[ContinuousLinearMap.mul ℂ ℂ] manuscriptTriangleC

theorem manuscriptDoubleTriangle_integrable : Integrable manuscriptDoubleTriangle :=
  manuscriptTriangleC_integrable.integrable_convolution _ manuscriptTriangleC_integrable

theorem manuscriptDoubleTriangle_continuous : Continuous manuscriptDoubleTriangle :=
  manuscriptTriangleC_compact.continuous_convolution_right _
    manuscriptTriangleC_integrable.locallyIntegrable manuscriptTriangleC_continuous

theorem manuscriptDoubleTriangle_compact : HasCompactSupport manuscriptDoubleTriangle :=
  manuscriptTriangleC_compact.convolution _ manuscriptTriangleC_compact

theorem manuscriptDoubleTriangle_outside (x : ℝ) (hx : 1 < |x|) :
    manuscriptDoubleTriangle x = 0 := by
  change (∫ t : ℝ, manuscriptTriangleC t * manuscriptTriangleC (x-t)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases ht : 1/2 ≤ |t|
  · simp [manuscriptTriangleC, manuscriptTriangle_zero t ht]
  · have hb : 1/2 ≤ |x-t| := by
      have h := abs_add_le t (x-t)
      rw [add_sub_cancel] at h
      linarith
    simp [manuscriptTriangleC, manuscriptTriangle_zero (x-t) hb]

theorem manuscriptDoubleTriangle_at_zero : manuscriptDoubleTriangle 0 = (4/3:ℂ) := by
  change (∫ t : ℝ, manuscriptTriangleC t * manuscriptTriangleC (0-t)) = _
  simp only [manuscriptTriangleC, zero_sub, manuscriptTriangle_even, ← Complex.ofReal_mul]
  simp_rw [← pow_two]
  rw [integral_complex_ofReal, manuscriptTriangle_sq_integral]
  norm_num

end BerryEsseen
