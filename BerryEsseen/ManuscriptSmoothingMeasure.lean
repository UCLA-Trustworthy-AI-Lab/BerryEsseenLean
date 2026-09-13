import BerryEsseen.ManuscriptSmoothingMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual measure with the manuscript's sinc⁴ density. -/
noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

def manuscriptSmoothingMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (manuscriptSmoothingKernel x))

instance : IsFiniteMeasure manuscriptSmoothingMeasure :=
  isFiniteMeasure_withDensity_ofReal manuscriptSmoothingKernel_integrable.hasFiniteIntegral

theorem manuscriptSmoothingMeasure_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂manuscriptSmoothingMeasure) =
      ∫ x, manuscriptSmoothingKernel x * f x := by
  rw [manuscriptSmoothingMeasure, integral_withDensity_eq_integral_toReal_smul
    manuscriptSmoothingKernel_continuous.measurable.ennreal_ofReal
    (by simp)]
  simp only [ENNReal.toReal_ofReal (manuscriptSmoothingKernel_nonneg _), smul_eq_mul]

theorem manuscriptSmoothingMeasure_setIntegral (f : ℝ → ℝ) (s : Set ℝ)
    (hs : MeasurableSet s) :
    (∫ x in s, f x ∂manuscriptSmoothingMeasure) =
      ∫ x in s, manuscriptSmoothingKernel x * f x := by
  rw [manuscriptSmoothingMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    manuscriptSmoothingKernel_continuous.measurable.ennreal_ofReal.aemeasurable
    (by simp) _ hs]
  simp only [ENNReal.toReal_ofReal (manuscriptSmoothingKernel_nonneg _), smul_eq_mul]

theorem manuscriptSmoothingMeasure_integrable_iff (f : ℝ → ℝ) :
    Integrable f manuscriptSmoothingMeasure ↔
      Integrable (fun x => manuscriptSmoothingKernel x * f x) := by
  rw [manuscriptSmoothingMeasure, integrable_withDensity_iff_integrable_smul'
    manuscriptSmoothingKernel_continuous.measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (manuscriptSmoothingKernel_nonneg _), smul_eq_mul]

theorem manuscriptSmoothingMeasure_real (s : Set ℝ) (hs : MeasurableSet s) :
    manuscriptSmoothingMeasure.real s = ∫ x in s, manuscriptSmoothingKernel x := by
  have hh := manuscriptSmoothingMeasure_setIntegral (fun _ => 1) s hs
  simpa using hh

theorem manuscriptSmoothingMeasure_first_moment :
    Integrable (fun x : ℝ => x) manuscriptSmoothingMeasure := by
  rw [manuscriptSmoothingMeasure_integrable_iff]
  simpa only [mul_comm] using manuscriptSmoothingKernel_signed_moment_integrable

theorem manuscriptSmoothingMeasure_loss_integrable :
    Integrable (fun x : ℝ => max (16 - x) 0) manuscriptSmoothingMeasure := by
  rw [manuscriptSmoothingMeasure_integrable_iff]
  simpa only [mul_comm] using manuscriptSmoothingKernel_loss_integrable

theorem manuscriptSmoothingMeasure_loss_plus_integrable :
    Integrable (fun x : ℝ => max (16 + x) 0) manuscriptSmoothingMeasure := by
  exact ((integrable_const 16).add manuscriptSmoothingMeasure_first_moment).sup (integrable_const 0)

theorem manuscriptSmoothingMeasure_tail :
    manuscriptSmoothingMeasure.real (Ioi 16) < 1 / 8 := by
  rw [manuscriptSmoothingMeasure_real _ measurableSet_Ioi]
  exact manuscriptSmoothingKernel_tail_sixteen_lt

theorem manuscriptSmoothingMeasure_loss_symmetry :
    (∫ x, max (16 + x) 0 ∂manuscriptSmoothingMeasure) =
      ∫ x, max (16 - x) 0 ∂manuscriptSmoothingMeasure := by
  simp only [manuscriptSmoothingMeasure_integral]
  simpa only [mul_comm] using manuscriptSmoothingKernel_loss_symmetry

theorem manuscriptSmoothingMeasure_tail_symmetry :
    manuscriptSmoothingMeasure.real (Iio (-16)) = manuscriptSmoothingMeasure.real (Ioi 16) := by
  rw [manuscriptSmoothingMeasure_real _ measurableSet_Iio,
    manuscriptSmoothingMeasure_real _ measurableSet_Ioi]
  have hh := integral_comp_neg_Iic (-16 : ℝ) manuscriptSmoothingKernel
  simpa only [neg_neg, manuscriptSmoothingKernel_even, integral_Iic_eq_integral_Iio] using hh

end BerryEsseen
