import BerryEsseen.Statement
import Mathlib.Tactic

/-! A concrete inhabitant checks that the target's class of laws is nonempty. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BerryEsseen

def rademacherMeasure : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (-1) + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

theorem rademacher_integrable (f : ℝ → ℝ) : Integrable f rademacherMeasure := by
  simp only [rademacherMeasure, integrable_add_measure]
  constructor <;> exact (integrable_dirac (by simp)).smul_measure (by norm_num)

theorem integral_rademacher (f : ℝ → ℝ) :
    (∫ x, f x ∂rademacherMeasure) = f (-1) / 2 + f 1 / 2 := by
  have hi := rademacher_integrable f
  rw [rademacherMeasure, integrable_add_measure] at hi
  rw [rademacherMeasure, integral_add_measure hi.1 hi.2]
  simp [integral_smul_measure, smul_eq_mul, div_eq_mul_inv, mul_comm]

def rademacher : StandardizedLaw where
  measure := rademacherMeasure
  probability := ⟨by norm_num [rademacherMeasure, ENNReal.inv_two_add_inv_two]⟩
  first_integrable := rademacher_integrable _
  second_integrable := rademacher_integrable _
  third_integrable := rademacher_integrable _
  mean_zero := by rw [integral_rademacher]; norm_num
  second_one := by rw [integral_rademacher]; norm_num

theorem standardizedLaw_nonempty : Nonempty StandardizedLaw := ⟨rademacher⟩

theorem thirdMoment_rademacher : thirdMoment rademacher = 1 := by
  change (∫ x, |x| ^ 3 ∂rademacherMeasure) = 1
  rw [integral_rademacher]
  norm_num

end BerryEsseen
