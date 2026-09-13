import BerryEsseen.GlobalSpectralBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem appendix_global_cutoff_ge_ten : 10 ≤ appendixGlobalCutoff := by
  have h := Real.add_one_le_exp (20 * appendixA)
  change 10 ≤ Real.exp (20 * appendixA)
  linarith [show (10 : ℝ) ≤ 20 * appendixA + 1 by norm_num [appendixA]]

theorem appendix_derivative_error_formula :
    appendixDerivativeError = (10 : ℝ) ^ 10 * Real.exp (-60 * appendixA) := by
  unfold appendixDerivativeError appendixRetention appendixGlobalCutoff
  rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem appendix_derivative_error_small :
    0 < appendixDerivativeError ∧ appendixDerivativeError ≤ 1 / (10 : ℝ) ^ 6 := by
  rw [appendix_derivative_error_formula]
  refine ⟨by positivity, ?_⟩
  have h := exponential_sixteenth_bound ((10 : ℝ) ^ 16) (60 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(60 * appendixA) = -60 * appendixA by ring] at h
  linarith

theorem appendix_derivative_transport_budget (w u : ℝ)
    (hw : w ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hu : |u| ≤ appendixGlobalCutoff + 1) :
    2000 * (1 + |u|) * w ≤ appendixDerivativeError := by
  have hT := appendix_global_cutoff_ge_ten
  have hτ := appendix_retention_bounds.1
  have h1 := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2000 * (1 + |u|) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hu (show 0 ≤ 2000 * (10 : ℝ) ^ 5 * appendixRetention by positivity)
  have hT2 : appendixGlobalCutoff + 2 ≤ 3 * appendixGlobalCutoff ^ 2 := by nlinarith [sq_nonneg (appendixGlobalCutoff - 1)]
  have h3 := mul_le_mul_of_nonneg_right hT2 (show 0 ≤ 2000 * (10 : ℝ) ^ 5 * appendixRetention by positivity)
  unfold appendixDerivativeError
  nlinarith only [h1, h2, h3, mul_nonneg hτ.le (sq_nonneg appendixGlobalCutoff)]

end BerryEsseen
