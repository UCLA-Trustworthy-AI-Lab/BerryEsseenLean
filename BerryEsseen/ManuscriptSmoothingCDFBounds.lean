import BerryEsseen.ManuscriptSmoothingConvolution
import BerryEsseen.ManuscriptSmoothingInversion

/-! Elementary bounds and measurability of the manuscript's actual CDF difference. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped NNReal
namespace BerryEsseen

theorem manuscript_signed_cdf_difference_bounded
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) :
    ∀ x, |μ.real (Iic x) - s (Iic x)| ≤
      1 + s.toJordanDecomposition.posPart.real univ +
        s.toJordanDecomposition.negPart.real univ := by
  intro x
  have hμ0 : 0 ≤ μ.real (Iic x) := ENNReal.toReal_nonneg
  have hμ1 : μ.real (Iic x) ≤ 1 := by
    simpa using (measureReal_mono (μ := μ) (subset_univ (Iic x)))
  have hp0 : 0 ≤ s.toJordanDecomposition.posPart.real (Iic x) := ENNReal.toReal_nonneg
  have hn0 : 0 ≤ s.toJordanDecomposition.negPart.real (Iic x) := ENNReal.toReal_nonneg
  have hp := measureReal_mono (μ := s.toJordanDecomposition.posPart) (subset_univ (Iic x))
  have hn := measureReal_mono (μ := s.toJordanDecomposition.negPart) (subset_univ (Iic x))
  have hpU : 0 ≤ s.toJordanDecomposition.posPart.real univ := ENNReal.toReal_nonneg
  have hnU : 0 ≤ s.toJordanDecomposition.negPart.real univ := ENNReal.toReal_nonneg
  rw [signedMeasure_jordan_apply s (Iic x) measurableSet_Iic]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem manuscript_probability_cdf_monotone
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (fun x : ℝ => μ.real (Iic x)) := by
  intro x y hxy
  exact measureReal_mono (Iic_subset_Iic.mpr hxy)

theorem manuscript_signed_cdf_difference_measurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x))) :
    Measurable (fun x => μ.real (Iic x) - s (Iic x)) :=
  (manuscript_probability_cdf_monotone μ).measurable.sub hM.continuous.measurable

theorem manuscript_signed_cdf_difference_growth
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x))) :
    ∀ x y, x ≤ y →
      (μ.real (Iic x) - s (Iic x)) - (M : ℝ) * (y - x) ≤
        μ.real (Iic y) - s (Iic y) := by
  apply manuscript_cdf_difference_growth _ _ (manuscript_probability_cdf_monotone μ) M
  intro x y
  simpa only [Real.dist_eq] using hM.dist_le_mul x y

end BerryEsseen
