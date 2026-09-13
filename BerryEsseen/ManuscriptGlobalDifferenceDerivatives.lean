import BerryEsseen.ManuscriptDifferenceDerivativesCore
import BerryEsseen.MeasureCharacteristicDerivatives

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem manuscript_difference_second_raw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    (∫ x, x ^ 2 ∂manuscriptDifferenceLaw μ μ) = 2 * rawStdDev μ ^ 2 := by
  rw [manuscriptDifferenceLaw, integral_map (by fun_prop) (by fun_prop),
    raw_centered_variance_formula μ h1 h2]
  have he : (fun x : ℝ × ℝ => (x.1 - x.2) ^ 2) =
      (fun x => x.1 ^ 2 - 2 * (x.1 * x.2) + x.2 ^ 2) := by funext x; ring
  have hi : Integrable (fun x : ℝ × ℝ => x.1 ^ 2 - 2 * (x.1 * x.2)) (μ.prod μ) :=
    (h2.comp_fst μ).sub ((h1.mul_prod h1).const_mul 2)
  rw [he, integral_add hi (h2.comp_snd μ),
    integral_sub (h2.comp_fst μ) ((h1.mul_prod h1).const_mul 2),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2),
    integral_const_mul, integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x)]
  simp only [probReal_univ, one_smul, rawMean]
  ring

/-- The manuscript bounds the third derivative using the independent difference
in [-26,26] and its second moment 2v, rather than moments of P. -/
theorem manuscript_measure_squareThird_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (u : ℝ) :
    |measureCharacteristicSquareThird μ u| ≤ 52 * rawStdDev μ ^ 2 := by
  have hD : ∀ᵐ x ∂manuscriptDifferenceLaw μ μ, |x| ≤ 26 := by
    convert manuscript_difference_bounded μ μ 13 13 hμ hμ using 1 <;> norm_num
  have hi (k : ℕ) : Integrable (fun x : ℝ => x ^ k) μ := by
    simpa using (bounded_shifted_power_integrable μ 13 0 (by norm_num) hμ k).1
  have hDi (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (manuscriptDifferenceLaw μ μ) := by
    simpa using (bounded_shifted_power_integrable _ 26 0 (by norm_num) hD k).1
  have hi1 : Integrable (fun x : ℝ => x) μ := by simpa using hi 1
  have hDi1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw μ μ) := by simpa using hDi 1
  rw [manuscript_measure_squareThird_difference μ hi1 (hi 2) (hi 3) hDi1 (hDi 2) (hDi 3)]
  apply (Complex.abs_im_le_norm _).trans
  apply (norm_weightedCharFun_le _ 3 u).trans
  have habs : Integrable (fun x : ℝ => |x| ^ 3) (manuscriptDifferenceLaw μ μ) := by
    simpa only [abs_pow] using (hDi 3).abs
  calc
    (∫ x, |x| ^ 3 ∂manuscriptDifferenceLaw μ μ) ≤
        ∫ x, 26 * x ^ 2 ∂manuscriptDifferenceLaw μ μ := by
      apply integral_mono_ae habs ((hDi 2).const_mul 26)
      filter_upwards [hD] with x hx
      calc
        |x| ^ 3 = |x| * |x| ^ 2 := by ring
        _ ≤ 26 * |x| ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
        _ = 26 * x ^ 2 := by rw [sq_abs]
    _ = 52 * rawStdDev μ ^ 2 := by
      rw [integral_const_mul, manuscript_difference_second_raw μ hi1 (hi 2)]
      ring

theorem manuscript_measure_squareThird_sixty (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (hv : rawStdDev μ ^ 2 ≤ 1.1) (u : ℝ) :
    |measureCharacteristicSquareThird μ u| < 60 :=
  (manuscript_measure_squareThird_bound μ hμ u).trans_lt (by linarith)

theorem manuscript_measure_curvature_lipschitz_sixty (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (hv : rawStdDev μ ^ 2 ≤ 1.1) :
    LipschitzWith 60 (measureCharacteristicSquareCurvature μ) := by
  have hi (k : ℕ) : Integrable (fun x : ℝ => x ^ k) μ := by
    simpa using (bounded_shifted_power_integrable μ 13 0 (by norm_num) hμ k).1
  have hi1 : Integrable (fun x : ℝ => x) μ := by simpa using hi 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (measureCharacteristicSquareCurvature_hasDerivAt μ hi1 (hi 2) (hi 3) u).hasDerivWithinAt)
    (fun u _ => show ‖measureCharacteristicSquareThird μ u‖ ≤ (60 : ℝ) by
      rw [Real.norm_eq_abs]
      exact (manuscript_measure_squareThird_sixty μ hμ hv u).le)
    (mem_univ y) (mem_univ x)
  simpa only [dist_eq_norm, Real.norm_eq_abs] using hh

end BerryEsseen
