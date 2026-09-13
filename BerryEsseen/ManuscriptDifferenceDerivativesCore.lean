import BerryEsseen.ManuscriptIndependentCopy
import BerryEsseen.MeasureCharacteristicDerivativesCore

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem manuscript_difference_bounded (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (R S : ℝ)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ x ∂ν, |x| ≤ S) :
    ∀ᵐ x ∂manuscriptDifferenceLaw μ ν, |x| ≤ R + S := by
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).mpr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact (abs_sub x y).trans (add_le_add hx hy)

theorem manuscript_weightedCharFun_re (μ : Measure ℝ) (k : ℕ)
    (hk : Integrable (fun x : ℝ => x ^ k) μ) (u : ℝ) :
    (weightedCharFun μ k u).re = ∫ x, x ^ k * Real.cos (u * x) ∂μ := by
  change RCLike.re (∫ x : ℝ, (x : ℂ) ^ k * realPhase u x ∂μ) = _
  rw [← integral_re (weightedCharFun_integrable μ k hk u)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change (((x : ℂ) ^ k * realPhase u x).re) = _
    simp only [realPhase, ← Complex.ofReal_pow,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re])

theorem manuscript_weightedCharFun_im (μ : Measure ℝ) (k : ℕ)
    (hk : Integrable (fun x : ℝ => x ^ k) μ) (u : ℝ) :
    (weightedCharFun μ k u).im = ∫ x, x ^ k * Real.sin (u * x) ∂μ := by
  change RCLike.im (∫ x : ℝ, (x : ℂ) ^ k * realPhase u x ∂μ) = _
  rw [← integral_im (weightedCharFun_integrable μ k hk u)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change (((x : ℂ) ^ k * realPhase u x).im) = _
    simp only [realPhase, ← Complex.ofReal_pow,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im])

theorem manuscript_measure_squareSlope_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ)
    (hD1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw μ μ)) (u : ℝ) :
    measureCharacteristicSquareSlope μ u =
      -(weightedCharFun (manuscriptDifferenceLaw μ μ) 1 u).im := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
    (measure_charFun_hasDerivAt (manuscriptDifferenceLaw μ μ) hD1 u)
  have he : (fun v => (charFun (manuscriptDifferenceLaw μ μ) v).re) =
      measureCharacteristicSquare μ := by
    funext v
    rw [manuscriptDifferenceLaw_charFun, Complex.mul_conj]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq, measureCharacteristicSquare]
  change HasDerivAt (fun v => (charFun (manuscriptDifferenceLaw μ μ) v).re) _ u at hd
  rw [he] at hd
  have hd' : HasDerivAt (measureCharacteristicSquare μ)
      (-(weightedCharFun (manuscriptDifferenceLaw μ μ) 1 u).im) u := by
    simpa only [Complex.reCLM_apply, measureCharFunDerivative, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub] using hd
  exact (measureCharacteristicSquare_hasDerivAt μ h1 u).unique hd'

theorem manuscript_measure_squareCurvature_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (hD1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw μ μ))
    (hD2 : Integrable (fun x : ℝ => x ^ 2) (manuscriptDifferenceLaw μ μ)) (u : ℝ) :
    measureCharacteristicSquareCurvature μ u =
      -(weightedCharFun (manuscriptDifferenceLaw μ μ) 2 u).re := by
  have hd := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u
    (weightedCharFun_hasDerivAt (manuscriptDifferenceLaw μ μ) 1
      (by simpa using hD1) hD2 u)).neg
  change HasDerivAt (fun v => -(weightedCharFun (manuscriptDifferenceLaw μ μ) 1 v).im) _ u at hd
  have he : (fun v => -(weightedCharFun (manuscriptDifferenceLaw μ μ) 1 v).im) =
      measureCharacteristicSquareSlope μ := by
    funext v
    exact (manuscript_measure_squareSlope_difference μ h1 hD1 v).symm
  rw [he] at hd
  have hd' : HasDerivAt (measureCharacteristicSquareSlope μ)
      (-(weightedCharFun (manuscriptDifferenceLaw μ μ) 2 u).re) u := by
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using hd
  exact (measureCharacteristicSquareSlope_hasDerivAt μ h1 h2 u).unique hd'

theorem manuscript_measure_squareThird_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (h3 : Integrable (fun x : ℝ => x ^ 3) μ)
    (hD1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw μ μ))
    (hD2 : Integrable (fun x : ℝ => x ^ 2) (manuscriptDifferenceLaw μ μ))
    (hD3 : Integrable (fun x : ℝ => x ^ 3) (manuscriptDifferenceLaw μ μ)) (u : ℝ) :
    measureCharacteristicSquareThird μ u =
      (weightedCharFun (manuscriptDifferenceLaw μ μ) 3 u).im := by
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u
    (weightedCharFun_hasDerivAt (manuscriptDifferenceLaw μ μ) 2 hD2 hD3 u)).neg
  change HasDerivAt (fun v => -(weightedCharFun (manuscriptDifferenceLaw μ μ) 2 v).re) _ u at hd
  have he : (fun v => -(weightedCharFun (manuscriptDifferenceLaw μ μ) 2 v).re) =
      measureCharacteristicSquareCurvature μ := by
    funext v
    exact (manuscript_measure_squareCurvature_difference μ h1 h2 hD1 hD2 v).symm
  rw [he] at hd
  have hd' : HasDerivAt (measureCharacteristicSquareCurvature μ)
      ((weightedCharFun (manuscriptDifferenceLaw μ μ) 3 u).im) u := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg] using hd
  exact (measureCharacteristicSquareCurvature_hasDerivAt μ h1 h2 h3 u).unique hd'


end BerryEsseen
