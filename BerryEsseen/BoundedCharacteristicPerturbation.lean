import BerryEsseen.WeightedCharacteristicTransport
import BerryEsseen.MeasureCharacteristicDerivatives
import BerryEsseen.ManuscriptGlobalDifferenceTransport

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem real_inner_difference_bound (a b c d : ℂ) :
    |inner ℝ a b - inner ℝ c d| ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by
  have he : inner ℝ a b - inner ℝ c d = inner ℝ (a - c) b + inner ℝ c (b - d) := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _))

theorem bounded_weighted_characteristic_norm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0 ≤ R) (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (k : ℕ) (u : ℝ) :
    ‖weightedCharFun μ k u‖ ≤ R ^ k := by
  apply (norm_weightedCharFun_le μ k u).trans
  have hi := (bounded_shifted_power_integrable μ R 0 hR hμ k).2
  simp only [sub_zero] at hi
  have hb : ∫ x : ℝ, |x| ^ k ∂μ ≤ ∫ _ : ℝ, R ^ k ∂μ :=
    integral_mono_ae hi (integrable_const _) (by
      filter_upwards [hμ] with x hx
      exact pow_le_pow_left₀ (abs_nonneg x) hx k)
  simpa using hb

theorem measureCharFunDerivative_norm (μ : Measure ℝ) (u : ℝ) :
    ‖measureCharFunDerivative μ u‖ = ‖weightedCharFun μ 1 u‖ := by
  simp only [measureCharFunDerivative, norm_mul, Complex.norm_I, one_mul]

theorem measureCharFunDerivative_difference_norm (μ ν : Measure ℝ) (u : ℝ) :
    ‖measureCharFunDerivative μ u - measureCharFunDerivative ν u‖ =
      ‖weightedCharFun μ 1 u - weightedCharFun ν 1 u‖ := by
  simp only [measureCharFunDerivative, ← mul_sub, norm_mul, Complex.norm_I, one_mul]

theorem bounded_characteristic_square_derivative_transport (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (hν : ∀ᵐ x ∂ν, |x| ≤ 13) (u : ℝ) :
    |measureCharacteristicSquareSlope μ u - measureCharacteristicSquareSlope ν u| ≤
        2000 * (1 + |u|) * wassersteinOne μ ν ∧
      |measureCharacteristicSquareCurvature μ u - measureCharacteristicSquareCurvature ν u| ≤
        2000 * (1 + |u|) * wassersteinOne μ ν := by
  obtain ⟨h0, h1, h2⟩ := weighted_characteristic_transport_thirteen K μ ν hμ hν u
  have hiμ := real_function_integrable_of_abs_le μ (fun x : ℝ => x) 13 measurable_id hμ
  have hiν := real_function_integrable_of_abs_le ν (fun x : ℝ => x) 13 measurable_id hν
  have hw := wassersteinOne_nonneg K μ ν hiμ hiν
  have hm1 : ‖measureCharFunDerivative μ u‖ ≤ 13 := by
    rw [measureCharFunDerivative_norm]
    simpa using bounded_weighted_characteristic_norm μ 13 (by norm_num) hμ 1 u
  have hn1 : ‖measureCharFunDerivative ν u‖ ≤ 13 := by
    rw [measureCharFunDerivative_norm]
    simpa using bounded_weighted_characteristic_norm ν 13 (by norm_num) hν 1 u
  have hm2 : ‖weightedCharFun μ 2 u‖ ≤ 169 := by
    convert bounded_weighted_characteristic_norm μ 13 (by norm_num) hμ 2 u using 1 <;> norm_num
  have hn0 : ‖charFun ν u‖ ≤ 1 := norm_charFun_le_one u
  have hd1 : ‖measureCharFunDerivative μ u - measureCharFunDerivative ν u‖ ≤
      (1 + 13 * |u|) * wassersteinOne μ ν := by
    rwa [measureCharFunDerivative_difference_norm]
  have hs := real_inner_difference_bound (charFun μ u) (measureCharFunDerivative μ u)
    (charFun ν u) (measureCharFunDerivative ν u)
  have hs0 := mul_le_mul h0 hm1 (norm_nonneg _) (by positivity : 0 ≤ (1 + |u|) * wassersteinOne μ ν)
  have hs1 := mul_le_mul hn0 hd1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hs' : |inner ℝ (charFun μ u) (measureCharFunDerivative μ u) -
      inner ℝ (charFun ν u) (measureCharFunDerivative ν u)| ≤ (14 + 26 * |u|) * wassersteinOne μ ν := by
    nlinarith only [hs, hs0, hs1]
  have hc0 := real_inner_difference_bound (charFun μ u) (-weightedCharFun μ 2 u)
    (charFun ν u) (-weightedCharFun ν 2 u)
  simp only [norm_neg, neg_sub_neg, norm_sub_rev (weightedCharFun ν 2 u)] at hc0
  have hc01 := mul_le_mul h0 hm2 (norm_nonneg _) (by positivity : 0 ≤ (1 + |u|) * wassersteinOne μ ν)
  have hc02 := mul_le_mul hn0 h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hc0' : |inner ℝ (charFun μ u) (-weightedCharFun μ 2 u) -
      inner ℝ (charFun ν u) (-weightedCharFun ν 2 u)| ≤ (195 + 338 * |u|) * wassersteinOne μ ν := by
    nlinarith only [hc0, hc01, hc02]
  have hc1 := real_inner_difference_bound (measureCharFunDerivative μ u) (measureCharFunDerivative μ u)
    (measureCharFunDerivative ν u) (measureCharFunDerivative ν u)
  have hc11 := mul_le_mul hd1 hm1 (norm_nonneg _) (by positivity : 0 ≤ (1 + 13 * |u|) * wassersteinOne μ ν)
  have hc12 := mul_le_mul hn1 hd1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 13)
  have hc1' : |inner ℝ (measureCharFunDerivative μ u) (measureCharFunDerivative μ u) -
      inner ℝ (measureCharFunDerivative ν u) (measureCharFunDerivative ν u)| ≤
        (26 + 338 * |u|) * wassersteinOne μ ν := by
    nlinarith only [hc1, hc11, hc12]
  constructor
  · unfold measureCharacteristicSquareSlope
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_nonneg (abs_nonneg u) hw]
  · unfold measureCharacteristicSquareCurvature
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have he (a b c d : ℝ) : (a + b) - (c + d) = (a - c) + (b - d) := by ring
    rw [he]
    have ht := abs_add_le
      (inner ℝ (charFun μ u) (-weightedCharFun μ 2 u) - inner ℝ (charFun ν u) (-weightedCharFun ν 2 u))
      (inner ℝ (measureCharFunDerivative μ u) (measureCharFunDerivative μ u) -
        inner ℝ (measureCharFunDerivative ν u) (measureCharFunDerivative ν u))
    nlinarith [mul_nonneg (abs_nonneg u) hw]

/-- Pointwise Lipschitz budget for the original difference-variable slope integrand. -/
theorem manuscript_difference_slope_lipschitz (u x y : ℝ) (hx : |x| ≤ 26) (hy : |y| ≤ 26) :
    |(-x * Real.sin (u * x)) - (-y * Real.sin (u * y))| ≤
      (1 + 26 * |u|) * |x - y| := by
  have he : (-x * Real.sin (u * x)) - (-y * Real.sin (u * y)) =
      -(x - y) * Real.sin (u * x) - y * (Real.sin (u * x) - Real.sin (u * y)) := by ring
  rw [he]
  have ht := abs_sub (-(x - y) * Real.sin (u * x)) (y * (Real.sin (u * x) - Real.sin (u * y)))
  simp only [abs_mul, abs_neg] at ht
  have hs := Real.abs_sin_sub_sin_le (u * x) (u * y)
  rw [← mul_sub, abs_mul] at hs
  have h1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (u * x)) (abs_nonneg (x - y))
  have h2 := mul_le_mul hy hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 26)
  nlinarith only [ht, h1, h2]

/-- Pointwise Lipschitz budget for the original difference-variable curvature integrand. -/
theorem manuscript_difference_curvature_lipschitz (u x y : ℝ) (hx : |x| ≤ 26) (hy : |y| ≤ 26) :
    |(-x ^ 2 * Real.cos (u * x)) - (-y ^ 2 * Real.cos (u * y))| ≤
      (52 + 676 * |u|) * |x - y| := by
  have he : (-x ^ 2 * Real.cos (u * x)) - (-y ^ 2 * Real.cos (u * y)) =
      -(x ^ 2 - y ^ 2) * Real.cos (u * x) - y ^ 2 * (Real.cos (u * x) - Real.cos (u * y)) := by ring
  rw [he]
  have ht := abs_sub (-(x ^ 2 - y ^ 2) * Real.cos (u * x))
    (y ^ 2 * (Real.cos (u * x) - Real.cos (u * y)))
  simp only [abs_mul, abs_neg, abs_pow] at ht
  have hc := Real.abs_cos_sub_cos_le (u * x) (u * y)
  rw [← mul_sub, abs_mul] at hc
  have hp := square_difference_bounded 26 x y (by norm_num) hx hy
  have h1 := mul_le_mul hp (Real.abs_cos_le_one (u * x)) (abs_nonneg _) (by positivity : 0 ≤ 2 * 26 * |x - y|)
  have hy2 : |y| ^ 2 ≤ 676 :=
    (pow_le_pow_left₀ (abs_nonneg y) hy 2).trans_eq (by norm_num)
  have h2 := mul_le_mul hy2 hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 676)
  nlinarith only [ht, h1, h2]

/-- Original derivative transport: couple two independent copies, whose differences
lie in [-26,26], and apply the constants 1+26|u| and 52+676|u|. -/
theorem manuscript_bounded_difference_derivative_transport (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (hν : ∀ᵐ x ∂ν, |x| ≤ 13) (u : ℝ) :
    |measureCharacteristicSquareSlope μ u - measureCharacteristicSquareSlope ν u| ≤
        (1 + 26 * |u|) * (2 * wassersteinOne μ ν) ∧
      |measureCharacteristicSquareCurvature μ u - measureCharacteristicSquareCurvature ν u| ≤
        (52 + 676 * |u|) * (2 * wassersteinOne μ ν) := by
  have hDμ : ∀ᵐ x ∂manuscriptDifferenceLaw μ μ, |x| ≤ 26 := by
    convert manuscript_difference_bounded μ μ 13 13 hμ hμ using 1 <;> norm_num
  have hDν : ∀ᵐ x ∂manuscriptDifferenceLaw ν ν, |x| ≤ 26 := by
    convert manuscript_difference_bounded ν ν 13 13 hν hν using 1 <;> norm_num
  have hiμ (k : ℕ) : Integrable (fun x : ℝ => x ^ k) μ := by
    simpa using (bounded_shifted_power_integrable μ 13 0 (by norm_num) hμ k).1
  have hiν (k : ℕ) : Integrable (fun x : ℝ => x ^ k) ν := by
    simpa using (bounded_shifted_power_integrable ν 13 0 (by norm_num) hν k).1
  have hiDμ (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (manuscriptDifferenceLaw μ μ) := by
    simpa using (bounded_shifted_power_integrable _ 26 0 (by norm_num) hDμ k).1
  have hiDν (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (manuscriptDifferenceLaw ν ν) := by
    simpa using (bounded_shifted_power_integrable _ 26 0 (by norm_num) hDν k).1
  have hμ1 : Integrable (fun x : ℝ => x) μ := by simpa using hiμ 1
  have hν1 : Integrable (fun x : ℝ => x) ν := by simpa using hiν 1
  have hDμ1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw μ μ) := by simpa using hiDμ 1
  have hDν1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw ν ν) := by simpa using hiDν 1
  have hW := manuscript_difference_wasserstein_le_two μ ν hμ1 hν1

  have hs := (bounded_lipschitz_integral_transport K (manuscriptDifferenceLaw μ μ)
    (manuscriptDifferenceLaw ν ν) 26 (1 + 26 * |u|) (by norm_num) (by positivity) hDμ hDν
    (fun x => -x * Real.sin (u * x)) (manuscript_difference_slope_lipschitz u)).2.2
  have hc := (bounded_lipschitz_integral_transport K (manuscriptDifferenceLaw μ μ)
    (manuscriptDifferenceLaw ν ν) 26 (52 + 676 * |u|) (by norm_num) (by positivity) hDμ hDν
    (fun x => -x ^ 2 * Real.cos (u * x)) (manuscript_difference_curvature_lipschitz u)).2.2
  simp only [neg_mul, integral_neg] at hs hc
  constructor
  · rw [manuscript_measure_squareSlope_difference μ hμ1 hDμ1,
      manuscript_measure_squareSlope_difference ν hν1 hDν1,
      manuscript_weightedCharFun_im _ 1 (hiDμ 1), manuscript_weightedCharFun_im _ 1 (hiDν 1)]
    simp only [pow_one]
    exact hs.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  · rw [manuscript_measure_squareCurvature_difference μ hμ1 (hiμ 2) hDμ1 (hiDμ 2),
      manuscript_measure_squareCurvature_difference ν hν1 (hiν 2) hDν1 (hiDν 2),
      manuscript_weightedCharFun_re _ 2 (hiDμ 2), manuscript_weightedCharFun_re _ 2 (hiDν 2)]
    exact hc.trans (mul_le_mul_of_nonneg_left hW (by positivity))

end BerryEsseen
