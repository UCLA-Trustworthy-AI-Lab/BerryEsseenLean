import BerryEsseen.BoundedCharacteristicPerturbation
import BerryEsseen.GlobalDerivativeBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Exact manuscript frequency budget after transporting two independent copies. -/
theorem manuscript_global_difference_derivative_budget (u : ℝ)
    (hu : |u| ≤ appendixGlobalCutoff + 1) :
    (1 + 26 * |u|) * ((2 : ℝ) * 10 ^ 5 * appendixRetention) ≤ appendixDerivativeError ∧
      (52 + 676 * |u|) * ((2 : ℝ) * 10 ^ 5 * appendixRetention) ≤ appendixDerivativeError := by
  have hT := appendix_global_cutoff_ge_ten
  have hτ := appendix_retention_bounds.1.le
  have hc : 2 * (52 + 676 * |u|) ≤ (10 : ℝ) ^ 5 * appendixGlobalCutoff ^ 2 := by
    nlinarith [sq_nonneg (appendixGlobalCutoff - 1)]
  have hb := mul_le_mul_of_nonneg_right hc (show 0 ≤ (10 : ℝ) ^ 5 * appendixRetention by positivity)
  have hc' : (52 + 676 * |u|) * ((2 : ℝ) * 10 ^ 5 * appendixRetention) ≤ appendixDerivativeError := by
    unfold appendixDerivativeError
    nlinarith only [hb]
  refine ⟨?_, hc'⟩
  have hsmall : 1 + 26 * |u| ≤ 52 + 676 * |u| := by linarith [abs_nonneg u]
  exact (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans hc'

theorem effective_global_derivative_bounds (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (u : ℝ) (hu : |u| ≤ appendixGlobalCutoff + 1) :
    |characteristicSquareSlope P u - measureCharacteristicSquareSlope Q u| ≤ appendixDerivativeError ∧
      |characteristicSquareCurvature P u - measureCharacteristicSquareCurvature Q u| ≤ appendixDerivativeError := by
  have hP13 : ∀ᵐ x ∂P.measure, |x| ≤ 13 := by filter_upwards [hP] with x hx; linarith
  have hb := manuscript_bounded_difference_derivative_transport K P.measure Q hP13 hQ u
  have he := manuscript_global_difference_derivative_budget u hu
  have hs := mul_le_mul_of_nonneg_left hW (show 0 ≤ 2 * (1 + 26 * |u|) by positivity)
  have hc := mul_le_mul_of_nonneg_left hW (show 0 ≤ 2 * (52 + 676 * |u|) by positivity)
  constructor
  · change |measureCharacteristicSquareSlope P.measure u - measureCharacteristicSquareSlope Q u| ≤ _
    nlinarith only [hb.1, he.1, hs]
  · change |measureCharacteristicSquareCurvature P.measure u - measureCharacteristicSquareCurvature Q u| ≤ _
    nlinarith only [hb.2, he.2, hc]

theorem effective_global_resonance_derivatives (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (r : ℝ) (hr : r ∈ resonanceSubgroup Q) (hrange : |r| ≤ appendixGlobalCutoff + 1) :
    |characteristicSquareSlope P r| ≤ appendixDerivativeError ∧
      characteristicSquareCurvature P r ≤ -1.9 := by
  have h1 := real_function_integrable_of_abs_le Q (fun x : ℝ => x) 13 measurable_id hQ
  have h2 := (bounded_shifted_power_integrable Q 13 0 (by norm_num) hQ 2).1
  simp only [sub_zero] at h2
  have hd := effective_global_derivative_bounds K P Q hP hQ hW r hrange
  rw [measureCharacteristicSquareSlope_at_resonance Q r hr, sub_zero] at hd
  rw [measureCharacteristicSquareCurvature_at_resonance Q h1 h2 r hr] at hd
  refine ⟨hd.1, ?_⟩
  have hupper := (abs_le.mp hd.2).2
  have hlower := (abs_le.mp hv).1
  nlinarith only [hupper, hlower, appendix_retention_tiny, appendix_derivative_error_small.2]

/-- Transfer the curvature on the entire cell using the Q third-derivative bound 60. -/
theorem manuscript_global_cell_curvature (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (r u : ℝ) (hr : r ∈ resonanceSubgroup Q)
    (hrange : |r| ≤ appendixGlobalCutoff + 1 / 1000) (hu : |u - r| ≤ 1 / 1000) :
    characteristicSquareCurvature P u ≤ -1 := by
  have hvsmall : (10 : ℝ) ^ 9 * appendixRetention ≤ 1 / 100 := by
    nlinarith only [appendix_retention_tiny]
  have hvupper : rawStdDev Q ^ 2 ≤ 1.1 := by linarith [(abs_le.mp hv).2]
  have h1 := real_function_integrable_of_abs_le Q (fun x : ℝ => x) 13 measurable_id hQ
  have h2 : Integrable (fun x : ℝ => x ^ 2) Q := by
    simpa using (bounded_shifted_power_integrable Q 13 0 (by norm_num) hQ 2).1
  have hcenter := measureCharacteristicSquareCurvature_at_resonance Q h1 h2 r hr
  have hQlip := (manuscript_measure_curvature_lipschitz_sixty Q hQ hvupper).dist_le_mul u r
  simp only [Real.dist_eq, NNReal.coe_ofNat] at hQlip
  have hurange : |u| ≤ appendixGlobalCutoff + 1 := by
    have hh := abs_add_le (u - r) r
    rw [sub_add_cancel] at hh
    linarith
  have htransfer := (effective_global_derivative_bounds K P Q hP hQ hW u hurange).2
  have hlow := (abs_le.mp hv).1
  have hQup := (abs_le.mp hQlip).2
  have hup := (abs_le.mp htransfer).2
  linarith [appendix_derivative_error_small.2]

theorem lattice_integer_resonance (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (h : ℝ) (hlat : IsLatticeSpan Q h) (j : ℤ) :
    (j : ℝ) * (2 * Real.pi / h) ∈ resonanceSubgroup Q := by
  have hr := latticeSpan_gives_resonance Q h hlat
  simpa only [zsmul_eq_mul] using (resonanceSubgroup Q).zsmul_mem hr j

end BerryEsseen
