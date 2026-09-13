import BerryEsseen.ManuscriptCenteredTransport

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem integral_difference_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (C : ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, |f x - g x| ≤ C) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ C := by
  rw [← integral_sub hf hg]
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x - g x)
    (by simpa only [Real.norm_eq_abs] using h)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

theorem bounded_transport_moment_errors (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (w : ℝ) (hw : w ∈ Icc 0 1)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hW : wassersteinOne P.measure Q ≤ w) :
    |rawMean Q| ≤ w ∧ |rawStdDev Q ^ 2 - 1| ≤ 27 * w ∧
      |rawThirdAbsoluteMoment Q - thirdMoment P| ≤ 1176 * w ∧
      |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 1176 * w := by
  have hP13 : ∀ᵐ x ∂P.measure, |x| ≤ 13 := by filter_upwards [hP] with x hx; linarith
  have hiQ := real_function_integrable_of_abs_le Q (fun x : ℝ => x) 13 measurable_id hQ
  have hm : |rawMean Q| ≤ w := by
    have h := (lipschitz_integral_abs_le_wassersteinOne K P.measure Q P.first_integrable hiQ
      (fun x => x) LipschitzWith.id).trans hW
    simpa only [P.mean_zero, zero_sub, abs_neg, rawMean] using h
  have hm1 : |rawMean Q| ≤ 1 := hm.trans hw.2
  have hm2 : rawMean Q ^ 2 ≤ w ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hm
    simpa only [← sq, sq_abs] using hh
  have hsecond := bounded_lipschitz_integral_transport K P.measure Q 13 26 (by norm_num)
    (by norm_num) hP13 hQ (fun x => x ^ 2) (by
      intro x y hx hy
      convert square_difference_bounded 13 x y (by norm_num) hx hy using 1 <;> norm_num)
  have hsecondW : |(∫ x, x ^ 2 ∂Q) - 1| ≤ 26 * w := by
    have h := hsecond.2.2.trans (mul_le_mul_of_nonneg_left hW (by norm_num))
    rw [P.second_one, abs_sub_comm] at h
    exact h
  have hvExact : |rawStdDev Q ^ 2 - 1| ≤ 26 * w + w ^ 2 := by
    rw [raw_centered_variance_formula Q hiQ hsecond.2.1]
    have hh := abs_sub ((∫ x, x ^ 2 ∂Q) - 1) (rawMean Q ^ 2)
    rw [abs_of_nonneg (sq_nonneg (rawMean Q))] at hh
    rw [show (∫ x, x ^ 2 ∂Q) - rawMean Q ^ 2 - 1 =
      ((∫ x, x ^ 2 ∂Q) - 1) - rawMean Q ^ 2 by ring]
    linarith
  have hv : |rawStdDev Q ^ 2 - 1| ≤ 27 * w :=
    hvExact.trans (by nlinarith [mul_le_mul_of_nonneg_left hw.2 hw.1])
  let C := manuscriptCenteredMeasure Q (rawMean Q)
  letI : IsProbabilityMeasure C := Measure.isProbabilityMeasure_map (by fun_prop)
  have hcentered : wassersteinOne P.measure C ≤ 2 * w :=
    manuscript_centered_transport_two_w P Q w hiQ hW hm
  have hP14 : ∀ᵐ x ∂P.measure, |x| ≤ 14 := by
    filter_upwards [hP] with x hx
    linarith
  have hC14 : ∀ᵐ x ∂C, |x| ≤ 14 := by
    apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).mpr
    filter_upwards [hQ] with x hx
    exact (abs_sub x (rawMean Q)).trans (by linarith)
  have hcube := bounded_lipschitz_integral_transport K P.measure C 14 588
    (by norm_num) (by norm_num) hP14 hC14 (fun x : ℝ => x ^ 3) (by
      intro x y hx hy
      convert cube_difference_bounded 14 x y (by norm_num) hx hy using 1 <;> norm_num)
  have habscube := bounded_lipschitz_integral_transport K P.measure C 14 588
    (by norm_num) (by norm_num) hP14 hC14 (fun x : ℝ => |x| ^ 3) (by
      intro x y hx hy
      convert absolute_cube_difference_bounded 14 x y (by norm_num) hx hy using 1 <;> norm_num)
  have hcW := hcube.2.2.trans (mul_le_mul_of_nonneg_left hcentered (by norm_num))
  have haW := habscube.2.2.trans (mul_le_mul_of_nonneg_left hcentered (by norm_num))
  change |(∫ x, x ^ 3 ∂P.measure) - (∫ x, x ^ 3 ∂Q.map (fun x => x - rawMean Q))| ≤ _ at hcW
  change |(∫ x, |x| ^ 3 ∂P.measure) - (∫ x, |x| ^ 3 ∂Q.map (fun x => x - rawMean Q))| ≤ _ at haW
  rw [integral_map (by fun_prop) (by fun_prop), abs_sub_comm] at hcW haW
  refine ⟨hm, hv, ?_, ?_⟩
  · change |(∫ x, |x - rawMean Q| ^ 3 ∂Q) - (∫ x, |x| ^ 3 ∂P.measure)| ≤ _
    nlinarith only [haW]
  · change |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - (∫ x, x ^ 3 ∂P.measure)| ≤ _
    nlinarith only [hcW]

end BerryEsseen
