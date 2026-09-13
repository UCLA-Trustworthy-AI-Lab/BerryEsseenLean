import BerryEsseen.VariationalExtremizer

/-! Reflection selects a positive CDF discrepancy, including distributions
with atoms. No continuity of the sum CDF is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BerryEsseen

def reflectedLaw (P : StandardizedLaw) : StandardizedLaw where
  measure := P.measure.map (fun x => -x)
  probability := Measure.isProbabilityMeasure_map (by fun_prop)
  first_integrable := (integrable_map_measure (by fun_prop) (by fun_prop)).2 (by
    simpa only [Function.comp_def] using P.first_integrable.neg)
  second_integrable := (integrable_map_measure (by fun_prop) (by fun_prop)).2 (by
    simpa only [Function.comp_def, neg_sq] using P.second_integrable)
  third_integrable := (integrable_map_measure (by fun_prop) (by fun_prop)).2 (by
    simpa only [Function.comp_def, abs_neg] using P.third_integrable)
  mean_zero := by
    rw [integral_map (by fun_prop) (by fun_prop), integral_neg, P.mean_zero, neg_zero]
  second_one := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simpa only [neg_sq] using P.second_one

theorem reflectedLaw_thirdMoment (P : StandardizedLaw) : thirdMoment (reflectedLaw P) = thirdMoment P := by
  unfold thirdMoment reflectedLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_neg]

theorem iidSumLaw_reflected (P : StandardizedLaw) (n : ℕ) :
    iidSumLaw (reflectedLaw P).measure n = (iidSumLaw P.measure n).map (fun x => -x) := by
  have h := iidSumLaw_standardizedMeasure P.measure 0 (-1) n
  simpa only [standardizedMeasure, mul_zero, sub_zero, div_neg, div_one] using h

theorem reflected_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cdf (μ.map (fun x => -x)) (-t) = μ.real (Ici t) := by
  letI : IsProbabilityMeasure (μ.map (fun x => -x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [cdf_eq_real]
  change ((μ.map (fun x => -x)) (Iic (-t))).toReal = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext x
  simp

theorem cdf_add_reflected_cdf_ge_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    1 ≤ cdf μ t + cdf (μ.map (fun x => -x)) (-t) := by
  rw [reflected_cdf, cdf_eq_real]
  have h := measureReal_union_le (μ := μ) (Iic t) (Ici t)
  simpa only [Iic_union_Ici, probReal_univ] using h

theorem normalCDF_reflection (t : ℝ) : normalCDF (-t) = 1 - normalCDF t := by
  letI := noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have h := measureReal_union_add_inter₀ (μ := gaussianReal 0 1) (s := Iic t)
    (measurableSet_Ici (a := t)).nullMeasurableSet
  have hr := reflected_cdf (gaussianReal 0 1) t
  rw [gaussianReal_map_neg, neg_zero, cdf_eq_real] at hr
  have hzero : (gaussianReal 0 1).real {t} = 0 := by
    simp only [Measure.real, measure_singleton, ENNReal.toReal_zero]
  simp only [Iic_union_Ici, Iic_inter_Ici, Icc_self, probReal_univ, hzero, add_zero] at h
  change normalCDF (-t) = (gaussianReal 0 1).real (Ici t) at hr
  change _ = 1 - (gaussianReal 0 1).real (Iic t)
  linarith

theorem neg_signedRatio_le_reflected (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    -signedRatio P n t ≤ signedRatio (reflectedLaw P) n (-t) := by
  have h := cdf_add_reflected_cdf_ge_one (iidSumLaw P.measure (n + 1)) t
  unfold signedRatio
  rw [reflectedLaw_thirdMoment, iidSumLaw_reflected, neg_div, normalCDF_reflection]
  rw [← neg_div]
  apply (div_le_div_iff_of_pos_right (thirdMoment_pos P)).2
  have hs : 0 ≤ Real.sqrt (n + 1 : ℝ) := Real.sqrt_nonneg _
  nlinarith

theorem exists_positive_signedRatio_dominating (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    ∃ (Q : StandardizedLaw) (u : ℝ), |signedRatio P n t| ≤ signedRatio Q n u := by
  by_cases h : 0 ≤ signedRatio P n t
  · exact ⟨P, t, (abs_of_nonneg h).le⟩
  · exact ⟨reflectedLaw P, -t, by
      rw [abs_of_neg (lt_of_not_ge h)]
      exact neg_signedRatio_le_reflected P n t⟩

theorem exists_signedRatio_ge_normalized (P : StandardizedLaw) (n : ℕ) (x : ℝ) :
    ∃ (Q : StandardizedLaw) (t : ℝ), normalizedDiscrepancy P (n + 1) x ≤ signedRatio Q n t := by
  obtain ⟨Q, t, h⟩ := exists_positive_signedRatio_dominating P n (Real.sqrt (n + 1 : ℝ) * x)
  rw [abs_signedRatio_eq_normalized] at h
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ x hs] at h
  exact ⟨Q, t, h⟩

theorem extremal_positive_approximation (H : ClassicalBerryEsseenBounds) (n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : StandardizedLaw) (t : ℝ), extremalConstant (n + 1) - ε < signedRatio P n t ∧
      signedRatio P n t ≤ extremalConstant (n + 1) := by
  have hex : ∃ r ∈ extremalValues (n + 1), extremalConstant (n + 1) - ε < r := by
    apply exists_lt_of_lt_csSup (extremalValues_nonempty (n + 1))
    change extremalConstant (n + 1) - ε < extremalConstant (n + 1)
    linarith
  obtain ⟨r, ⟨P, x, rfl⟩, hr⟩ := hex
  obtain ⟨Q, t, hQ⟩ := exists_signedRatio_ge_normalized P n x
  exact ⟨Q, t, hr.trans_le hQ, signedRatio_le_extremalConstant H Q n t⟩

end BerryEsseen
