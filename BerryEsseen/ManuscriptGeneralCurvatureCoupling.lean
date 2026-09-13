import BerryEsseen.ManuscriptGeneralCouplingLimits

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_standardized_curvature_difference (P : StandardizedLaw) (u : ℝ) :
    characteristicSquareCurvature P u =
      -(∫ x, x ^ 2 * Real.cos (u * x) ∂manuscriptDifferenceLaw P.measure P.measure) := by
  have hD1 : Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw P.measure P.measure) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    exact (P.first_integrable.comp_fst P.measure).sub (P.first_integrable.comp_snd P.measure)
  have hD2 := manuscriptDifferenceLaw_second_integrable P
  have hh := manuscript_measure_squareCurvature_difference P.measure P.first_integrable
    P.second_integrable hD1 hD2 u
  rw [manuscript_weightedCharFun_re _ 2 hD2] at hh
  exact hh

theorem manuscript_curvature_coupled_fst (P : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (hf : π.map Prod.fst = P.measure) (u : ℝ) :
    characteristicSquareCurvature P u =
      -(∫ z, manuscriptCoupledD z ^ 2 * Real.cos (u * manuscriptCoupledD z) ∂π.prod π) := by
  rw [manuscript_standardized_curvature_difference,
    ← manuscript_double_coupling_fst π P.measure hf,
    integral_map (by unfold manuscriptCoupledD; fun_prop) (by fun_prop)]

theorem manuscript_curvature_coupled_snd (P : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (hs : π.map Prod.snd = P.measure) (u : ℝ) :
    characteristicSquareCurvature P u =
      -(∫ z, manuscriptCoupledLimitD z ^ 2 * Real.cos (u * manuscriptCoupledLimitD z) ∂π.prod π) := by
  rw [manuscript_standardized_curvature_difference,
    ← manuscript_double_coupling_snd π P.measure hs,
    integral_map (by unfold manuscriptCoupledLimitD; fun_prop) (by fun_prop)]

theorem manuscript_cos_difference_bound (u a b T : ℝ) (hu : |u| ≤ T) :
    |Real.cos (u * a) - Real.cos (u * b)| ≤ min 2 (T * |a - b|) := by
  apply le_min
  · exact (abs_sub _ _).trans (by linarith [Real.abs_cos_le_one (u * a), Real.abs_cos_le_one (u * b)])
  · have h := Real.abs_cos_sub_cos_le (u * a) (u * b)
    rw [← mul_sub, abs_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hu (abs_nonneg _))

/-- The exact two-error decomposition displayed in the manuscript. -/
theorem manuscript_curvature_integrand_difference (u a b T : ℝ) (hu : |u| ≤ T) :
    |a ^ 2 * Real.cos (u * a) - b ^ 2 * Real.cos (u * b)| ≤
      |a ^ 2 - b ^ 2| + b ^ 2 * min 2 (T * |a - b|) := by
  have he : a ^ 2 * Real.cos (u * a) - b ^ 2 * Real.cos (u * b) =
      (a ^ 2 - b ^ 2) * Real.cos (u * a) +
        b ^ 2 * (Real.cos (u * a) - Real.cos (u * b)) := by ring
  rw [he]
  have h1 : |(a ^ 2 - b ^ 2) * Real.cos (u * a)| ≤ |a ^ 2 - b ^ 2| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |b ^ 2 * (Real.cos (u * a) - Real.cos (u * b))| ≤
      b ^ 2 * min 2 (T * |a - b|) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg b)]
    exact mul_le_mul_of_nonneg_left (manuscript_cos_difference_bound u a b T hu) (sq_nonneg b)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem manuscript_square_factor_truncation (a b T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) :
    b ^ 2 * min 2 (T * |a - b|) ≤
      2 * (b ^ 2 - min (b ^ 2) A) + A * T * |a - b| := by
  have htail := mul_le_mul_of_nonneg_left (min_le_left 2 (T * |a - b|))
    (sub_nonneg.mpr (min_le_left (b ^ 2) A))
  have hcap := mul_le_mul (min_le_right (b ^ 2) A) (min_le_right 2 (T * |a - b|))
    (le_min (by norm_num) (mul_nonneg hT (abs_nonneg _))) hA
  nlinarith only [htail, hcap]

theorem manuscript_coupled_square_cos_integrable (μ : Measure ManuscriptDoubleCoupling)
    (D : ManuscriptDoubleCoupling → ℝ) (hD : Measurable D)
    (hi : Integrable (fun z => D z ^ 2) μ) (u : ℝ) :
    Integrable (fun z => D z ^ 2 * Real.cos (u * D z)) μ := by
  apply hi.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)

theorem manuscript_curvature_coupling_bound (P Q : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hf : π.map Prod.fst = P.measure) (hs : π.map Prod.snd = Q.measure)
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π)
    (T A u : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hu : |u| ≤ T) :
    |characteristicSquareCurvature P u - characteristicSquareCurvature Q u| ≤
      (∫ z, |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2| ∂π.prod π) +
      2 * manuscriptSquareTail (manuscriptDifferenceLaw Q.measure Q.measure) A +
      A * T * (∫ z, |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂π.prod π) := by
  have hfst2 := (manuscript_double_coupling_second_fst P π hf).1
  have hsnd2 := (manuscript_double_coupling_second_snd Q π hs).1
  have hfi := manuscript_coupled_square_cos_integrable (π.prod π) manuscriptCoupledD
    (by unfold manuscriptCoupledD; fun_prop) hfst2 u
  have hsi := manuscript_coupled_square_cos_integrable (π.prod π) manuscriptCoupledLimitD
    (by unfold manuscriptCoupledLimitD; fun_prop) hsnd2 u
  have hsq := manuscript_double_coupling_square_difference_integrable P Q π hf hs
  have hab := manuscript_double_coupling_abs_error_integrable π hi
  have hmap := manuscript_double_coupling_snd π Q.measure hs
  have htail : Integrable (fun z => manuscriptCoupledLimitD z ^ 2 - min (manuscriptCoupledLimitD z ^ 2) A) (π.prod π) := by
    have hh := manuscript_square_tail_integrable _ (manuscriptDifferenceLaw_second_integrable Q) A hA
    rw [← hmap] at hh
    exact (integrable_map_measure (by fun_prop) (by unfold manuscriptCoupledLimitD; fun_prop)).mp hh
  have htailint : (∫ z, manuscriptCoupledLimitD z ^ 2 - min (manuscriptCoupledLimitD z ^ 2) A ∂π.prod π) =
      manuscriptSquareTail (manuscriptDifferenceLaw Q.measure Q.measure) A := by
    unfold manuscriptSquareTail
    rw [← hmap, integral_map (by unfold manuscriptCoupledLimitD; fun_prop) (by fun_prop)]
  rw [manuscript_curvature_coupled_fst P π hf, manuscript_curvature_coupled_snd Q π hs,
    neg_sub_neg, abs_sub_comm, ← integral_sub hfi hsi]
  calc
    _ ≤ ∫ z, |manuscriptCoupledD z ^ 2 * Real.cos (u * manuscriptCoupledD z) -
        manuscriptCoupledLimitD z ^ 2 * Real.cos (u * manuscriptCoupledLimitD z)| ∂π.prod π := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => manuscriptCoupledD z ^ 2 * Real.cos (u * manuscriptCoupledD z) -
          manuscriptCoupledLimitD z ^ 2 * Real.cos (u * manuscriptCoupledLimitD z)) (μ := π.prod π)
    _ ≤ ∫ z, |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2| +
        2 * (manuscriptCoupledLimitD z ^ 2 - min (manuscriptCoupledLimitD z ^ 2) A) +
        (A * T) * |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂π.prod π := by
      apply integral_mono (hfi.sub hsi).abs ((hsq.add (htail.const_mul 2)).add (hab.const_mul (A * T)))
      intro z
      have hh := manuscript_curvature_integrand_difference u (manuscriptCoupledD z) (manuscriptCoupledLimitD z) T hu
      have ht := manuscript_square_factor_truncation (manuscriptCoupledD z) (manuscriptCoupledLimitD z) T A hT hA
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith
    _ = _ := by
      have hsum : Integrable (fun z => |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2| +
          2 * (manuscriptCoupledLimitD z ^ 2 - min (manuscriptCoupledLimitD z ^ 2) A)) (π.prod π) :=
        hsq.add (htail.const_mul 2)
      rw [integral_add hsum (hab.const_mul (A * T)),
        integral_add hsq (htail.const_mul 2), integral_const_mul, integral_const_mul, htailint]

end BerryEsseen
