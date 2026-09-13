import BerryEsseen.UniformJitter

/-! The two exact weighted uniform-jitter identities printed in the proof of
`lem:accumulated-cluster-variance`. The backward identity retains the atom at x.
The quarter-interval improvements are obtained from these identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

theorem manuscript_unit_uniform_cdf (t : ℝ) :
    cdf (uniformJitter 1) t = max 0 (min t (1 / 2) + 1 / 2) := by
  letI := uniformJitter_probability (h := 1) (by norm_num)
  rw [cdf_eq_real]
  have hset : Iic t ∩ Icc (-(1 : ℝ) / 2) (1 / 2) =
      Icc (-(1 : ℝ) / 2) (min t (1 / 2)) := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  simp only [Measure.real, uniformJitter, one_div_one, ENNReal.ofReal_one,
    one_smul, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc,
    ENNReal.toReal_ofReal']
  rw [max_comm]
  congr 1
  ring

theorem manuscript_uniform_forward_weight_pointwise (x y : ℝ) :
    cdf (uniformJitter 1) (x + 1 / 2 - y) - (Iic x).indicator (fun _ => (1 : ℝ)) y =
      (Ioo x (x + 1)).indicator (fun y => x + 1 - y) y := by
  rw [manuscript_unit_uniform_cdf]
  simp only [indicator_apply, mem_Iic, mem_Ioo]
  by_cases hxy : y ≤ x
  · rw [if_pos hxy, if_neg (by intro h; linarith [h.1])]
    rw [min_eq_right (by linarith), max_eq_right (by norm_num)]
    norm_num
  · rw [if_neg hxy]
    by_cases hy : y < x + 1
    · rw [if_pos ⟨lt_of_not_ge hxy, hy⟩, min_eq_left (by linarith),
        max_eq_right (by linarith)]
      ring
    · rw [if_neg (by tauto), min_eq_left (by linarith), max_eq_left (by linarith)]
      ring

theorem manuscript_uniform_backward_weight_pointwise (x y : ℝ) :
    (Iic x).indicator (fun _ => (1 : ℝ)) y - cdf (uniformJitter 1) (x - 1 / 2 - y) =
      (Ioo (x - 1) x).indicator (fun y => y - x + 1) y +
        ({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y := by
  rw [manuscript_unit_uniform_cdf]
  simp only [indicator_apply, mem_Iic, mem_Ioo, mem_singleton_iff]
  by_cases hxy : y ≤ x
  · rw [if_pos hxy]
    by_cases he : y = x
    · subst y
      norm_num
    · rw [if_neg he]
      by_cases hy : x - 1 < y
      · rw [if_pos ⟨hy, lt_of_le_of_ne hxy he⟩, min_eq_left (by linarith),
          max_eq_right (by linarith)]
        ring
      · rw [if_neg (by tauto), min_eq_right (by linarith), max_eq_right (by norm_num)]
        norm_num
  · rw [if_neg hxy, if_neg (by intro h; exact hxy h.2.le),
      if_neg (by intro h; subst y; exact hxy le_rfl), min_eq_left (by linarith),
      max_eq_left (by linarith)]
    norm_num

theorem manuscript_uniform_forward_weight_integrable (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    Integrable ((Ioo x (x + 1)).indicator (fun y => x + 1 - y)) μ := by
  have hi := (translated_cdf_integrable μ (uniformJitter 1) (x + 1 / 2)).sub
    ((integrable_const (1 : ℝ)).indicator (measurableSet_Iic (a := x)))
  exact hi.congr (Filter.Eventually.of_forall (manuscript_uniform_forward_weight_pointwise x))

theorem manuscript_uniform_backward_weight_integrable (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    Integrable ((Ioo (x - 1) x).indicator (fun y => y - x + 1)) μ := by
  have hi := (((integrable_const (1 : ℝ)).indicator (measurableSet_Iic (a := x))).sub
    (translated_cdf_integrable μ (uniformJitter 1) (x - 1 / 2))).sub
    ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton x))
  apply hi.congr
  filter_upwards [] with y
  simp only [Pi.sub_apply]
  rw [manuscript_uniform_backward_weight_pointwise]
  ring

/-- First printed identity: no continuity or absence of atoms is assumed. -/
theorem manuscript_uniform_forward_weighted_identity (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (μ ∗ uniformJitter 1) (x + 1 / 2) - cdf μ x =
      ∫ y, (Ioo x (x + 1)).indicator (fun y => x + 1 - y) y ∂μ := by
  letI := uniformJitter_probability (h := 1) (by norm_num)
  rw [cdf_convolution_integral, cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  change (∫ y, cdf (uniformJitter 1) (x + 1 / 2 - y) ∂μ) -
    (∫ y, (Iic x).indicator (fun _ => (1 : ℝ)) y ∂μ) = _
  rw [← integral_sub (translated_cdf_integrable μ (uniformJitter 1) (x + 1 / 2))
      ((integrable_const (1 : ℝ)).indicator (measurableSet_Iic (a := x)))]
  exact integral_congr_ae (Filter.Eventually.of_forall (manuscript_uniform_forward_weight_pointwise x))

/-- Second printed identity, including precisely the mass of the singleton x. -/
theorem manuscript_uniform_backward_weighted_identity (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf μ x - cdf (μ ∗ uniformJitter 1) (x - 1 / 2) =
      (∫ y, (Ioo (x - 1) x).indicator (fun y => y - x + 1) y ∂μ) + μ.real {x} := by
  letI := uniformJitter_probability (h := 1) (by norm_num)
  rw [cdf_convolution_integral, cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  change (∫ y, (Iic x).indicator (fun _ => (1 : ℝ)) y ∂μ) -
    (∫ y, cdf (uniformJitter 1) (x - 1 / 2 - y) ∂μ) = _
  rw [← integral_sub ((integrable_const (1 : ℝ)).indicator (measurableSet_Iic (a := x)))
      (translated_cdf_integrable μ (uniformJitter 1) (x - 1 / 2))]
  calc
    _ = ∫ y, ((Ioo (x - 1) x).indicator (fun y => y - x + 1) y +
        ({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (manuscript_uniform_backward_weight_pointwise x))
    _ = _ := by
      rw [integral_add (manuscript_uniform_backward_weight_integrable μ x)
        ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton x)),
        integral_indicator_const (1 : ℝ) (measurableSet_singleton x)]
      simp

/-- The manuscript's right quarter-interval improvement follows by bounding
its weight below by one half inside that open interval. -/
theorem manuscript_uniform_forward_quarter_gap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    (1 / 2 : ℝ) * μ.real (Ioo (x + 1 / 4) (x + 1 / 2)) ≤
      cdf (μ ∗ uniformJitter 1) (x + 1 / 2) - cdf μ x := by
  rw [manuscript_uniform_forward_weighted_identity]
  calc
    _ = ∫ y, (Ioo (x + 1 / 4) (x + 1 / 2)).indicator
        (fun _ => (1 / 2 : ℝ)) y ∂μ := by
      rw [integral_indicator_const _ measurableSet_Ioo]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := by
      apply integral_mono ((integrable_const (1 / 2 : ℝ)).indicator measurableSet_Ioo)
        (manuscript_uniform_forward_weight_integrable μ x)
      intro y
      by_cases hy : y ∈ Ioo (x + 1 / 4) (x + 1 / 2)
      · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ Ioo x (x + 1) from
          ⟨by linarith [hy.1], by linarith [hy.2]⟩)]
        linarith [hy.2]
      · rw [indicator_of_notMem hy]
        by_cases hw : y ∈ Ioo x (x + 1)
        · rw [indicator_of_mem hw]
          linarith [hw.2]
        · rw [indicator_of_notMem hw]

/-- The backward quarter-interval bound is derived from the exact identity
and the nonnegative atom term; no atomless hypothesis is introduced. -/
theorem manuscript_uniform_backward_quarter_gap (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    (1 / 2 : ℝ) * μ.real (Ioo (x - 1 / 2) (x - 1 / 4)) ≤
      cdf μ x - cdf (μ ∗ uniformJitter 1) (x - 1 / 2) := by
  rw [manuscript_uniform_backward_weighted_identity]
  have hweight : (1 / 2 : ℝ) * μ.real (Ioo (x - 1 / 2) (x - 1 / 4)) ≤
      ∫ y, (Ioo (x - 1) x).indicator (fun y => y - x + 1) y ∂μ := by
    calc
      _ = ∫ y, (Ioo (x - 1 / 2) (x - 1 / 4)).indicator
          (fun _ => (1 / 2 : ℝ)) y ∂μ := by
        rw [integral_indicator_const _ measurableSet_Ioo]
        simp only [smul_eq_mul]
        ring
      _ ≤ _ := by
        apply integral_mono ((integrable_const (1 / 2 : ℝ)).indicator measurableSet_Ioo)
          (manuscript_uniform_backward_weight_integrable μ x)
        intro y
        by_cases hy : y ∈ Ioo (x - 1 / 2) (x - 1 / 4)
        · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ Ioo (x - 1) x from
            ⟨by linarith [hy.1], by linarith [hy.2]⟩)]
          linarith [hy.1]
        · rw [indicator_of_notMem hy]
          by_cases hw : y ∈ Ioo (x - 1) x
          · rw [indicator_of_mem hw]
            linarith [hw.1]
          · rw [indicator_of_notMem hw]
  exact hweight.trans (le_add_of_nonneg_right (measureReal_nonneg))

end BerryEsseen
