import BerryEsseen.JitterLowFrequency

/-! Exact CDF sandwich for the actual raw and normalized jittered sums. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem uniformJitter_cdf_between (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 < h) (u : ℝ) :
    cdf μ u ≤ cdf (μ ∗ uniformJitter h) (u + h / 2) ∧
      cdf (μ ∗ uniformJitter h) (u + h / 2) ≤ cdf μ (u + h) := by
  rw [uniformJitter_cdf_average μ hh u]
  have hm : Monotone (fun s => cdf μ (u + s)) :=
    (monotone_cdf μ).comp (monotone_const.add monotone_id)
  constructor
  · apply (le_div_iff₀ hh).2
    have hi := intervalIntegral.integral_mono_on (μ := volume) hh.le (intervalIntegrable_const (c := cdf μ u))
      hm.intervalIntegrable (fun s hs => monotone_cdf μ (by linarith [hs.1]))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hi
  · apply (div_le_iff₀ hh).2
    have hi := intervalIntegral.integral_mono_on (μ := volume) hh.le hm.intervalIntegrable
      (intervalIntegrable_const (c := cdf μ (u + h))) (fun s hs => monotone_cdf μ (by linarith [hs.2]))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hi

theorem spanJitter_cdf_sandwich (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 ≤ h) (t : ℝ) :
    cdf (μ ∗ spanJitter h) (t - h / 2) ≤ cdf μ t ∧
      cdf μ t ≤ cdf (μ ∗ spanJitter h) (t + h / 2) := by
  by_cases hhpos : 0 < h
  · simp only [spanJitter, if_pos hhpos]
    refine ⟨?_, (uniformJitter_cdf_between μ h hhpos t).1⟩
    convert (uniformJitter_cdf_between μ h hhpos (t - h)).2 using 1 <;> congr 1 <;> ring
  · have hz : h = 0 := le_antisymm (le_of_not_gt hhpos) hh
    subst h
    simp [spanJitter, Measure.conv_dirac]

theorem cdf_map_div_positive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : ℝ) (hs : 0 < s) (x : ℝ) :
    cdf (μ.map (fun y => y / s)) x = cdf μ (s * x) := by
  letI : IsProbabilityMeasure (μ.map (fun y => y / s)) := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [cdf_eq_real, cdf_eq_real, Measure.real, Measure.real, Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext y
  simp only [mem_preimage, mem_Iic, div_le_iff₀ hs, mul_comm]

def normalizedSumCDF (P : StandardizedLaw) (n : ℕ) (x : ℝ) : ℝ :=
  cdf (iidSumLaw P.measure n) (Real.sqrt (n : ℝ) * x)

theorem actual_normalized_jitter_sandwich (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : 0 ≤ h) (x : ℝ) :
    ((normalizedJitteredSumLaw P n h) (Iic (x - h / (2 * Real.sqrt (n : ℝ))))).toReal ≤ normalizedSumCDF P n x ∧
    normalizedSumCDF P n x ≤ ((normalizedJitteredSumLaw P n h) (Iic (x + h / (2 * Real.sqrt (n : ℝ))))).toReal := by
  letI := spanJitter_probability h
  letI := normalizedJitteredSumLaw_probability P n h
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  change (normalizedJitteredSumLaw P n h).real (Iic (x - h / (2 * Real.sqrt (n : ℝ)))) ≤ normalizedSumCDF P n x ∧
    normalizedSumCDF P n x ≤ (normalizedJitteredSumLaw P n h).real (Iic (x + h / (2 * Real.sqrt (n : ℝ))))
  rw [← cdf_eq_real, ← cdf_eq_real]
  unfold normalizedJitteredSumLaw normalizedSumCDF
  rw [cdf_map_div_positive _ _ hs, cdf_map_div_positive _ _ hs]
  convert spanJitter_cdf_sandwich (iidSumLaw P.measure n) h hh (Real.sqrt (n : ℝ) * x) using 1 <;>
    congr 2 <;> field_simp [hs.ne'] <;> ring

end BerryEsseen
