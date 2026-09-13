import BerryEsseen.ReflectionBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def rawMean (μ : Measure ℝ) : ℝ := ∫ x, x ∂μ
def rawStdDev (μ : Measure ℝ) : ℝ := Real.sqrt (∫ x, (x - rawMean μ) ^ 2 ∂μ)
def rawThirdAbsoluteMoment (μ : Measure ℝ) : ℝ := ∫ x, |x - rawMean μ| ^ 3 ∂μ
def rawNormalizedDiscrepancy (μ : Measure ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) / (rawThirdAbsoluteMoment μ / rawStdDev μ ^ 3) *
    |cdf (iidSumLaw μ n) ((n : ℝ) * rawMean μ + rawStdDev μ * Real.sqrt (n : ℝ) * x) - normalCDF x|
def rawNormalizedConstant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  sSup (range (rawNormalizedDiscrepancy μ n))

theorem inverse_standardized_representation (μ : Measure ℝ) (Z : StandardizedLaw)
    (m σ : ℝ) (hσ : 0 < σ) (hmap : Z.measure = standardizedMeasure μ m σ) :
    μ = Z.measure.map (fun x => σ * x + m) := by
  rw [hmap, standardizedMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => σ * ((x - m) / σ) + m) = id := by
    funext x
    dsimp
    field_simp
    <;> ring
  change μ = μ.map (fun x => σ * ((x - m) / σ) + m)
  rw [he, Measure.map_id]

theorem raw_moments_of_standardized_representation (μ : Measure ℝ) (Z : StandardizedLaw)
    (m σ : ℝ) (hσ : 0 < σ) (hmap : Z.measure = standardizedMeasure μ m σ) :
    rawMean μ = m ∧ rawStdDev μ = σ ∧
      rawThirdAbsoluteMoment μ = σ ^ 3 * thirdMoment Z := by
  have hinv := inverse_standardized_representation μ Z m σ hσ hmap
  have hm : rawMean μ = m := by
    unfold rawMean
    rw [hinv, integral_map (by fun_prop) (by fun_prop),
      integral_add (Z.first_integrable.const_mul σ) (integrable_const m),
      integral_const_mul, Z.mean_zero]
    simp
  refine ⟨hm, ?_, ?_⟩
  · unfold rawStdDev
    rw [hm, hinv, integral_map (by fun_prop) (by fun_prop)]
    simp only [add_sub_cancel_right, mul_pow]
    rw [integral_const_mul, Z.second_one, mul_one, Real.sqrt_sq hσ.le]
  · unfold rawThirdAbsoluteMoment
    rw [hm, hinv, integral_map (by fun_prop) (by fun_prop)]
    simp only [add_sub_cancel_right, abs_mul, abs_of_pos hσ, mul_pow]
    exact integral_const_mul _ _

theorem rawNormalizedDiscrepancy_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hmap : Z.measure = standardizedMeasure μ m σ) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    rawNormalizedDiscrepancy μ n x = normalizedDiscrepancy Z n x := by
  obtain ⟨hm, hs, hthird⟩ := raw_moments_of_standardized_representation μ Z m σ hσ hmap
  rw [rawNormalizedDiscrepancy, hm, hs, hthird,
    mul_div_cancel_left₀ (thirdMoment Z) (pow_ne_zero 3 hσ.ne'),
    normalizedDiscrepancy_eq_iid_error Z n hn, normalizedIIDSumLaw_cdf Z n hn, hmap]
  have hc := standardized_sum_cdf μ m σ hσ n
    ((n : ℝ) * m + σ * Real.sqrt (n : ℝ) * x)
  have he : ((n : ℝ) * m + σ * Real.sqrt (n : ℝ) * x - (n : ℝ) * m) / σ =
      Real.sqrt (n : ℝ) * x := by field_simp; ring
  rw [he] at hc
  rw [hc]

theorem rawNormalizedConstant_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hmap : Z.measure = standardizedMeasure μ m σ) (n : ℕ) (hn : 1 ≤ n) :
    rawNormalizedConstant μ n = sSup (range (normalizedDiscrepancy Z n)) := by
  unfold rawNormalizedConstant
  congr 2
  funext x
  exact rawNormalizedDiscrepancy_eq μ Z m σ hσ hmap n hn x

end BerryEsseen
