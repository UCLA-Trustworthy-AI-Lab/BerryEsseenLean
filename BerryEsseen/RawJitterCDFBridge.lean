import BerryEsseen.GeneralJitterWidth
import BerryEsseen.Standardization

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem standardized_spanJitter_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ d : ℝ) (hσ : 0 < σ) (hd : 0 ≤ d) (n : ℕ) (t : ℝ) :
    cdf (iidSumLaw (standardizedMeasure μ m σ) n ∗ spanJitter (d / σ))
      ((t - (n : ℝ) * m) / σ) =
      cdf (iidSumLaw μ n ∗ spanJitter d) t := by
  rw [spanJitter_cdf_common_uniform _ _ (div_nonneg hd hσ.le),
    spanJitter_cdf_common_uniform _ _ hd]
  apply integral_congr_ae
  filter_upwards [] with v
  have he : (t - (n : ℝ) * m) / σ - d / σ * v =
      ((t - d * v) - (n : ℝ) * m) / σ := by ring
  rw [he, standardized_sum_cdf μ m σ hσ n (t - d * v)]

theorem standardized_normalized_spanJitter_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hZ : Z.measure = standardizedMeasure μ m σ)
    (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d) (x : ℝ) :
    cdf (normalizedJitteredSumLaw Z n (d / σ)) x =
      cdf (iidSumLaw μ n ∗ spanJitter d)
        ((n : ℝ) * m + σ * Real.sqrt (n : ℝ) * x) := by
  letI := spanJitter_probability (d / σ)
  have hr : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  unfold normalizedJitteredSumLaw
  rw [cdf_map_div_positive _ _ hr, hZ]
  have he : Real.sqrt (n : ℝ) * x =
      (((n : ℝ) * m + σ * Real.sqrt (n : ℝ) * x) - (n : ℝ) * m) / σ := by
    field_simp
    ring
  rw [he]
  exact standardized_spanJitter_cdf μ m σ d hσ hd n _

theorem standardized_normalized_spanJitter_cdf_at_raw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hZ : Z.measure = standardizedMeasure μ m σ)
    (n : ℕ) (hn : 1 ≤ n) (d : ℝ) (hd : 0 ≤ d) (t : ℝ) :
    cdf (normalizedJitteredSumLaw Z n (d / σ))
      ((t - (n : ℝ) * m) / (σ * Real.sqrt (n : ℝ))) =
      cdf (iidSumLaw μ n ∗ spanJitter d) t := by
  rw [standardized_normalized_spanJitter_cdf μ Z m σ hσ hZ n hn d hd]
  congr 1
  have hr : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  field_simp
  ring

end BerryEsseen
