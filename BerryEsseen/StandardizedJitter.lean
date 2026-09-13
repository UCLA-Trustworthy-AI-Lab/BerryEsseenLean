import BerryEsseen.Standardization
import BerryEsseen.UniformJitter

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BerryEsseen

theorem standardized_jitter_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (n : ℕ) (t : ℝ) :
    cdf (iidSumLaw (standardizedMeasure μ m σ) n ∗ uniformJitter h)
      ((t - (n : ℝ) * m) / σ + h / 2) =
    cdf (iidSumLaw μ n ∗ uniformJitter (σ * h)) (t + (σ * h) / 2) := by
  rw [uniformJitter_cdf_average _ hh, uniformJitter_cdf_average _ (mul_pos hσ hh)]
  have he (s : ℝ) :
      cdf (iidSumLaw (standardizedMeasure μ m σ) n) ((t - (n : ℝ) * m) / σ + s) =
        cdf (iidSumLaw μ n) (t + σ * s) := by
    have hx : (t - (n : ℝ) * m) / σ + s = ((t + σ * s) - (n : ℝ) * m) / σ := by field_simp; ring
    rw [hx, standardized_sum_cdf _ _ _ hσ]
  simp_rw [he]
  have hchange := intervalIntegral.integral_comp_mul_left (fun s : ℝ => cdf (iidSumLaw μ n) (t + s)) hσ.ne' (a := 0) (b := h)
  simp only [mul_zero, smul_eq_mul] at hchange
  rw [hchange]
  ring

theorem standardized_jitter_cdf_left (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (n : ℕ) (t : ℝ) :
    cdf (iidSumLaw (standardizedMeasure μ m σ) n ∗ uniformJitter h)
      ((t - (n : ℝ) * m) / σ - h / 2) =
    cdf (iidSumLaw μ n ∗ uniformJitter (σ * h)) (t - (σ * h) / 2) := by
  have hcdf := standardized_jitter_cdf μ m σ h hσ hh n (t - σ * h)
  have he : ((t - σ * h) - (n : ℝ) * m) / σ + h / 2 = (t - (n : ℝ) * m) / σ - h / 2 := by field_simp; ring
  rw [he] at hcdf
  convert hcdf using 1
  congr 1
  ring

end BerryEsseen
