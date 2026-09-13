import BerryEsseen.EffectiveJitterLowFrequency

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem globalJitterLowFrequencyMajorant_integral (h : ℝ) (hh2 : h ^ 2 ≤ 25) :
    (∫ t, effectiveJitterLowFrequencyMajorant h t) < 11 := by
  have he : effectiveJitterLowFrequencyMajorant h = fun t =>
      effectiveLowFrequencyMajorant t + (h ^ 2 / 24) * (|t| * Real.exp (-(0.35 : ℝ) * t ^ 2)) := by
    funext t
    unfold effectiveJitterLowFrequencyMajorant
    ring
  have hi : Integrable (fun t : ℝ => |t| * Real.exp (-(0.35 : ℝ) * t ^ 2)) := by
    simpa only [pow_one] using gaussian_abs_pow_integrable 1 (0.35 : ℝ) (by norm_num)
  rw [he, integral_add effectiveLowFrequencyMajorant_integrable (hi.const_mul _),
    integral_const_mul, gaussian_abs_linear_integral _ (by norm_num)]
  nlinarith only [effectiveLowFrequencyMajorant_integral, hh2]

theorem globalJitterLowFrequencyIntegral_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) (hh2 : h ^ 2 ≤ 25) :
    (∫ t in effectiveLowFrequencyRange n, jitterFourierError P n h t) ≤ 11 / (n : ℝ) := by
  calc
    _ ≤ ∫ t in effectiveLowFrequencyRange n, effectiveJitterLowFrequencyMajorant h t / (n : ℝ) := by
      apply integral_mono_ae (effectiveJitterLowFrequencyIntegral_integrable P hβ hb n hn h hh)
        ((effectiveJitterLowFrequencyMajorant_integrable h).div_const (n : ℝ)).integrableOn
      filter_upwards [ae_restrict_mem (show MeasurableSet (effectiveLowFrequencyRange n) from measurableSet_Icc)] with t ht
      exact effective_jitterFourierError_low_bound P hβ hb n hn h hh t ht
    _ ≤ ∫ t, effectiveJitterLowFrequencyMajorant h t / (n : ℝ) := by
      apply setIntegral_le_integral ((effectiveJitterLowFrequencyMajorant_integrable h).div_const (n : ℝ))
      exact ae_of_all _ (fun t => div_nonneg (effectiveJitterLowFrequencyMajorant_nonneg h t) (Nat.cast_nonneg n))
    _ = (∫ t, effectiveJitterLowFrequencyMajorant h t) / (n : ℝ) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right (globalJitterLowFrequencyMajorant_integral h hh2).le (Nat.cast_nonneg n)

end BerryEsseen
