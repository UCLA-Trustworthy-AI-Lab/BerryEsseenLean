import BerryEsseen.SmoothingApplicationMoments
import BerryEsseen.EffectiveDensity
import BerryEsseen.EffectiveLowFrequencyIntegral
import BerryEsseen.EffectiveGaussianTail

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

def normalizedIIDSumLaw (P : StandardizedLaw) (n : ℕ) : Measure ℝ :=
  (iidSumLaw P.measure n).map (fun x => x / Real.sqrt (n : ℝ))

theorem normalizedIIDSumLaw_probability (P : StandardizedLaw) (n : ℕ) :
    IsProbabilityMeasure (normalizedIIDSumLaw P n) := by
  unfold normalizedIIDSumLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_normalizedIIDSumLaw (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    charFun (normalizedIIDSumLaw P n) t = charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n := by
  unfold normalizedIIDSumLaw
  have he : (fun x : ℝ => x / Real.sqrt (n : ℝ)) = (fun x => (Real.sqrt (n : ℝ))⁻¹ * x) := by funext x; ring
  rw [he, charFun_map_mul, charFun_iidSumLaw]
  simp only [div_eq_mul_inv, mul_comm t]

theorem normalizedIIDSumLaw_cdf (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    cdf (normalizedIIDSumLaw P n) x = cdf (iidSumLaw P.measure n) (Real.sqrt (n : ℝ) * x) := by
  letI := normalizedIIDSumLaw_probability P n
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [cdf_eq_real, cdf_eq_real]
  unfold normalizedIIDSumLaw Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext y
  simp only [mem_preimage, mem_Iic]
  rw [div_le_iff₀ hs, mul_comm x]

theorem normalizedDiscrepancy_eq_iid_error (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    normalizedDiscrepancy P n x = Real.sqrt (n : ℝ) / thirdMoment P *
      |cdf (normalizedIIDSumLaw P n) x - normalCDF x| := by
  rw [normalizedIIDSumLaw_cdf P n hn x, cdf_eq_real]
  unfold normalizedDiscrepancy discrepancy Measure.real
  ring

theorem iid_signed_smoothing (S : PublishedSignedSmoothing) (P : StandardizedLaw)
    (n : ℕ) (hn : 1 ≤ n) (hβ : thirdMoment P ≤ 1.84) (L : ℝ) (hL : 0 < L)
    (hi : IntegrableOn (fourierEdgeworthError P n) (Icc (-L) L)) (x : ℝ) :
    |cdf (normalizedIIDSumLaw P n) x - edgeworthCDF n (signedThirdMoment P) x| ≤
      (1 / 4) * (∫ t in Icc (-L) L, fourierEdgeworthError P n t) + (24) / L := by
  letI := normalizedIIDSumLaw_probability P n
  have he : (fun t => ‖charFun (normalizedIIDSumLaw P n) t - densityFourier (edgeworthDensity n (signedThirdMoment P)) t‖ / |t|) =
      fourierEdgeworthError P n := by
    funext t
    rw [charFun_normalizedIIDSumLaw, edgeworthDensity_fourier]
    rfl
  have hi' := hi
  rw [← he] at hi'
  have h := S.bound (normalizedIIDSumLaw P n) inferInstance
    (normalizedIIDMap_first_integrable P n) (edgeworthDensity n (signedThirdMoment P))
    (edgeworthDensity_integrable _ _) (edgeworthDensity_first_integrable _ _) (edgeworthDensity_mass_one _ _) 1 L (by norm_num) hL
    (edgeworthDensity_effective_bound n hn _ ((signedThirdMoment_abs_le P).trans hβ)) hi' x
  rw [he, mul_one, ← edgeworthCDF_cumulative] at h
  simpa only [cdf_eq_real, Measure.real] using h

end BerryEsseen
