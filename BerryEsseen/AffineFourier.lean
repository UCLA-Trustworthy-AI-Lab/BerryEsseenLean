import BerryEsseen.SmoothingApplicationMoments
import BerryEsseen.EffectiveClusterFrequency
import BerryEsseen.EffectiveJitterLowFrequency
import BerryEsseen.StandardizedJitter
import BerryEsseen.EffectiveDensity

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem charFun_standardizedMeasure_norm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ t : ℝ) : ‖charFun (standardizedMeasure μ m σ) t‖ = ‖charFun μ (t / σ)‖ := by
  have he : standardizedMeasure μ m σ =
      (μ.map (fun x : ℝ => x + (-m))).map (fun x : ℝ => σ⁻¹ * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    unfold standardizedMeasure
    congr 1
    funext x
    dsimp only [Function.comp_def]
    ring
  rw [he, charFun_map_mul, charFun_map_add_const, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  congr 2
  ring

theorem normalizedJitteredSumLaw_cdf (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (h x : ℝ) :
    cdf (normalizedJitteredSumLaw P n h) x =
      cdf (iidSumLaw P.measure n ∗ spanJitter h) (Real.sqrt (n : ℝ) * x) := by
  letI := normalizedJitteredSumLaw_probability P n h
  letI := spanJitter_probability h
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [cdf_eq_real, cdf_eq_real]
  unfold normalizedJitteredSumLaw Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext y
  simp only [mem_preimage, mem_Iic]
  rw [div_le_iff₀ hs, mul_comm x]

theorem effective_jitter_signed_smoothing (S : PublishedSignedSmoothing) (P : StandardizedLaw)
    (n : ℕ) (hn : 1 ≤ n) (hβ : thirdMoment P ≤ 1.84) (h L : ℝ) (hL : 0 < L)
    (hi : IntegrableOn (jitterFourierError P n h) (Icc (-L) L)) (x : ℝ) :
    |cdf (normalizedJitteredSumLaw P n h) x - edgeworthCDF n (signedThirdMoment P) x| ≤
      (1 / 4) * (∫ t in Icc (-L) L, jitterFourierError P n h t) + (24) / L := by
  letI := normalizedJitteredSumLaw_probability P n h
  have hi' : IntegrableOn (fun t => ‖charFun (normalizedJitteredSumLaw P n h) t -
      densityFourier (edgeworthDensity n (signedThirdMoment P)) t‖ / |t|) (Icc (-L) L) := by
    simpa only [edgeworthDensity_fourier, jitterFourierError] using hi
  have hb := S.bound (normalizedJitteredSumLaw P n h) inferInstance
    (normalizedJitteredSumLaw_first_integrable P n h) (edgeworthDensity n (signedThirdMoment P))
    (edgeworthDensity_integrable _ _) (edgeworthDensity_first_integrable _ _) (edgeworthDensity_mass_one _ _) 1 L (by norm_num) hL
    (edgeworthDensity_effective_bound n hn _ ((signedThirdMoment_abs_le P).trans hβ)) hi' x
  simpa only [← edgeworthCDF_cumulative, edgeworthDensity_fourier, jitterFourierError,
    cdf_eq_real, Measure.real, mul_one] using hb

theorem standardized_unit_jitter_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ) (hP : P.measure = standardizedMeasure μ m σ)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    cdf (normalizedJitteredSumLaw P n σ⁻¹) ((x - (n : ℝ) * m) / (σ * Real.sqrt (n : ℝ))) =
      cdf (iidSumLaw μ n ∗ uniformJitter 1) x := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [normalizedJitteredSumLaw_cdf P n hn, hP, spanJitter, if_pos (inv_pos.mpr hσ)]
  have h := standardized_jitter_cdf μ m σ σ⁻¹ hσ (inv_pos.mpr hσ) n (x - 1 / 2)
  rw [mul_inv_cancel₀ hσ.ne'] at h
  convert h using 1
  · congr 1
    field_simp
    ring
  · congr 1
    ring

theorem scaled_annular_integral (f : ℝ → ℝ) (a T s : ℝ) (hs : 0 < s)
    (hi : IntegrableOn f (abs ⁻¹' Icc a T)) :
    IntegrableOn (fun t => f (t / s) / s) (abs ⁻¹' Icc (s * a) (s * T)) ∧
      (∫ t in abs ⁻¹' Icc (s * a) (s * T), f (t / s) / s) = ∫ u in abs ⁻¹' Icc a T, f u := by
  let K := abs ⁻¹' Icc a T
  let L := abs ⁻¹' Icc (s * a) (s * T)
  have hK : MeasurableSet K := measurableSet_Icc.preimage measurable_abs
  have hL : MeasurableSet L := measurableSet_Icc.preimage measurable_abs
  have hmem (t : ℝ) : t ∈ L ↔ t / s ∈ K := by
    change (s * a ≤ |t| ∧ |t| ≤ s * T) ↔ (a ≤ |t / s| ∧ |t / s| ≤ T)
    rw [abs_div, abs_of_pos hs, le_div_iff₀ hs, div_le_iff₀ hs, mul_comm a, mul_comm T]
  have he : L.indicator (fun t => f (t / s) / s) = fun t => K.indicator f (s⁻¹ * t) / s := by
    funext t
    have hdiv : s⁻¹ * t = t / s := by ring
    rw [hdiv]
    by_cases ht : t ∈ L
    · rw [indicator_of_mem ht, indicator_of_mem ((hmem t).mp ht)]
    · rw [indicator_of_notMem ht, indicator_of_notMem (mt (hmem t).mpr ht), zero_div]
  have hind := ((hi.integrable_indicator hK).comp_mul_left' (inv_ne_zero hs.ne')).div_const s
  rw [← he] at hind
  refine ⟨(integrable_indicator_iff hL).mp hind, ?_⟩
  rw [← integral_indicator hL, he, integral_div, Measure.integral_comp_mul_left,
    inv_inv, abs_of_pos hs, smul_eq_mul, mul_div_cancel_left₀ _ hs.ne', integral_indicator hK]

end BerryEsseen
