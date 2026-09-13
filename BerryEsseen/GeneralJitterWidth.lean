import BerryEsseen.GeneralJitterAssembly
import BerryEsseen.ActualJitterSandwich
import BerryEsseen.EdgeworthEnvelopes

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem spanJitter_eq_scaled_unit (h : ℝ) (hh : 0 ≤ h) :
    spanJitter h = (uniformJitter 1).map (fun x => h * x) := by
  letI := spanJitter_probability h
  letI := uniformJitter_probability (show (0 : ℝ) < 1 by norm_num)
  letI : IsProbabilityMeasure ((uniformJitter 1).map (fun x => h * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_spanJitter h hh, charFun_map_mul, charFun_uniformJitter 1 (by norm_num)]
  simp only [one_mul]

theorem unit_jitter_abs_bound : ∀ᵐ v ∂uniformJitter 1, |v| ≤ 1 / 2 := by
  have hb : ∀ᵐ v ∂volume.restrict (Icc (-(1 : ℝ) / 2) (1 / 2)), |v| ≤ 1 / 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
  simpa only [uniformJitter, one_div_one, ENNReal.ofReal_one, one_smul] using hb

theorem jitter_scaled_cdf_integrable (μ : Measure ℝ) (h t : ℝ) :
    Integrable (fun v => cdf μ (t - h * v)) (uniformJitter 1) := by
  letI := uniformJitter_probability (show (0 : ℝ) < 1 by norm_num)
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((monotone_cdf μ).measurable.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg μ _)]
    exact cdf_le_one μ _

theorem spanJitter_cdf_common_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : 0 ≤ h) (t : ℝ) :
    cdf (μ ∗ spanJitter h) t = ∫ v, cdf μ (t - h * v) ∂uniformJitter 1 := by
  letI := spanJitter_probability h
  letI := uniformJitter_probability (show (0 : ℝ) < 1 by norm_num)
  rw [Measure.conv_comm, cdf_convolution_integral, spanJitter_eq_scaled_unit h hh]
  have hf : Measurable (fun x : ℝ => cdf μ (t - x)) :=
    (monotone_cdf μ).measurable.comp (by fun_prop)
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem spanJitter_width_cdf_sandwich (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h w : ℝ) (hh : 0 ≤ h) (hw : 0 ≤ w) (t : ℝ) :
    cdf (μ ∗ spanJitter h) (t - |w - h| / 2) ≤ cdf (μ ∗ spanJitter w) t ∧
      cdf (μ ∗ spanJitter w) t ≤ cdf (μ ∗ spanJitter h) (t + |w - h| / 2) := by
  rw [spanJitter_cdf_common_uniform μ h hh, spanJitter_cdf_common_uniform μ w hw,
    spanJitter_cdf_common_uniform μ h hh]
  have hp : ∀ᵐ v ∂uniformJitter 1, |(w - h) * v| ≤ |w - h| / 2 := by
    filter_upwards [unit_jitter_abs_bound] with v hv
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hv (abs_nonneg (w - h))]
  constructor
  · apply integral_mono_ae (jitter_scaled_cdf_integrable μ h _) (jitter_scaled_cdf_integrable μ w _)
    filter_upwards [hp] with v hv
    apply monotone_cdf μ
    have hb := (abs_le.mp hv).2
    nlinarith
  · apply integral_mono_ae (jitter_scaled_cdf_integrable μ w _) (jitter_scaled_cdf_integrable μ h _)
    filter_upwards [hp] with v hv
    apply monotone_cdf μ
    have hb := (abs_le.mp hv).1
    nlinarith

theorem normalized_jitter_width_cdf_sandwich (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h w : ℝ) (hh : 0 ≤ h) (hw : 0 ≤ w) (x : ℝ) :
    ((normalizedJitteredSumLaw P n h) (Iic (x - |w - h| / (2 * Real.sqrt (n : ℝ))))).toReal ≤
      ((normalizedJitteredSumLaw P n w) (Iic x)).toReal ∧
    ((normalizedJitteredSumLaw P n w) (Iic x)).toReal ≤
      ((normalizedJitteredSumLaw P n h) (Iic (x + |w - h| / (2 * Real.sqrt (n : ℝ))))).toReal := by
  letI := spanJitter_probability h
  letI := spanJitter_probability w
  letI := normalizedJitteredSumLaw_probability P n h
  letI := normalizedJitteredSumLaw_probability P n w
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  change (normalizedJitteredSumLaw P n h).real (Iic _) ≤ (normalizedJitteredSumLaw P n w).real (Iic _) ∧
    (normalizedJitteredSumLaw P n w).real (Iic _) ≤ (normalizedJitteredSumLaw P n h).real (Iic _)
  rw [← cdf_eq_real, ← cdf_eq_real, ← cdf_eq_real]
  unfold normalizedJitteredSumLaw
  rw [cdf_map_div_positive _ _ hs, cdf_map_div_positive _ _ hs, cdf_map_div_positive _ _ hs]
  convert spanJitter_width_cdf_sandwich (iidSumLaw P.measure n) h w hh hw (Real.sqrt (n : ℝ) * x) using 1 <;>
    congr 2 <;> field_simp [hs.ne'] <;> ring

theorem edgeworthCDF_hasDerivAt (n : ℕ) (κ x : ℝ) :
    HasDerivAt (edgeworthCDF n κ) (edgeworthDensity n κ x) x := by
  convert (normalCDF_hasDerivAt x).add
    ((gaussian_x_density_second_hasDerivAt x).const_mul (κ / (6 * Real.sqrt (n : ℝ)))) using 1
  funext t
  dsimp only [edgeworthCDF, Pi.add_apply]
  ring

theorem edgeworthCDF_general_lipschitz (n : ℕ) (hn : 1 ≤ n) (κ B : ℝ) (hκ : |κ| ≤ B)
    (x y : ℝ) :
    |edgeworthCDF n κ y - edgeworthCDF n κ x| ≤ ((1 + 3 * B) * phi0) * |y - x| := by
  simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (edgeworthCDF_hasDerivAt n κ t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using edgeworthDensity_uniform_bound n hn κ B hκ t)
    (mem_univ x) (mem_univ y)

/-- The variable-width jitter remark, including zero limiting span. The fixed
width actual expansion is a proved sublemma to be supplied by the caller. -/
theorem variable_jitter_uniform_expansion_of_fixed
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (hn1 : ∀ j, 1 ≤ n j)
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (h : ℝ) (hh : 0 ≤ h) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hwlim : Tendsto w atTop (𝓝 h))
    (hfixed : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) (w j) x)
      (fun _ => 0) atTop := by
  let M := (1 + 3 * B) * phi0
  have hwidth : Tendsto (fun j => M * (|w j - h| / 2)) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_div, mul_zero] using ((hwlim.sub_const h).abs.div_const 2).const_mul M
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 hfixed (ε / 2) (by linarith),
    hwidth.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hj hwj
  intro x
  let r := Real.sqrt (n j : ℝ)
  let a := |w j - h| / (2 * r)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n j by have := hn1 j; omega))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hS := normalized_jitter_width_cdf_sandwich (P j) (n j) (hn1 j) h (w j) hh (hw j) x
  have hlo : |r * jitterCDFError (P j) (n j) h (x - a)| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hj (x - a)
  have hhi : |r * jitterCDFError (P j) (n j) h (x + a)| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hj (x + a)
  have hκ := (signedThirdMoment_abs_le (P j)).trans (hB j)
  have hglo := edgeworthCDF_general_lipschitz (n j) (hn1 j) (signedThirdMoment (P j)) B hκ x (x - a)
  have hghi := edgeworthCDF_general_lipschitz (n j) (hn1 j) (signedThirdMoment (P j)) B hκ x (x + a)
  have hlowshift : r * |edgeworthCDF (n j) (signedThirdMoment (P j)) (x - a) -
      edgeworthCDF (n j) (signedThirdMoment (P j)) x| ≤ M * (|w j - h| / 2) := by
    have hg := mul_le_mul_of_nonneg_left hglo hr.le
    simp only [sub_sub_cancel_left, abs_neg, abs_of_nonneg ha] at hg
    convert hg using 1
    dsimp only [a]
    field_simp [hr.ne']
    <;> ring
  have hhighshift : r * |edgeworthCDF (n j) (signedThirdMoment (P j)) (x + a) -
      edgeworthCDF (n j) (signedThirdMoment (P j)) x| ≤ M * (|w j - h| / 2) := by
    have hg := mul_le_mul_of_nonneg_left hghi hr.le
    simp only [add_sub_cancel_left, abs_of_nonneg ha] at hg
    convert hg using 1
    dsimp only [a]
    field_simp [hr.ne']
    <;> ring
  have hls := mul_le_mul_of_nonneg_left hS.1 hr.le
  have hus := mul_le_mul_of_nonneg_left hS.2 hr.le
  have hll := (abs_lt.mp hlo).1
  have huu := (abs_lt.mp hhi).2
  have hlg := neg_abs_le (edgeworthCDF (n j) (signedThirdMoment (P j)) (x - a) -
      edgeworthCDF (n j) (signedThirdMoment (P j)) x)
  have hug := le_abs_self (edgeworthCDF (n j) (signedThirdMoment (P j)) (x + a) -
      edgeworthCDF (n j) (signedThirdMoment (P j)) x)
  have hlgb := mul_le_mul_of_nonneg_left hlg hr.le
  have hugb := mul_le_mul_of_nonneg_left hug hr.le
  simp only [Real.dist_eq, zero_sub, abs_neg]
  rw [abs_lt]
  dsimp only [jitterCDFError] at hll huu ⊢
  change r * _ ≤ r * _ at hls hus
  change _ < ε / 2 at hwj
  constructor <;> nlinarith only [hls, hus, hll, huu, hlgb, hugb, hlowshift, hhighshift, hwj]

end BerryEsseen
