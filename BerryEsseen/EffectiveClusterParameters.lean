import BerryEsseen.EffectiveClusterPeaks

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace BerryEsseen

theorem effective_noise_amplitude_bound (ε T : ℝ) (hε : 0 ≤ ε) (hT : 10 ≤ T)
    (hεT : ε ≤ (100 * T)⁻¹) : ε ≤ 0.001 := by
  have h := (le_div_iff₀ (by positivity : 0 < 100 * T)).mp
    (show ε ≤ 1 / (100 * T) by simpa only [one_div] using hεT)
  have hm := mul_le_mul_of_nonneg_left hT hε
  nlinarith only [h, hm]

theorem averageNoiseVariance_le_square (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc 0 1) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    averageNoiseVariance P Q p ≤ ε ^ 2 := by
  have hP2 := mul_le_mul_of_nonneg_left (P.secondMoment_le_sq ε hε hP) (sub_nonneg.mpr hp.2)
  have hQ2 := mul_le_mul_of_nonneg_left (Q.secondMoment_le_sq ε hε hQ) hp.1
  unfold averageNoiseVariance
  nlinarith only [hP2, hQ2]

theorem effective_cluster_variance_bounds (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    clusterVariance P Q p ∈ Icc 0.24 0.250001 := by
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hs0 := averageNoiseVariance_nonneg P Q p hp01
  have hs := averageNoiseVariance_le_square P Q p ε hp01 hε.1 hP hQ
  have hv : 6 / 25 ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (show 0 ≤ 3 / 5 - p by linarith [hp.2])]
  have hvu : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hε2 : ε ^ 2 ≤ (0.001 : ℝ) ^ 2 := pow_le_pow_left₀ hε.1 hε.2 2
  have he : clusterVariance P Q p = p * (1 - p) + averageNoiseVariance P Q p := by
    unfold clusterVariance averageNoiseVariance
    ring
  rw [he]
  constructor <;> nlinarith only [hs0, hs, hv, hvu, hε2]

theorem effective_cluster_scale_bounds (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    Real.sqrt (clusterVariance P Q p) ∈ Icc 0.48 1 ∧
      (Real.sqrt (clusterVariance P Q p))⁻¹ ^ 2 ≤ 25 / 6 := by
  have hv := effective_cluster_variance_bounds P Q p ε hp hε hP hQ
  have hv0 : 0 < clusterVariance P Q p := by linarith [hv.1]
  have hs := Real.sqrt_nonneg (clusterVariance P Q p)
  have hs2 := Real.sq_sqrt hv0.le
  constructor
  · constructor <;> nlinarith [hv.1, hv.2]
  · rw [inv_pow, hs2]
    apply (inv_le_comm₀ hv0 (by norm_num : (0 : ℝ) < 25 / 6)).mpr
    norm_num
    linarith [hv.1]

theorem effective_twoCluster_centered_bound (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ≤ 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    ∀ᵐ x ∂twoClusterMeasure P Q p, |x - p| ≤ 0.601 := by
  rw [twoClusterMeasure, mixtureMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    filter_upwards [hP] with x hx
    have h := abs_sub x p
    rw [abs_of_nonneg (show 0 ≤ p by linarith [hp.1])] at h
    linarith [hp.2]
  · apply Measure.ae_smul_measure
    rw [ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [hQ] with x hx
    have he : (1 + x) - p = x + (1 - p) := by ring
    rw [he]
    have h := abs_add_le x (1 - p)
    rw [abs_of_nonneg (show 0 ≤ 1 - p by linarith [hp.2])] at h
    linarith [hp.1]

theorem effective_standardized_cluster_bound (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hp01 : p ∈ Ioo 0 1) :
    ∀ᵐ x ∂(standardizedTwoClusterLaw P Q p hp01).measure, |x| ≤ 1.5 := by
  have hscale := (effective_cluster_scale_bounds P Q p ε hp hε hP hQ).1
  have hσ : 0 < Real.sqrt (clusterVariance P Q p) := by linarith [hscale.1]
  rw [standardizedTwoClusterLaw_measure, standardizedMeasure,
    ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  filter_upwards [effective_twoCluster_centered_bound P Q p ε hp hε.2 hP hQ] with x hx
  rw [abs_div, abs_of_pos hσ]
  apply (div_le_iff₀ hσ).mpr
  linarith [hscale.1]

theorem thirdMoment_le_of_standardized_bound (P : StandardizedLaw) (L : ℝ)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ L) : thirdMoment P ≤ L := by
  unfold thirdMoment
  calc
    _ ≤ ∫ x, L * x ^ 2 ∂P.measure := by
      apply integral_mono_ae P.third_integrable (P.second_integrable.const_mul L)
      filter_upwards [hb] with x hx
      have h := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
      convert h using 1 <;> rw [← sq_abs x] <;> ring
    _ = L := by rw [integral_const_mul, P.second_one, mul_one]

/-- The manuscript's conditional cubic expansion, before standardization. -/
theorem manuscript_effective_cluster_third_numerator (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    clusterThirdAbsoluteMoment P Q p ≤ (1 / 4 : ℝ) * 0.52 + 4 * (10 : ℝ) ^ (-6 : ℤ) := by
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have he := twoCluster_abs_third_error P Q p ε hp01
    (by linarith [hp.1, hε.2]) (by linarith [hp.2, hε.2]) hP hQ
  change |clusterThirdAbsoluteMoment P Q p - p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)| ≤
    (3 + ε) * averageNoiseVariance P Q p at he
  have hs0 := averageNoiseVariance_nonneg P Q p hp01
  have hs := averageNoiseVariance_le_square P Q p ε hp01 hε.1 hP hQ
  have he2 := pow_le_pow_left₀ hε.1 hε.2 2
  have ht : p ^ 2 + (1 - p) ^ 2 ≤ (0.52 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (show 0 ≤ 3 / 5 - p by linarith [hp.2])]
  have hv : p * (1 - p) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hbase := mul_le_mul hv ht (by positivity : 0 ≤ p ^ 2 + (1 - p) ^ 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have herr := mul_le_mul (show 3 + ε ≤ (4 : ℝ) by linarith [hε.2]) hs hs0 (by norm_num : (0 : ℝ) ≤ 4)
  have hh := (abs_le.mp he).2
  norm_num
  nlinarith only [hh, hbase, herr, he2]

/-- Exact manuscript bound β < 1.11, from its original numerator and variance bounds. -/
theorem manuscript_effective_standardized_cluster_moment (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hp01 : p ∈ Ioo 0 1) :
    thirdMoment (standardizedTwoClusterLaw P Q p hp01) < 1.11 := by
  have hn := manuscript_effective_cluster_third_numerator P Q p ε hp hε hP hQ
  have hv := effective_cluster_variance_bounds P Q p ε hp hε hP hQ
  have hs0 := Real.sqrt_nonneg (clusterVariance P Q p)
  have hs2 := Real.sq_sqrt (show 0 ≤ clusterVariance P Q p by linarith [hv.1])
  have hs : (0.4898 : ℝ) < Real.sqrt (clusterVariance P Q p) := by nlinarith [hv.1]
  have hc : (0.117552 : ℝ) < Real.sqrt (clusterVariance P Q p) ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hv.1 hs0
    nlinarith only [hm, hs2, hs]
  rw [standardizedTwoClusterLaw_third]
  apply (div_lt_iff₀ (by positivity : 0 < Real.sqrt (clusterVariance P Q p) ^ 3)).mpr
  norm_num at hn
  nlinarith only [hn, hc]

theorem effective_standardized_cluster_moment (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hp01 : p ∈ Ioo 0 1) :
    thirdMoment (standardizedTwoClusterLaw P Q p hp01) ≤ 1.84 := by
  exact (manuscript_effective_standardized_cluster_moment P Q p ε hp hε hP hQ hp01).le.trans (by norm_num)

end BerryEsseen
