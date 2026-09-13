import BerryEsseen.ManuscriptEffectiveSmallVariance
import BerryEsseen.ManuscriptEffectiveJitterGap
import BerryEsseen.ManuscriptEffectiveClusterBudget
import BerryEsseen.ManuscriptEffectiveClusterEnvelope
import BerryEsseen.EffectiveClusters
import BerryEsseen.ManuscriptWeightedJitter

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_effective_cluster_local_jitter_gaps (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (x : ℝ) (hx : |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ)) :
    appendixClusterGap / Real.sqrt (n : ℝ) ≤
      cdf (iidSumLaw (twoClusterMeasure P Q p) n ∗ uniformJitter 1) (x + 1 / 2) -
        cdf (iidSumLaw (twoClusterMeasure P Q p) n) x ∧
    appendixClusterGap / Real.sqrt (n : ℝ) ≤
      cdf (iidSumLaw (twoClusterMeasure P Q p) n) x -
        cdf (iidSumLaw (twoClusterMeasure P Q p) n ∗ uniformJitter 1) (x - 1 / 2) := by
  have hp01 := (effective_binomial_parameters p hp).1
  letI := twoClusterMeasure_probability P Q p ⟨hp01.1.le, hp01.2.le⟩
  have hR := manuscript_effective_local_mass_pointwise I P Q p hp hP hQ n hn hlam x (1 / 4) (1 / 2) hx (by norm_num) (by norm_num) (by norm_num)
  have hL := manuscript_effective_local_mass_pointwise I P Q p hp hP hQ n hn hlam x (-1 / 2) (-1 / 4) hx (by norm_num) (by norm_num) (by norm_num)
  simp only [add_zero, neg_div, ← sub_eq_add_neg] at hR hL
  have hJU := manuscript_uniform_forward_quarter_gap (iidSumLaw (twoClusterMeasure P Q p) n) x
  have hJL := manuscript_uniform_backward_quarter_gap (iidSumLaw (twoClusterMeasure P Q p) n) x
  have hRM := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hLM := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hD := div_le_div_of_nonneg_right appendixClusterGap_bounds.2.2 (Real.sqrt_nonneg (n : ℝ))
  have hid : (Real.exp (-4000000000000) / 2) / Real.sqrt (n : ℝ) =
      (1 / 2) * (Real.exp (-4000000000000) / Real.sqrt (n : ℝ)) := by ring
  rw [hid] at hD
  exact ⟨hD.trans (hRM.trans hJU), hD.trans (hLM.trans hJL)⟩

theorem manuscript_effective_cluster_central_large_variance (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : appendixNStar ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (z : ℝ) (hz : |z| ≤ 5) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n z ≤
      cE - appendixClusterGap / 4 := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpcc
  let Z := standardizedTwoClusterLaw P Q p hp01
  let σ := Real.sqrt (clusterVariance P Q p)
  let r := Real.sqrt (n : ℝ)
  let t := σ * r * z + n * p
  have hnlarge := (appendix_sample_size_bounds n hn).1
  have hn1 : 1 ≤ n := by omega
  have hε : Real.exp (-appendixA) ∈ Icc 0 0.001 := ⟨(Real.exp_pos _).le, by linarith [appendix_noise_and_cutoff_bounds.1]⟩
  have hσbounds := effective_cluster_scale_bounds P Q p (Real.exp (-appendixA)) hp hε hP hQ
  have hσ : 0 < σ := by have h := hσbounds.1.1; change (0.48 : ℝ) ≤ σ at h; linarith
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hβ := effective_standardized_cluster_moment P Q p (Real.exp (-appendixA)) hp hε hP hQ hp01
  have hκ : |signedThirdMoment Z| ≤ 2 := (signedThirdMoment_abs_le Z).trans (hβ.trans (by norm_num))
  have hσhi : σ ≤ 0.51 := by
    have hv := effective_cluster_variance_bounds P Q p (Real.exp (-appendixA)) hp hε hP hQ
    have hsq := Real.sq_sqrt (clusterVariance_pos P Q p hp01).le
    change σ ^ 2 = _ at hsq
    nlinarith [hv.2]
  have ht : |t - (n : ℝ) * p| ≤ 3 * r := by
    dsimp only [t]
    rw [add_sub_cancel_right, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hr]
    have hm := mul_le_mul hσhi hz (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 0.51)
    have h := mul_le_mul_of_nonneg_right hm hr.le
    nlinarith only [h, hr.le]
  have hJ := effective_cluster_jitter_pointwise manuscriptSignedSmoothing P Q p (Real.exp (-appendixA)) appendixClusterCutoff hp hp01
    (Real.exp_pos _).le appendix_noise_and_cutoff_bounds.2.1 appendix_noise_and_cutoff_bounds.2.2 hP hQ n (by omega)
  have hgap := manuscript_effective_cluster_local_jitter_gaps I P Q p hp hP hQ n hnlarge hlam t ht
  have hzid : (t - (n : ℝ) * p) / (σ * r) = z := by dsimp only [t]; field_simp; ring
  have hbound := manuscript_jitter_gap_edgeworth_bound (iidSumLaw (twoClusterMeasure P Q p) n) n hn1 ((n : ℝ) * p) σ
    (signedThirdMoment Z) (effectiveClusterError n (Real.exp (-appendixA)) appendixClusterCutoff) appendixClusterGap t
    hσ hσbounds.1.1 hκ hJ hgap.1 hgap.2
  change r * |cdf (iidSumLaw (twoClusterMeasure P Q p) n) t - normalCDF ((t - n * p) / (σ * r))| ≤ _ at hbound
  rw [hzid] at hbound
  have hmoment := manuscript_effective_cluster_envelope_moment P Q p (Real.exp (-appendixA)) hp hε hP hQ
  have hbudget1 := manuscript_effective_cluster_error_budget n hn
  have hbudget2 := manuscript_effective_cluster_shift_moment_budget n hn (averageNoiseVariance P Q p)
    (averageNoiseVariance_le_square P Q p (Real.exp (-appendixA)) hpcc (Real.exp_pos _).le hP hQ)
  have hraw : r * |cdf (iidSumLaw (twoClusterMeasure P Q p) n) t - normalCDF z| ≤ cE * thirdMoment Z - appendixClusterGap / 2 := by
    nlinarith only [hbound, hmoment, hbudget1, hbudget2]
  have harg : (t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p) = z := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), mul_comm (Real.sqrt (n : ℝ))]
    exact hzid
  have hdisc := standardizedTwoCluster_discrepancy P Q p hp01 n hn1 t
  rw [harg] at hdisc
  have hNorm : normalizedDiscrepancy Z n z =
      (r * |cdf (iidSumLaw (twoClusterMeasure P Q p) n) t - normalCDF z|) / thirdMoment Z := by
    rw [hdisc, standardizedTwoClusterLaw_third]
    change r * σ ^ 3 / clusterThirdAbsoluteMoment P Q p * _ = _ / (clusterThirdAbsoluteMoment P Q p / σ ^ 3)
    field_simp [(clusterThirdAbsoluteMoment_pos P Q p hp01).ne']
    <;> ring
  rw [hNorm]
  apply (div_le_iff₀ (thirdMoment_pos Z)).mpr
  have hDβ := mul_le_mul_of_nonneg_left (hβ.trans (by norm_num : (1.84 : ℝ) ≤ 2)) appendixClusterGap_bounds.1.le
  nlinarith only [hraw, hDβ]

theorem manuscript_effective_cluster_large_variance (I : PublishedNonIIDBound)
    (U : PublishedNonuniformBound) (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : appendixNStar ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n) :
    sSup (Set.range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) ≤
      cE - appendixClusterGap / 4 := by
  have hnlarge := (appendix_sample_size_bounds n hn).1
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨z, rfl⟩
  by_cases hz : |z| ≤ 5
  · exact manuscript_effective_cluster_central_large_variance I P Q p hp hP hQ n hn hlam z hz
  · have h := normalizedDiscrepancy_far_five U (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1)
      n (by omega) z (le_of_not_ge hz)
    linarith [cE_numeric_bounds.1, appendixClusterGap_bounds.2.1]

theorem manuscript_effective_cluster_stability (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : appendixNStar ≤ n) :
    sSup (Set.range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) < cE := by
  by_cases hsmall : accumulatedNoiseVariance P Q p n ≤ 1 / (10 : ℝ) ^ 12
  · have h := manuscript_effective_small_variance B U P Q p (Real.exp (-appendixA)) hp
      ⟨(Real.exp_pos _).le, appendix_noise_and_cutoff_bounds.1⟩ hP hQ n (appendix_sample_size_bounds n hn).1 hsmall
    exact h.1.trans_lt h.2
  · have h := manuscript_effective_cluster_large_variance I U P Q p hp hP hQ n hn (le_of_not_ge hsmall)
    exact h.trans_lt (sub_lt_self _ (div_pos appendixClusterGap_bounds.1 (by norm_num)))

end BerryEsseen
