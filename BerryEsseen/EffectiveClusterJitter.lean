import BerryEsseen.ClusterSmoothing
import BerryEsseen.EffectiveSmoothingBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem effective_cluster_jitter_pointwise (S : PublishedSignedSmoothing)
    (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hp01 : p ∈ Ioo 0 1)
    (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 1000000 ≤ n) (x : ℝ) :
    Real.sqrt (n : ℝ) * |cdf (iidSumLaw (twoClusterMeasure P Q p) n ∗ uniformJitter 1) x -
      edgeworthCDF n (signedThirdMoment (standardizedTwoClusterLaw P Q p hp01))
        ((x - (n : ℝ) * p) / (Real.sqrt (clusterVariance P Q p) * Real.sqrt (n : ℝ)))| ≤
      effectiveClusterError n ε T := by
  let Z := standardizedTwoClusterLaw P Q p hp01
  let σ := Real.sqrt (clusterVariance P Q p)
  let r := Real.sqrt (n : ℝ)
  let L := σ * r * T
  let z := (x - (n : ℝ) * p) / (σ * r)
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpcc
  have hεb : ε ∈ Icc 0 0.001 := ⟨hε, effective_noise_amplitude_bound ε T hε hT hεT⟩
  have hσbounds := effective_cluster_scale_bounds P Q p ε hp hεb hP hQ
  have hσ : 0 < σ := by have h := hσbounds.1.1; change (0.48 : ℝ) ≤ σ at h; linarith
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hL : 0 < L := mul_pos (mul_pos hσ hr) (by linarith)
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hβ := effective_standardized_cluster_moment P Q p ε hp hεb hP hQ hp01
  have hF := effective_cluster_fourier_integral P Q p ε T hp hp01 hε hT hεT hP hQ n hn2
  have hsm := effective_jitter_signed_smoothing S Z n hn1 hβ σ⁻¹ L hL hF.1 z
  have hfi : (∫ t in Icc (-L) L, jitterFourierError Z n σ⁻¹ t) ≤
      effectiveClusterFourierBudget n (averageNoiseVariance P Q p) T := hF.2
  have hbound : r * |cdf (normalizedJitteredSumLaw Z n σ⁻¹) z - edgeworthCDF n (signedThirdMoment Z) z| ≤
      r * ((1 / 4 : ℝ) * effectiveClusterFourierBudget n (averageNoiseVariance P Q p) T + 24 / L) := by
    apply mul_le_mul_of_nonneg_left (hsm.trans (add_le_add (mul_le_mul_of_nonneg_left hfi (by positivity)) le_rfl)) hr.le
  have hbudget := effective_cluster_smoothing_budget n hn (averageNoiseVariance P Q p) ε T σ
    (averageNoiseVariance_nonneg P Q p hpcc) (averageNoiseVariance_le_square P Q p ε hpcc hε hP hQ) hT hσbounds.1.1
  have hfinal := hbound.trans hbudget
  have hc := standardized_unit_jitter_cdf (twoClusterMeasure P Q p) Z p σ hσ rfl n hn1 x
  change cdf (normalizedJitteredSumLaw Z n σ⁻¹) z = _ at hc
  rw [hc] at hfinal
  exact hfinal

theorem effective_cluster_jitter (S : PublishedSignedSmoothing)
    (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hp01 : p ∈ Ioo 0 1)
    (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 1000000 ≤ n) :
    Real.sqrt (n : ℝ) * sSup (Set.range (fun x : ℝ =>
      |cdf (iidSumLaw (twoClusterMeasure P Q p) n ∗ uniformJitter 1) x -
        edgeworthCDF n (signedThirdMoment (standardizedTwoClusterLaw P Q p hp01))
          ((x - (n : ℝ) * p) / (Real.sqrt (clusterVariance P Q p) * Real.sqrt (n : ℝ)))|)) ≤
      effectiveClusterError n ε T := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hsup : sSup (Set.range (fun x : ℝ =>
      |cdf (iidSumLaw (twoClusterMeasure P Q p) n ∗ uniformJitter 1) x -
        edgeworthCDF n (signedThirdMoment (standardizedTwoClusterLaw P Q p hp01))
          ((x - (n : ℝ) * p) / (Real.sqrt (clusterVariance P Q p) * Real.sqrt (n : ℝ)))|)) ≤
      effectiveClusterError n ε T / Real.sqrt (n : ℝ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    apply (le_div_iff₀ hr).mpr
    simpa only [mul_comm] using effective_cluster_jitter_pointwise S P Q p ε T hp hp01 hε hT hεT hP hQ n hn x
  have h := mul_le_mul_of_nonneg_left hsup hr.le
  simpa only [mul_div_cancel₀ _ hr.ne'] using h

end BerryEsseen
