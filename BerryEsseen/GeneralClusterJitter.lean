import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.GeneralClusterLimits
import BerryEsseen.GeneralJitterExpansion
import BerryEsseen.AffineFourier
import BerryEsseen.GeneralJitterGap

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem general_cluster_variable_jitter_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    TendstoUniformly (fun j z => Real.sqrt (n j : ℝ) *
      jitterCDFError (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)
        (Real.sqrt (clusterVariance (P j) (Q j) (p j)))⁻¹ z) (fun _ => 0) atTop := by
  have hs := averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ
  have hv := (clusterVariance_tendsto_general P Q p p₀ hplim hs).sqrt
  have hσ : 0 < Real.sqrt (p₀ * (1 - p₀)) :=
    Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))
  exact general_variable_jitter_uniform_expansion W S _ (standardizedBernoulliLaw p₀ hp₀)
    (standardizedTwoClusterLaw_tendsto P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ)
    (standardizedTwoCluster_third_tendsto P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ)
    n hn (1 / Real.sqrt (p₀ * (1 - p₀))) (one_div_pos.mpr hσ).le
    (standardizedBernoulli_resonance_multiplier_zero p₀ hp₀) _
    (fun j => inv_nonneg.mpr (Real.sqrt_nonneg _))
    (by simpa only [one_div] using hv.inv₀ hσ.ne')

/-- Actual raw sums, centered by np, with independent Uniform[-1/2,1/2] jitter. -/
theorem general_cluster_raw_jitter_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1) x -
        edgeworthCDF (n j) (signedThirdMoment (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)))
          ((x - (n j : ℝ) * p j) /
            (Real.sqrt (clusterVariance (P j) (Q j) (p j)) * Real.sqrt (n j : ℝ)))))
      (fun _ => 0) atTop := by
  have hU := general_cluster_variable_jitter_expansion W S P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ n hn
  apply Metric.tendstoUniformly_iff.2
  intro η hη
  filter_upwards [Metric.tendstoUniformly_iff.1 hU η hη, hn.eventually (eventually_ge_atTop 1)] with j hj hn1
  intro x
  letI := twoClusterMeasure_probability (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩
  letI := normalizedJitteredSumLaw_probability (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j))
    (n j) (Real.sqrt (clusterVariance (P j) (Q j) (p j)))⁻¹
  have hc := standardized_unit_jitter_cdf (twoClusterMeasure (P j) (Q j) (p j))
    (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (p j)
    (Real.sqrt (clusterVariance (P j) (Q j) (p j)))
    (Real.sqrt_pos.mpr (clusterVariance_pos _ _ _ (hp j))) rfl (n j) hn1 x
  have h := hj ((x - (n j : ℝ) * p j) /
    (Real.sqrt (clusterVariance (P j) (Q j) (p j)) * Real.sqrt (n j : ℝ)))
  simp only [cdf_eq_real, Measure.real] at hc ⊢
  simpa only [jitterCDFError, hc] using h

theorem general_shifted_jitter_envelope_limit (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (w b : ℕ → ℝ) (b₀ κ : ℝ)
    (hblim : Tendsto b atTop (𝓝 b₀))
    (hκlim : Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 κ))
    (hU : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) (w j) x)
      (fun _ => 0) atTop) :
    TendstoUniformly (fun j z => Real.sqrt (n j : ℝ) *
      (cdf (normalizedJitteredSumLaw (P j) (n j) (w j))
        (z + b j / (2 * Real.sqrt (n j : ℝ))) - normalCDF z) - edgeworthEnvelope b₀ κ z)
      (fun _ => 0) atTop := by
  obtain ⟨K, hK⟩ := hκlim.abs.bddAbove_range
  have hκ : ∀ j, |signedThirdMoment (P j)| ≤ K := fun j => hK ⟨j, rfl⟩
  have hC : Tendsto (fun j => generalEdgeworthShiftConstant K (b j)) atTop
      (𝓝 (generalEdgeworthShiftConstant K b₀)) := by
    unfold generalEdgeworthShiftConstant
    simpa only [mul_assoc] using (((hblim.pow 2).const_mul 3).div_const 8 |>.add
      (((hblim.abs.const_mul K).const_mul 3).div_const 2)).const_mul phi0
  have hC0 := hC.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))
  have he : Tendsto (fun j => phi0 * (|b j - b₀| / 2 + |signedThirdMoment (P j) - κ| / 6))
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_div, add_zero, mul_zero] using
      ((((hblim.sub_const b₀).abs).div_const 2).add (((hκlim.sub_const κ).abs).div_const 6)).const_mul phi0
  apply Metric.tendstoUniformly_iff.2
  intro η hη
  filter_upwards [Metric.tendstoUniformly_iff.1 hU (η / 3) (by positivity),
    hC0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3)),
    he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 3)),
    hn.eventually (eventually_ge_atTop 1)] with j hj hCj hej hnj
  intro z
  letI := normalizedJitteredSumLaw_probability (P j) (n j) (w j)
  dsimp only [Function.comp_apply] at hCj
  have hJ : |Real.sqrt (n j : ℝ) *
      (cdf (normalizedJitteredSumLaw (P j) (n j) (w j)) (z + b j / (2 * Real.sqrt (n j : ℝ))) -
        edgeworthCDF (n j) (signedThirdMoment (P j)) (z + b j / (2 * Real.sqrt (n j : ℝ))))| < η / 3 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, jitterCDFError, cdf_eq_real, Measure.real] using
      hj (z + b j / (2 * Real.sqrt (n j : ℝ)))
  have hshift := general_edgeworthCDF_shift_remainder (n j) hnj (signedThirdMoment (P j)) (b j) z K (hκ j)
  have hparam := edgeworthEnvelope_both_parameter_bound (b j) b₀ (signedThirdMoment (P j)) κ z
  have hJlo := (abs_lt.mp hJ).1
  have hJhi := (abs_lt.mp hJ).2
  have hslo := (abs_le.mp hshift).1
  have hshi := (abs_le.mp hshift).2
  have hplo := (abs_le.mp hparam).1
  have hphi := (abs_le.mp hparam).2
  simp only [Real.dist_eq, zero_sub, abs_neg]
  apply abs_lt.mpr
  constructor <;> nlinarith only [hJlo, hJhi, hslo, hshi, hplo, hphi, hCj, hej]

/-- Both raw shifted-jitter envelopes, by choosing b = 1 and b = -1. -/
theorem general_cluster_shifted_jitter_envelopes (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (b : ℝ) :
    TendstoUniformly (fun j z => Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1)
        ((n j : ℝ) * p j + Real.sqrt (clusterVariance (P j) (Q j) (p j)) * Real.sqrt (n j : ℝ) * z + b / 2) -
        normalCDF z) - edgeworthEnvelope (b / Real.sqrt (p₀ * (1 - p₀)))
          ((1 - 2 * p₀) / Real.sqrt (p₀ * (1 - p₀))) z)
      (fun _ => 0) atTop := by
  have hs := averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ
  have hv := (clusterVariance_tendsto_general P Q p p₀ hplim hs).sqrt
  have hσ : 0 < Real.sqrt (p₀ * (1 - p₀)) :=
    Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))
  have hκ := standardizedTwoCluster_signed_third_tendsto P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ
  rw [standardizedBernoulli_signed_third] at hκ
  have hU := general_shifted_jitter_envelope_limit _ n hn _
    (fun j => b / Real.sqrt (clusterVariance (P j) (Q j) (p j)))
    (b / Real.sqrt (p₀ * (1 - p₀))) ((1 - 2 * p₀) / Real.sqrt (p₀ * (1 - p₀)))
    (tendsto_const_nhds.div hv hσ.ne') hκ
    (general_cluster_variable_jitter_expansion W S P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ n hn)
  apply Metric.tendstoUniformly_iff.2
  intro η hη
  filter_upwards [Metric.tendstoUniformly_iff.1 hU η hη, hn.eventually (eventually_ge_atTop 1)] with j hj hn1
  intro z
  letI := twoClusterMeasure_probability (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩
  have hσj : 0 < Real.sqrt (clusterVariance (P j) (Q j) (p j)) := Real.sqrt_pos.mpr (clusterVariance_pos _ _ _ (hp j))
  have hnj : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n j by omega))
  have hc := standardized_unit_jitter_cdf (twoClusterMeasure (P j) (Q j) (p j))
    (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (p j)
    (Real.sqrt (clusterVariance (P j) (Q j) (p j))) hσj rfl (n j) hn1
    ((n j : ℝ) * p j + Real.sqrt (clusterVariance (P j) (Q j) (p j)) * Real.sqrt (n j : ℝ) * z + b / 2)
  have he : (((n j : ℝ) * p j + Real.sqrt (clusterVariance (P j) (Q j) (p j)) * Real.sqrt (n j : ℝ) * z + b / 2) -
      (n j : ℝ) * p j) / (Real.sqrt (clusterVariance (P j) (Q j) (p j)) * Real.sqrt (n j : ℝ)) =
      z + (b / Real.sqrt (clusterVariance (P j) (Q j) (p j))) / (2 * Real.sqrt (n j : ℝ)) := by
    field_simp [hσj.ne', hnj.ne']
    <;> ring
  rw [he] at hc
  simpa only [hc] using hj z

end BerryEsseen
