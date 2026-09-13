import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.RepresentedSelected

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem RepresentedSelectedExtremizers.average_noise_tendsto (R : RepresentedSelectedExtremizers) :
    Tendsto (fun j => averageNoiseVariance (R.lower j) (R.upper j) (R.p j)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => averageNoiseVariance_nonneg _ _ _ ⟨(R.p_open j).1.le, (R.p_open j).2.le⟩)
    (fun j => ?_) (by simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using R.epsilon_tendsto.pow 2)
  have h := accumulatedNoiseVariance_le_noise_bound (R.lower j) (R.upper j) (R.p j) (R.epsilon j)
    ⟨(R.p_open j).1.le, (R.p_open j).2.le⟩ (R.epsilon_nonneg j) (R.noise_lower j) (R.noise_upper j) 1
  simpa only [accumulatedNoiseVariance, Nat.cast_one, one_mul, averageNoiseVariance] using h

theorem RepresentedSelectedExtremizers.scale_tendsto (R : RepresentedSelectedExtremizers) :
    Tendsto (fun j => Real.sqrt (clusterVariance (R.lower j) (R.upper j) (R.p j))) atTop (𝓝 sigmaE) :=
  (clusterVariance_tendsto R.lower R.upper R.p R.p_tendsto R.average_noise_tendsto).sqrt

theorem standardizedTwoCluster_sum_cdf (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (u : ℝ) :
    cdf (iidSumLaw (standardizedTwoClusterLaw P Q p hp).measure n) u =
      cdf (iidSumLaw (twoClusterMeasure P Q p) n)
        (Real.sqrt (clusterVariance P Q p) * u + (n : ℝ) * p) := by
  letI := twoClusterMeasure_probability P Q p ⟨hp.1.le, hp.2.le⟩
  have hs := Real.sqrt_pos.2 (clusterVariance_pos P Q p hp)
  have h := standardized_sum_cdf (twoClusterMeasure P Q p) p (Real.sqrt (clusterVariance P Q p)) hs n
    (Real.sqrt (clusterVariance P Q p) * u + (n : ℝ) * p)
  have he : (Real.sqrt (clusterVariance P Q p) * u + (n : ℝ) * p - (n : ℝ) * p) /
      Real.sqrt (clusterVariance P Q p) = u := by field_simp [hs.ne']; ring
  rw [he] at h
  exact h

theorem RepresentedSelectedExtremizers.raw_flat_center (R : RepresentedSelectedExtremizers)
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) :
    ∃ x : ℕ → ℝ,
      Tendsto (fun j => (x j - (R.X.n j : ℝ) * R.p j) / Real.sqrt (R.X.n j : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun j => Real.sqrt (R.X.n j : ℝ) *
        (cdf (iidSumLaw (twoClusterMeasure (R.lower j) (R.upper j) (R.p j)) (R.X.n j)) (x j + 1 / 2) -
          cdf (iidSumLaw (twoClusterMeasure (R.lower j) (R.upper j) (R.p j)) (R.X.n j)) (x j))) atTop (𝓝 0) := by
  have hb : bE ∈ esseenLaw.measure.support := by change bE ∈ esseenMeasure.support; rw [esseen_support]; simp
  obtain ⟨v, hvsupp, hv⟩ := weak_support_point_approximation R.X.P esseenLaw R.X.weak (Icc (-10) 10)
    isCompact_Icc R.X.support bE hb
  let σ := fun j => Real.sqrt (clusterVariance (R.lower j) (R.upper j) (R.p j))
  let u := fun j => R.X.t j - v j
  let x := fun j => σ j * u j + (R.X.n j : ℝ) * R.p j
  have hσ : ∀ j, 0 < σ j := fun j => Real.sqrt_pos.2 (clusterVariance_pos _ _ _ (R.p_open j))
  have hu := predecessor_threshold_tendsto_zero R.X.n R.X.t v bE R.X.n_tendsto
    (fun j => by have := R.X.n_ge_two j; omega) R.X.threshold hv
  refine ⟨x, ?_, ?_⟩
  · have h := R.scale_tendsto.mul hu
    simpa only [x, u, add_sub_cancel_right, mul_div_assoc, mul_zero] using h
  have havg := extremizer_jitter_contact_saturation H W S R.X.P R.X.n R.X.t R.X.n_tendsto R.X.n_ge_two
    R.X.attain R.X.violate R.X.weak R.X.threshold R.X.support v bE hvsupp hv
  have hd : Tendsto (fun j => (1 / 2 : ℝ) / σ j) atTop (𝓝 (hE / 2)) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).div R.scale_tendsto sigmaE_pos.ne'
    convert h using 1 <;> unfold hE <;> ring
  have hflat := raw_jitter_flat_increment_limit
    (fun j => iidSumLaw (R.X.P j).measure (R.X.n j)) (fun j => Real.sqrt (R.X.n j : ℝ)) u
    (fun j => (1 / 2 : ℝ) / σ j) (fun j => Real.sqrt_nonneg _) hE (hE / 2) hE_pos
    ⟨by linarith [hE_pos], by linarith [hE_pos]⟩ hd havg
  convert hflat using 1
  funext j
  dsimp only
  rw [← R.law_eq j, standardizedTwoCluster_sum_cdf, standardizedTwoCluster_sum_cdf]
  have he : σ j * (u j + (1 / 2 : ℝ) / σ j) + (R.X.n j : ℝ) * R.p j = x j + 1 / 2 := by
    dsimp only [x]
    field_simp [(hσ j).ne']
    ring
  change _ = Real.sqrt (R.X.n j : ℝ) *
    (cdf (iidSumLaw (twoClusterMeasure (R.lower j) (R.upper j) (R.p j)) (R.X.n j))
      (σ j * (u j + (1 / 2 : ℝ) / σ j) + (R.X.n j : ℝ) * R.p j) -
      cdf (iidSumLaw (twoClusterMeasure (R.lower j) (R.upper j) (R.p j)) (R.X.n j)) (x j))
  rw [he]

theorem RepresentedSelectedExtremizers.accumulated_noise_tendsto (R : RepresentedSelectedExtremizers)
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) :
    Tendsto (fun j => accumulatedNoiseVariance (R.lower j) (R.upper j) (R.p j) (R.X.n j)) atTop (𝓝 0) := by
  obtain ⟨x, hx, hflat⟩ := R.raw_flat_center H W S
  exact accumulatedNoiseVariance_tendsto_of_flat_interval W S B I R.lower R.upper R.p R.epsilon R.p_open R.p_central
    R.p_tendsto R.epsilon_nonneg R.epsilon_tendsto R.noise_lower R.noise_upper R.X.n R.X.n_tendsto R.X.n_ge_two
    x (1 / 2) (by norm_num) hx hflat

theorem RepresentedSelectedExtremizers.successor_accumulated_noise_tendsto (R : RepresentedSelectedExtremizers)
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) :
    Tendsto (fun j => accumulatedNoiseVariance (R.lower j) (R.upper j) (R.p j) (R.X.n j + 1)) atTop (𝓝 0) := by
  have h := (R.accumulated_noise_tendsto H W S B I).add R.average_noise_tendsto
  simp only [zero_add] at h
  convert h using 1
  funext j
  unfold accumulatedNoiseVariance averageNoiseVariance
  push_cast
  ring

end BerryEsseen
