import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ClusterCoefficientLimits
import BerryEsseen.CentralClusterBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem normalized_binomial_Kolmogorov_lt (S : PublishedBernoulliBound) (p : ℝ)
    (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) *
      binomialKolmogorov p n < cE := by
  let v := p * (1 - p)
  let τ := p ^ 2 + (1 - p) ^ 2
  have hv : 0 < v := mul_pos hp.1 (sub_pos.2 hp.2)
  have hτ : 0 < τ := by dsimp only [τ]; nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := Real.sqrt_pos.2 hn0
  have hs := Real.sqrt_pos.2 hv
  have h := mul_lt_mul_of_pos_left (S.strict_bound p hp n hn)
    (mul_pos hr (div_pos (pow_pos hs 3) (mul_pos hv hτ)))
  apply h.trans_eq
  rw [mul_assoc (n : ℝ), Real.sqrt_mul hn0.le]
  change Real.sqrt (n : ℝ) * (Real.sqrt v ^ 3 / (v * τ)) *
    (cE * τ / (Real.sqrt (n : ℝ) * Real.sqrt v)) = cE
  field_simp [hr.ne', hs.ne', hv.ne', hτ.ne']
  rw [Real.sq_sqrt hv.le]

theorem averageNoiseVariance_le_accumulated (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (hn : 1 ≤ n) : averageNoiseVariance P Q p ≤ accumulatedNoiseVariance P Q p n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_right hn' (averageNoiseVariance_nonneg P Q p hp)
  simpa only [one_mul] using h

theorem eventually_absorption_at_positive_roots (c e q : ℕ → ℝ) (c0 : ℝ) (hc0 : 0 < c0)
    (hc : Tendsto c atTop (𝓝 c0)) (he : Tendsto e atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 0)) :
    ∀ᶠ j in atTop, 0 < c j ∧ (0 < q j → e j ≤ c j / (2 * q j)) := by
  filter_upwards [hc.eventually (lt_mem_nhds (by linarith : c0 / 2 < c0)),
    he.eventually (gt_mem_nhds (by linarith : 0 < c0 / 4)),
    hq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hjc hje hjq
  refine ⟨by linarith, ?_⟩
  intro hqpos
  apply (le_div_iff₀ (mul_pos (by norm_num) hqpos)).2
  have h1 := mul_le_mul_of_nonneg_right hje.le hqpos.le
  have h2 := mul_le_mul_of_nonneg_left hjq.le (by linarith : 0 ≤ c0 / 4)
  nlinarith only [h1, h2, hjc.le]

theorem binomial_central_raw_distance (p : ℝ) (hp : p ∈ Ioo 0 1) (n k : ℕ) (hn : 1 ≤ n)
    (hz : |binomialZ p n k| ≤ 1) : |(k : ℝ) - n * p| ≤ Real.sqrt (n : ℝ) := by
  have hv := (bernoulli_variance_tau_bounds p hp).1
  have hs : Real.sqrt (p * (1 - p)) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hv.2
  have he := binomialZ_scaling p hp n hn k
  have hroot := Real.sqrt_pos.2 hv.1
  have he' : (k : ℝ) - n * p = Real.sqrt (p * (1 - p)) * (Real.sqrt (n : ℝ) * binomialZ p n k) := by
    rw [he]
    simp only [Int.cast_natCast]
    exact (mul_div_cancel₀ _ hroot.ne').symm
  rw [he', abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := mul_le_mul hs (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg (n : ℝ)))
    (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mul_one, one_mul] using h

/-- The actual two-cluster central small-variance conclusion, along a sequence
approaching the Esseen parameter. It is uniform over offsets within one binomial
cell, includes zero noise, and has no assumed manuscript local-stability lemma. -/
theorem small_variance_central_sequence (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j) (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hlam : Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0))
    (k : ℕ → ℕ) (hk : ∀ j, k j ≤ n j)
    (hz : Tendsto (fun j => binomialZ (p j) (n j) (k j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∀ u : ℝ, |u| ≤ 1 / 2 →
      normalizedDiscrepancy (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)
        (((k j : ℝ) + u - (n j : ℝ) * p j) /
          Real.sqrt ((n j : ℝ) * clusterVariance (P j) (Q j) (p j))) ≤ cE := by
  let s := fun j => averageNoiseVariance (P j) (Q j) (p j)
  let lam := fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)
  let r := fun j => Real.sqrt (n j : ℝ)
  let v := fun j => p j * (1 - p j)
  let A := fun j => Real.sqrt (clusterVariance (P j) (Q j) (p j)) ^ 3 / clusterThirdAbsoluteMoment (P j) (Q j) (p j)
  let b := fun j => Real.sqrt (n j : ℝ) * binomialWeight (p j) (n j) (k j)
  let c := fun j => clusterCentralLossCoefficient (P j) (Q j) (p j) (n j) (k j)
  let e := fun j => clusterCentralErrorCoefficient (P j) (Q j) (p j) (2 / 5) (ε j) (n j) (k j)
  let q := fun j => Real.sqrt (3 * lam j / (2 / 5) + (ε j) ^ 2)
  have hn1 : ∀ j, 1 ≤ n j := fun j => by have := hn2 j; omega
  have hs0 : ∀ j, 0 ≤ s j := fun j => averageNoiseVariance_nonneg (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩
  have hs : Tendsto s atTop (𝓝 0) := squeeze_zero hs0
    (fun j => averageNoiseVariance_le_accumulated (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j) (hn1 j)) hlam
  have hv : Tendsto v atTop (𝓝 (pE * qE)) := hplim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hplim)
  have hv0 : pE * qE ≠ 0 := (mul_pos pE_pos qE_pos).ne'
  have hr : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hA : Tendsto A atTop (𝓝 bernoulliNormalizationE) := clusterNormalization_tendsto P Q p ε hp hplim hεp hεq hP hQ hs
  have hb : Tendsto b atTop (𝓝 (hE * phi0)) := by
    simpa only [standardNormalDensity_zero] using binomial_mass_at_moving_center W S B p hp hcentral hplim n hn hn2 k hk 0 hz
  let c0 := 3 / 16 * bernoulliNormalizationE * (hE * phi0)
  have hc0 : 0 < c0 := by have := bernoulliNormalizationE_pos; have := hE_pos; have := phi0_pos; dsimp only [c0]; positivity
  have hc : Tendsto c atTop (𝓝 c0) := (hA.const_mul (3 / 16)).mul hb
  have hefirst : Tendsto (fun j => (56 * cE + 48 * phi0) / (v j * r j)) atTop (𝓝 (0 : ℝ)) := by
    have h := ((tendsto_const_nhds (x := 56 * cE + 48 * phi0)).div hv hv0).div_atTop hr
    change Tendsto (fun j => ((56 * cE + 48 * phi0) / v j) / r j) atTop (𝓝 (0 : ℝ)) at h
    simpa only [div_div] using h
  have hD : Tendsto (fun j => 3 * lam j / (2 / 5 : ℝ) ^ 2 + (ε j) ^ 2 / (2 / 5)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using
      ((hlam.const_mul 3).div_const ((2 / 5 : ℝ) ^ 2)).add ((hεlim.pow 2).div_const (2 / 5))
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    have hcoef := ((hA.const_mul 11000).mul hb).add ((hA.const_mul (128 * cE)).div_const (2 / 5))
    simpa only [mul_zero, add_zero] using hefirst.add (hcoef.mul hD)
  have hq : Tendsto q atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_zero] using
      (((hlam.const_mul 3).div_const (2 / 5)).add (hεlim.pow 2)).sqrt
  have hsmall : ∀ᶠ j in atTop, s j ≤ v j / 16 := by
    have h := (hv.div_const 16).sub hs
    have hpos : 0 < pE * qE / 16 - 0 := by simpa only [sub_zero] using div_pos (mul_pos pE_pos qE_pos) (by norm_num : (0 : ℝ) < 16)
    filter_upwards [h.eventually (lt_mem_nhds hpos)] with j hj
    change 0 < v j / 16 - s j at hj
    linarith
  have hlarge : ∀ᶠ j in atTop, 2 ≤ (2 / 5 : ℝ) * r j := by
    filter_upwards [hr.eventually_ge_atTop 5] with j hj
    linarith
  filter_upwards [binomial_central_gaussian_derivative W S B p hp hcentral hplim n hn hn2 s hs0 hs 1 (by norm_num),
    eventually_absorption_at_positive_roots c e q c0 hc0 hc he hq, hsmall, hlarge,
    Metric.tendsto_nhds.1 hz 1 (by norm_num)] with j hjder hjbudget hjsmall hjlarge hjz
  intro u hu
  have hjz' : |binomialZ (p j) (n j) (k j)| ≤ 1 := by simpa only [Real.dist_eq, sub_zero] using hjz.le
  have hpδ : (2 / 5 : ℝ) ≤ p j := (hcentral j).1
  have hqδ : (2 / 5 : ℝ) ≤ 1 - p j := by have := (hcentral j).2; linarith
  by_cases hjlam : lam j = 0
  · have h := zero_noise_BoundAt B (P j) (Q j) (p j) (hp j) (n j) (hn1 j) hjlam
    exact (BoundAt_iff_normalized _ (n j) (hn1 j)).1 h _
  have hjlampos : 0 < lam j := lt_of_le_of_ne
    (accumulatedNoiseVariance_nonneg (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j)) (Ne.symm hjlam)
  have hjqpos : 0 < q j := Real.sqrt_pos.2 (by positivity)
  have hjd := hjder (k j) (hk j) hjz'
  have hcomp := twoCluster_central_error_budget B (P j) (Q j) (p j) (2 / 5) (ε j) 1 (by norm_num)
    hpδ hqδ (hε j) (by norm_num) (hεp j) (hεq j) (hP j) (hQ j) hjsmall (n j) (k j) (hn1 j) (hk j)
    hjd.1 hjd.2 (by simpa only [one_mul] using binomial_central_raw_distance (p j) (hp j) (n j) (k j) (hn1 j) hjz')
    (by simpa only [mul_one] using hjlarge) hjlampos u hu
  have hstrict := absorb_cluster_errors_strict _ _ (lam j) (c j) (q j) (e j) hjlampos hjqpos hjbudget.1
    (hjbudget.2 hjqpos) hcomp
  exact hstrict.le.trans (normalized_binomial_Kolmogorov_lt B (p j) (hp j) (n j) (hn1 j)).le

end BerryEsseen
