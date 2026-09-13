import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.SmallVarianceSequence
import BerryEsseen.ManuscriptCentralClusterBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-! The original small-variance central absorption, retaining a positive gap relative to the actual binomial constant. -/

theorem manuscript_small_variance_central_sequence (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j) (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hlam : Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0))
    (hlampos : ∀ j, 0 < accumulatedNoiseVariance (P j) (Q j) (p j) (n j))
    (k : ℕ → ℕ) (hk : ∀ j, k j ≤ n j) (z₀ : ℝ)
    (hz : Tendsto (fun j => binomialZ (p j) (n j) (k j)) atTop (𝓝 z₀)) :
    ∃ c > 0, ∀ᶠ j in atTop, ∀ u : ℝ, |u| ≤ 1 / 2 →
      normalizedDiscrepancy (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)
        (((k j : ℝ) + u - (n j : ℝ) * p j) /
          Real.sqrt ((n j : ℝ) * clusterVariance (P j) (Q j) (p j))) ≤
        Real.sqrt (n j : ℝ) * (Real.sqrt (p j * (1 - p j)) ^ 3 /
          (p j * (1 - p j) * ((p j) ^ 2 + (1 - p j) ^ 2))) * binomialKolmogorov (p j) (n j) -
        c * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) /
          Real.sqrt (3 * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) / (2 / 5) + (ε j) ^ 2) := by
  let M : ℝ := |z₀| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let s := fun j => averageNoiseVariance (P j) (Q j) (p j)
  let lam := fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)
  let r := fun j => Real.sqrt (n j : ℝ)
  let v := fun j => p j * (1 - p j)
  let A := fun j => Real.sqrt (clusterVariance (P j) (Q j) (p j)) ^ 3 / clusterThirdAbsoluteMoment (P j) (Q j) (p j)
  let b := fun j => Real.sqrt (n j : ℝ) * binomialWeight (p j) (n j) (k j)
  let c := fun j => manuscriptClusterCentralLossCoefficient (P j) (Q j) (p j) (n j) (k j)
  let e := fun j => manuscriptClusterCentralErrorCoefficient (P j) (Q j) (p j) (2 / 5) (ε j) (n j) (k j)
  let q := fun j => Real.sqrt (3 * lam j / (2 / 5) + (ε j) ^ 2)
  have hn1 : ∀ j, 1 ≤ n j := fun j => by have := hn2 j; omega
  have hs0 : ∀ j, 0 ≤ s j := fun j => averageNoiseVariance_nonneg (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩
  have hs : Tendsto s atTop (𝓝 0) := squeeze_zero hs0
    (fun j => averageNoiseVariance_le_accumulated (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j) (hn1 j)) hlam
  have hv : Tendsto v atTop (𝓝 (pE * qE)) := hplim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hplim)
  have hv0 : pE * qE ≠ 0 := (mul_pos pE_pos qE_pos).ne'
  have hr : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hA : Tendsto A atTop (𝓝 bernoulliNormalizationE) := clusterNormalization_tendsto P Q p ε hp hplim hεp hεq hP hQ hs
  have hb : Tendsto b atTop (𝓝 (hE * standardNormalDensity z₀)) :=
    binomial_mass_at_moving_center W S B p hp hcentral hplim n hn hn2 k hk z₀ hz
  let c0 := 3 / 16 * bernoulliNormalizationE * (hE * standardNormalDensity z₀)
  have hc0 : 0 < c0 := by have := bernoulliNormalizationE_pos; have := hE_pos; have := standardNormalDensity_pos z₀; dsimp only [c0]; positivity
  have hc : Tendsto c atTop (𝓝 c0) := (hA.const_mul (3 / 16)).mul hb
  have hefirst : Tendsto (fun j => (56 * cE + 48 * phi0) / (v j * r j)) atTop (𝓝 (0 : ℝ)) := by
    have h := ((tendsto_const_nhds (x := 56 * cE + 48 * phi0)).div hv hv0).div_atTop hr
    change Tendsto (fun j => ((56 * cE + 48 * phi0) / v j) / r j) atTop (𝓝 (0 : ℝ)) at h
    simpa only [div_div] using h
  have hD : Tendsto (fun j => 3 * lam j / (2 / 5 : ℝ) ^ 2 + (ε j) ^ 2 / (2 / 5)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using
      ((hlam.const_mul 3).div_const ((2 / 5 : ℝ) ^ 2)).add ((hεlim.pow 2).div_const (2 / 5))
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) := by
    have hcoef := ((hA.const_mul 176000).mul hb).add ((hA.const_mul (128 * cE)).div_const (2 / 5))
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
  have hlarge : ∀ᶠ j in atTop, 2 * M ≤ (2 / 5 : ℝ) * r j := by
    filter_upwards [hr.eventually_ge_atTop (5 * M)] with j hj
    linarith
  have hfourlim : Tendsto (fun j => 3 * (lam j / (2 / 5 : ℝ)) ^ 2 + (ε j) ^ 2 * (lam j / (2 / 5)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add] using
      (((hlam.div_const (2 / 5)).pow 2).const_mul 3).add ((hεlim.pow 2).mul (hlam.div_const (2 / 5)))
  refine ⟨c0 / 4, by positivity, ?_⟩
  filter_upwards [binomial_central_gaussian_derivative W S B p hp hcentral hplim n hn hn2 s hs0 hs M hM.le,
    eventually_absorption_at_positive_roots c e q c0 hc0 hc he hq, hsmall, hlarge,
    Metric.tendsto_nhds.1 hz 1 (by norm_num),
    hc.eventually (lt_mem_nhds (by linarith : c0 / 2 < c0)),
    hfourlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 160000))]
    with j hjder hjbudget hjsmall hjlarge hjz hjc hjfour
  intro u hu
  have hjz' : |binomialZ (p j) (n j) (k j)| ≤ M := by
    rw [Real.dist_eq] at hjz
    have htri := abs_add_le (binomialZ (p j) (n j) (k j) - z₀) z₀
    rw [sub_add_cancel] at htri
    dsimp only [M]
    linarith
  have hpδ : (2 / 5 : ℝ) ≤ p j := (hcentral j).1
  have hqδ : (2 / 5 : ℝ) ≤ 1 - p j := by have := (hcentral j).2; linarith
  have hjlampos : 0 < lam j := hlampos j
  have hjqpos : 0 < q j := Real.sqrt_pos.2 (by positivity)
  have hjd := hjder (k j) (hk j) hjz'
  have hfour : (twoNoiseBlock (P j) (Q j) (n j) (k j)).fourthMoment ≤ 1 / 160000 :=
    (noise_fourth_uniform_bound (P j) (Q j) (p j) (2 / 5) (ε j) (by norm_num)
      hpδ hqδ (hε j) (hP j) (hQ j) (n j) (k j) (hk j)).trans hjfour.le
  have hraw : |(k j : ℝ) - n j * p j| ≤ M * r j := by
    have hvb := (bernoulli_variance_tau_bounds (p j) (hp j)).1
    have hs1 : Real.sqrt (p j * (1 - p j)) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hvb.2
    have hid := binomialZ_scaling (p j) (hp j) (n j) (hn1 j) (k j)
    have hspos := Real.sqrt_pos.mpr hvb.1
    have he : (k j : ℝ) - n j * p j = Real.sqrt (p j * (1 - p j)) *
        (r j * binomialZ (p j) (n j) (k j)) := by
      rw [hid]
      simp only [Int.cast_natCast]
      exact (mul_div_cancel₀ _ hspos.ne').symm
    rw [he, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have hbnd := mul_le_mul hs1 (mul_le_mul_of_nonneg_left hjz' (Real.sqrt_nonneg (n j : ℝ)))
      (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul, mul_comm M] using hbnd
  have hcomp := manuscript_twoCluster_central_error_budget B (P j) (Q j) (p j) (2 / 5) (ε j) M (by norm_num)
    hpδ hqδ (hε j) hM.le (hεp j) (hεq j) (hP j) (hQ j) hjsmall (n j) (k j) (hn1 j) (hk j)
    hjd.1 hfour hjd.2 hraw hjlarge hjlampos u hu
  have hbound := absorb_cluster_errors _ _ (lam j) (c j) (q j) (e j) hjlampos.le hjqpos hjbudget.1
    (hjbudget.2 hjqpos) hcomp
  have hgap : c0 / 4 * lam j / q j ≤ c j * lam j / (2 * q j) := by
    apply (div_le_iff₀ hjqpos).mpr
    have he : c j * lam j / (2 * q j) * q j = c j * lam j / 2 := by
      field_simp [hjqpos.ne']
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_right hjc.le hjlampos.le]
  exact hbound.trans (sub_le_sub_left hgap _)

end BerryEsseen
