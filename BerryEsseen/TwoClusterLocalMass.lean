import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.LocalMassAssembly
import BerryEsseen.WindowGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The near-Esseen sequence version of uniform two-cluster local mass. The
interval may have atoms at either endpoint: its probability is genuinely open. -/
theorem twoCluster_local_mass_above_variance (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ y ∂(P j).measure, |y| ≤ ε j) (hQ : ∀ j, ∀ᵐ y ∂(Q j).measure, |y| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (Lstar : ℝ) (hLstar : 0 < Lstar)
    (R a b : ℝ) (hR : 0 ≤ R) (hab : a < b) :
    ∃ c > 0, ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j) →
      ∀ x : ℝ, |x - (n j : ℝ) * p j| ≤ R * Real.sqrt (n j : ℝ) →
      c / Real.sqrt (n j : ℝ) ≤ (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)).real (Ioo (x + a) (x + b)) := by
  let M := (R + 1) / (2 / 5 : ℝ)
  let B0 := hE * centralDensityFloor M / 2
  let C0 := (b - a) * centralDensityFloor (localNoiseWindowRadius Lstar a b) / 8
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hB0 : 0 < B0 := by have := hE_pos; have := centralDensityFloor_pos M; dsimp only [B0]; positivity
  have hC0 : 0 < C0 := by have := sub_pos.2 hab; have := centralDensityFloor_pos (localNoiseWindowRadius Lstar a b); dsimp only [C0]; positivity
  refine ⟨B0 * C0, mul_pos hB0 hC0, ?_⟩
  have hr : Tendsto (fun j => Real.sqrt (n j : ℝ)) atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  filter_upwards [binomial_uniform_local_mass_pE W S B p hp hcentral hplim n hn hn2 B0 hB0,
    hεlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hεlim.eventually (gt_mem_nhds hC0), hr.eventually_ge_atTop (5 * (R + 1))] with j hjmass hjε hjεC hjlarge
  intro hjL x hx
  let L := accumulatedNoiseVariance (P j) (Q j) (p j) (n j)
  let r := Real.sqrt (n j : ℝ)
  let K := integerWindow x (max 1 (Real.sqrt L))
  have hLpos : 0 < L := hLstar.trans_le hjL
  have hn1 : 1 ≤ n j := by have := hn2 j; omega
  have hn0 : (0 : ℝ) < n j := by exact_mod_cast (show 0 < n j by omega)
  have hrpos : 0 < r := Real.sqrt_pos.2 hn0
  have hpI : p j ∈ Icc 0 1 := ⟨(hp j).1.le, (hp j).2.le⟩
  have hpδ := (hcentral j).1
  have hqδ : (2 / 5 : ℝ) ≤ 1 - p j := by have := (hcentral j).2; linarith
  have hLn : L ≤ n j := by
    have hbound := accumulatedNoiseVariance_le_noise_bound (P j) (Q j) (p j) (ε j) hpI (hε j) (hP j) (hQ j) (n j)
    have heps : (ε j) ^ 2 ≤ 1 := by nlinarith [hε j]
    have h := mul_le_mul_of_nonneg_left heps hn0.le
    nlinarith only [hbound, h]
  have hlarge : 2 * (R + 1) ≤ (2 / 5 : ℝ) * Real.sqrt (n j : ℝ) := by linarith
  have hgeo := central_integer_window_geometry (p j) (2 / 5) R L x (by norm_num) hpδ hqδ hR (n j) hn1 hLn hlarge hx
  have hK : K ⊆ Finset.range (n j + 1) := by
    intro k hk
    exact Finset.mem_range.2 (by have := (hgeo.2.2 k hk).1; omega)
  have hweights : ∀ k ∈ K, B0 / r ≤ binomialWeight (p j) (n j) k := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    have hzk := binomialZ_bound_from_raw (p j) (2 / 5) (R + 1) (by norm_num) hpδ hqδ (by linarith)
      (n j) k hn1 hkgeo.2
    have hfloor := standardNormalDensity_central_lower M (binomialZ (p j) (n j) k) hM hzk
    have hfloor' := mul_le_mul_of_nonneg_left hfloor hE_pos.le
    have hmass := (abs_lt.1 (hjmass k hkgeo.1)).1
    apply (div_le_iff₀ hrpos).2
    rw [mul_comm (binomialWeight (p j) (n j) k) r]
    dsimp only [B0] at hmass ⊢
    linarith only [hmass, hfloor']
  have hnoise : ∀ k ∈ K, C0 / Real.sqrt L ≤
      (twoNoiseBlock (P j) (Q j) (n j) k).measure.real (Ioo ((x + a) - k) ((x + b) - k)) := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    have ht := noise_variance_central_half_double (P j) (Q j) (p j) (2 / 5) (R + 1) (by norm_num)
      hpδ hqδ (by linarith) (n j) k hn1 hkgeo.1 hkgeo.2 hlarge
    have hkx := integerWindow_distance x (max 1 (Real.sqrt L)) hgeo.1 (by positivity) k hk
    have h := noise_block_window_mass_lower I (P j) (Q j) (ε j) (hε j) (hP j) (hQ j) (n j) k hn1 hkgeo.1
      Lstar L x a b hLstar hjL hab ht.1 ht.2 hkx hjεC.le
    simpa only [C0, div_div] using h
  have hprob := twoCluster_open_interval_lower_of_blocks (P j) (Q j) (p j) hpI (n j) (x + a) (x + b)
    (by linarith) K hK (B0 / r) (C0 / Real.sqrt L) (by positivity) (by positivity) hweights hnoise
  have hcard : Real.sqrt L ≤ (K.card : ℝ) := (le_max_right 1 (Real.sqrt L)).trans
    (integerWindow_card_lower x (max 1 (Real.sqrt L)) hgeo.1 (le_max_left _ _))
  have hcount := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ B0 / r * (C0 / Real.sqrt L))
  have he : Real.sqrt L * (B0 / r * (C0 / Real.sqrt L)) = B0 * C0 / r := by
    field_simp [(Real.sqrt_pos.2 hLpos).ne']
  rw [he] at hcount
  exact hcount.trans (by simpa only [mul_assoc] using hprob)

end BerryEsseen

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem accumulatedNoiseVariance_tendsto_of_flat_interval
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ y ∂(P j).measure, |y| ≤ ε j) (hQ : ∀ j, ∀ᵐ y ∂(Q j).measure, |y| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (x : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hx : Tendsto (fun j => (x j - (n j : ℝ) * p j) / Real.sqrt (n j : ℝ)) atTop (𝓝 0))
    (hflat : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (x j + d) -
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (x j))) atTop (𝓝 0)) :
    Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro Lstar hLstar
  obtain ⟨c, hc, hmass⟩ := twoCluster_local_mass_above_variance W S B I P Q p ε hp hcentral hplim hε hεlim hP hQ n hn hn2
    Lstar hLstar 1 0 d (by norm_num) hd
  filter_upwards [hmass, hflat.eventually (gt_mem_nhds hc), Metric.tendsto_nhds.1 hx 1 (by norm_num)] with j hjmass hjflat hjx
  have hpI : p j ∈ Icc 0 1 := ⟨(hp j).1.le, (hp j).2.le⟩
  letI := twoClusterMeasure_probability (P j) (Q j) (p j) hpI
  have hnonneg := accumulatedNoiseVariance_nonneg (P j) (Q j) (p j) hpI (n j)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  by_contra hcontra
  have hL := le_of_not_gt hcontra
  have hn0 : (0 : ℝ) < n j := by exact_mod_cast (show 0 < n j by have := hn2 j; omega)
  have hr := Real.sqrt_pos.2 hn0
  have hxc : |x j - (n j : ℝ) * p j| ≤ 1 * Real.sqrt (n j : ℝ) := by
    have h := hjx.le
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hr] at h
    exact (div_le_iff₀ hr).1 h
  have hprob := hjmass hL (x j) hxc
  simp only [add_zero] at hprob
  have hmono : (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)).real (Ioo (x j) (x j + d)) ≤
      (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)).real (Ioc (x j) (x j + d)) :=
    measureReal_mono Ioo_subset_Ioc_self
  rw [← cdf_interval_mass _ (by linarith)] at hmono
  have h := (div_le_iff₀ hr).1 (hprob.trans hmono)
  nlinarith only [h, hjflat]

end BerryEsseen
