import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.TwoClusterLocalMass
import BerryEsseen.GeneralBinomialMass
import BerryEsseen.EffectiveJitterGap
import BerryEsseen.ManuscriptWeightedJitter
import BerryEsseen.GeneralBinomialAsymptotics
import BerryEsseen.ManuscriptGeneralLocalMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def generalLocalNoiseMassConstant (Lstar a b : ℝ) : ℝ :=
  manuscriptGeneralLocalC1 Lstar a b / 2

theorem generalLocalNoiseMassConstant_pos (Lstar a b : ℝ) (hab : a < b) :
    0 < generalLocalNoiseMassConstant Lstar a b := by
  have := manuscriptGeneralLocalC1_pos Lstar a b hab
  unfold generalLocalNoiseMassConstant
  positivity

theorem twoCluster_local_mass_of_central_binomial_bound
    (I : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (p δ ε Lstar R a b c : ℝ) (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ 1 - p)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hP : ∀ᵐ y ∂P.measure, |y| ≤ ε) (hQ : ∀ᵐ y ∂Q.measure, |y| ≤ ε)
    (hLstar : 0 < Lstar) (hR : 0 ≤ R) (hab : a < b) (hc : 0 < c)
    (hεC : ε ≤ manuscriptGeneralLocalEpsilon Lstar a b)
    (n : ℕ) (hn : 1 ≤ n)
    (hlarge : 2 * (R + 2) ≤ δ * Real.sqrt (n : ℝ))
    (hbin : ∀ k : ℕ, k ≤ n → |(k : ℝ) - n * p| ≤ (R + 2) * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k)
    (hL : Lstar ≤ accumulatedNoiseVariance P Q p n)
    (x : ℝ) (hx : |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ)) :
    c * generalLocalNoiseMassConstant Lstar a b / Real.sqrt (n : ℝ) ≤
      (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x + a) (x + b)) := by
  let L := accumulatedNoiseVariance P Q p n
  let r := Real.sqrt (n : ℝ)
  let K := integerWindow x (max 1 (Real.sqrt L))
  let C := generalLocalNoiseMassConstant Lstar a b
  have hC : 0 < C := generalLocalNoiseMassConstant_pos Lstar a b hab
  have hLpos : 0 < L := hLstar.trans_le hL
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hpI : p ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
  have hLn : L ≤ n := by
    have hbound := accumulatedNoiseVariance_le_noise_bound P Q p ε hpI hε hP hQ n
    have heps : ε ^ 2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left heps hn0.le
    nlinarith only [hbound, hm]
  have hgeo := manuscript_general_integer_window_geometry p δ R L x hδ hp hq hR n hn hLn hlarge hx
  have hK : K ⊆ Finset.range (n + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (by have := (hgeo.2.2 k hk).1; omega)
  have hweights : ∀ k ∈ K, c / r ≤ binomialWeight p n k := by
    intro k hk
    exact hbin k (hgeo.2.2 k hk).1 (hgeo.2.2 k hk).2
  have hnoise : ∀ k ∈ K, C / Real.sqrt L ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo ((x + a) - k) ((x + b) - k)) := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    have ht := manuscript_general_noise_variance_window P Q p δ (R + 2) hδ hp hq (by linarith)
      n k hn hkgeo.1 hkgeo.2 hlarge
    have hkx := integerWindow_distance x (max 1 (Real.sqrt L)) hgeo.1 (by positivity) k hk
    have h := manuscript_general_noise_block_window I P Q ε hε hP hQ n k hn hkgeo.1
      Lstar L x a b hLstar hL hab ht.1 ht.2 hkx hεC
    simpa only [C, generalLocalNoiseMassConstant, div_div] using h
  have hprob := twoCluster_open_interval_lower_of_blocks P Q p hpI n (x + a) (x + b)
    (by linarith) K hK (c / r) (C / Real.sqrt L) (by positivity) (by positivity) hweights hnoise
  have hcard : Real.sqrt L ≤ (K.card : ℝ) := (le_max_right 1 (Real.sqrt L)).trans
    (integerWindow_card_lower x (max 1 (Real.sqrt L)) hgeo.1 (le_max_left _ _))
  have hcount := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ c / r * (C / Real.sqrt L))
  have he : Real.sqrt L * (c / r * (C / Real.sqrt L)) = c * C / r := by
    field_simp [(Real.sqrt_pos.mpr hLpos).ne']
  rw [he] at hcount
  exact hcount.trans (by simpa only [mul_assoc] using hprob)

/-- Uniformization of the noise-block proof, with an explicit already-proved
central binomial estimate supplied as a helper hypothesis. -/
theorem compact_twoCluster_local_mass_from_binomial
    (I : PublishedNonIIDBound) (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (Lstar R a b : ℝ) (hLstar : 0 < Lstar) (hR : 0 ≤ R) (hab : a < b)
    (hbin : ∃ c > 0, ∃ N : ℕ, ∀ p ∈ K, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n →
      |(k : ℝ) - n * p| ≤ (R + 2) * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k) :
    ∃ ε > 0, ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ (P Q : CenteredFourthLaw) (p : ℝ), p ∈ K →
      (∀ᵐ y ∂P.measure, |y| ≤ ε) → (∀ᵐ y ∂Q.measure, |y| ≤ ε) →
      ∀ n : ℕ, N ≤ n → Lstar ≤ accumulatedNoiseVariance P Q p n →
      ∀ x : ℝ, |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ) →
        c / Real.sqrt (n : ℝ) ≤ (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x + a) (x + b)) := by
  obtain ⟨δ, hδ, hmargin⟩ := compact_bernoulli_parameter_margin K hK hKI
  obtain ⟨cbin, hcbin, Nbin, hbin⟩ := hbin
  let C := generalLocalNoiseMassConstant Lstar a b
  have hC : 0 < C := generalLocalNoiseMassConstant_pos Lstar a b hab
  let ε := min 1 (manuscriptGeneralLocalEpsilon Lstar a b)
  have hε : 0 < ε := lt_min (by norm_num) (manuscriptGeneralLocalEpsilon_pos Lstar a b hab)
  have hs : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ngeo, hgeo⟩ := eventually_atTop.mp (hs.eventually_ge_atTop (2 * (R + 2) / δ))
  let N := max 1 (max Nbin Ngeo)
  have hN1 : 1 ≤ N := le_max_left _ _
  refine ⟨ε, hε, cbin * C, mul_pos hcbin hC, N, hN1, ?_⟩
  intro P Q p hp hP hQ n hn hL x hx
  have hn1 : 1 ≤ n := hN1.trans hn
  have hnB : Nbin ≤ n := (le_trans (le_max_left Nbin Ngeo) (le_max_right 1 _)).trans hn
  have hnG : Ngeo ≤ n := (le_trans (le_max_right Nbin Ngeo) (le_max_right 1 _)).trans hn
  have hlarge : 2 * (R + 2) ≤ δ * Real.sqrt (n : ℝ) := by
    have hh := (div_le_iff₀ hδ).mp (hgeo n hnG)
    nlinarith only [hh]
  exact twoCluster_local_mass_of_central_binomial_bound I P Q p δ ε Lstar R a b cbin
    hδ (hmargin p hp).1 (hmargin p hp).2 hε.le (min_le_left _ _) hP hQ
    hLstar hR hab hcbin (min_le_right _ _) n hn1 hlarge (hbin p hp n hnB) hL x hx

theorem compact_centered_measure_local_mass_from_binomial
    (I : PublishedNonIIDBound) (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (Lstar R a b : ℝ) (hLstar : 0 < Lstar) (hR : 0 ≤ R) (hab : a < b)
    (hbin : ∃ c > 0, ∃ N : ℕ, ∀ p ∈ K, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n →
      |(k : ℝ) - n * p| ≤ (R + 2) * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k) :
    ∃ ε > 0, ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∫ x, x ∂μ) = 0 → (∫ x, x ∂ν) = 0 →
      (∀ᵐ y ∂μ, |y| ≤ ε) → (∀ᵐ y ∂ν, |y| ≤ ε) →
      ∀ p ∈ K, ∀ n : ℕ, N ≤ n →
        Lstar ≤ (n : ℝ) * ((1 - p) * (∫ x, x ^ 2 ∂μ) + p * (∫ x, x ^ 2 ∂ν)) →
        ∀ x : ℝ, |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ) →
          c / Real.sqrt (n : ℝ) ≤
            (iidSumLaw (mixtureMeasure μ (ν.map (fun y => 1 + y)) p) n).real
              (Ioo (x + a) (x + b)) := by
  obtain ⟨ε, hε, c, hc, N, hN, hmass⟩ :=
    compact_twoCluster_local_mass_from_binomial I K hK hKI Lstar R a b hLstar hR hab hbin
  refine ⟨ε, hε, c, hc, N, hN, ?_⟩
  intro μ ν hμ hν hmμ hmν hbμ hbν p hp n hn hL x hx
  letI := hμ
  letI := hν
  let P := CenteredFourthLaw.ofBounded μ ε hbμ hmμ
  let Q := CenteredFourthLaw.ofBounded ν ε hbν hmν
  exact hmass P Q p hp hbμ hbν n hn hL x hx

theorem compact_accumulatedNoiseVariance_tendsto_of_flat_interval_from_binomial
    (I : PublishedNonIIDBound) (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (hbin : ∃ c > 0, ∃ N : ℕ, ∀ p ∈ K, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n →
      |(k : ℝ) - n * p| ≤ 3 * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ) (hp : ∀ j, p j ∈ K)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ y ∂(P j).measure, |y| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ y ∂(Q j).measure, |y| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (x : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hx : Tendsto (fun j => (x j - (n j : ℝ) * p j) / Real.sqrt (n j : ℝ)) atTop (𝓝 0))
    (hflat : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (x j + d) -
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (x j))) atTop (𝓝 0)) :
    Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro Lstar hLstar
  obtain ⟨εstar, hεstar, c, hc, N, hN, hmass⟩ :=
    compact_twoCluster_local_mass_from_binomial I K hK hKI Lstar 1 0 d hLstar
      (by norm_num) hd (by simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hbin)
  filter_upwards [hn.eventually (eventually_ge_atTop N),
    hεlim.eventually (gt_mem_nhds hεstar), hflat.eventually (gt_mem_nhds hc),
    Metric.tendsto_nhds.1 hx 1 (by norm_num)] with j hjN hjε hjflat hjx
  have hpI : p j ∈ Icc 0 1 := ⟨(hKI (hp j)).1.le, (hKI (hp j)).2.le⟩
  letI := twoClusterMeasure_probability (P j) (Q j) (p j) hpI
  have hnonneg := accumulatedNoiseVariance_nonneg (P j) (Q j) (p j) hpI (n j)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  by_contra hcontra
  have hL := le_of_not_gt hcontra
  have hn0 : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by have := hn2 j; omega)
  have hr := Real.sqrt_pos.mpr hn0
  have hxc : |x j - (n j : ℝ) * p j| ≤ 1 * Real.sqrt (n j : ℝ) := by
    have hh := hjx.le
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hr] at hh
    exact (div_le_iff₀ hr).mp hh
  have hprob := hmass (P j) (Q j) (p j) (hp j)
    ((hP j).mono (fun _ hy => hy.trans hjε.le))
    ((hQ j).mono (fun _ hy => hy.trans hjε.le)) (n j) hjN hL (x j) hxc
  simp only [add_zero] at hprob
  have hmono : (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)).real (Ioo (x j) (x j + d)) ≤
      (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)).real (Ioc (x j) (x j + d)) :=
    measureReal_mono Ioo_subset_Ioc_self
  rw [← cdf_interval_mass _ (by linarith)] at hmono
  have hh := (div_le_iff₀ hr).mp (hprob.trans hmono)
  nlinarith only [hh, hjflat]

theorem compact_twoCluster_local_jitter_gaps_from_binomial
    (I : PublishedNonIIDBound) (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (Lstar R : ℝ) (hLstar : 0 < Lstar) (hR : 0 ≤ R)
    (hbin : ∃ c > 0, ∃ N : ℕ, ∀ p ∈ K, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n →
      |(k : ℝ) - n * p| ≤ (R + 2) * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ) (hp : ∀ j, p j ∈ K)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ y ∂(P j).measure, |y| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ y ∂(Q j).measure, |y| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hL : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) :
    ∃ c > 0, ∀ᶠ j in atTop, ∀ x : ℝ,
      |x - (n j : ℝ) * p j| ≤ R * Real.sqrt (n j : ℝ) →
      c / Real.sqrt (n j : ℝ) ≤
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1) (x + 1 / 2) -
          cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) x ∧
      c / Real.sqrt (n j : ℝ) ≤
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) x -
          cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1) (x - 1 / 2) := by
  obtain ⟨εR, hεR, cR, hcR, NR, hNR, hmassR⟩ :=
    compact_twoCluster_local_mass_from_binomial I K hK hKI Lstar R (1 / 4) (1 / 2) hLstar hR
      (by norm_num) hbin
  obtain ⟨εL, hεL, cL, hcL, NL, hNL, hmassL⟩ :=
    compact_twoCluster_local_mass_from_binomial I K hK hKI Lstar R (-1 / 2) (-1 / 4) hLstar hR
      (by norm_num) hbin
  let c := min cR cL / 2
  have hc : 0 < c := div_pos (lt_min hcR hcL) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hn.eventually (eventually_ge_atTop NR), hn.eventually (eventually_ge_atTop NL),
    hεlim.eventually (gt_mem_nhds hεR), hεlim.eventually (gt_mem_nhds hεL), hL]
    with j hjNR hjNL hjεR hjεL hjL
  intro x hx
  have hpI : p j ∈ Icc 0 1 := ⟨(hKI (hp j)).1.le, (hKI (hp j)).2.le⟩
  letI := twoClusterMeasure_probability (P j) (Q j) (p j) hpI
  have hright := hmassR (P j) (Q j) (p j) (hp j)
    ((hP j).mono (fun _ hy => hy.trans hjεR.le))
    ((hQ j).mono (fun _ hy => hy.trans hjεR.le)) (n j) hjNR hjL x hx
  have hleft := hmassL (P j) (Q j) (p j) (hp j)
    ((hP j).mono (fun _ hy => hy.trans hjεL.le))
    ((hQ j).mono (fun _ hy => hy.trans hjεL.le)) (n j) hjNL hjL x hx
  simp only [add_zero, neg_div, ← sub_eq_add_neg] at hright hleft
  have hJU := manuscript_uniform_forward_quarter_gap
    (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) x
  have hJL := manuscript_uniform_backward_quarter_gap
    (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) x
  have hRM := mul_le_mul_of_nonneg_left hright (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hLM := mul_le_mul_of_nonneg_left hleft (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcR' : c ≤ cR / 2 := by dsimp only [c]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hcL' : c ≤ cL / 2 := by dsimp only [c]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hdR := div_le_div_of_nonneg_right hcR' (Real.sqrt_nonneg (n j : ℝ))
  have hdL := div_le_div_of_nonneg_right hcL' (Real.sqrt_nonneg (n j : ℝ))
  rw [show (cR / 2) / Real.sqrt (n j : ℝ) = (1 / 2) * (cR / Real.sqrt (n j : ℝ)) by ring] at hdR
  rw [show (cL / 2) / Real.sqrt (n j : ℝ) = (1 / 2) * (cL / Real.sqrt (n j : ℝ)) by ring] at hdL
  exact ⟨hdR.trans (hRM.trans hJU), hdL.trans (hLM.trans hJL)⟩

theorem compact_binomial_lower_for_noise_window
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ c > 0, ∃ N : ℕ, ∀ p ∈ K, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, k ≤ n →
      |(k : ℝ) - n * p| ≤ (R + 2) * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k := by
  obtain ⟨c, hc, N, hN, hbound⟩ :=
    compact_binomial_central_lower_bound W S K hK hKI (R + 2) (by linarith)
  exact ⟨c, hc, N, hbound⟩

/-- The full compact-parameter uniform local mass lemma, for arbitrary centered
conditional noise laws. The interval probability is genuinely open. -/
theorem compact_twoCluster_local_mass
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (Lstar R a b : ℝ) (hLstar : 0 < Lstar) (hR : 0 ≤ R) (hab : a < b) :
    ∃ ε > 0, ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ (P Q : CenteredFourthLaw) (p : ℝ), p ∈ K →
      (∀ᵐ y ∂P.measure, |y| ≤ ε) → (∀ᵐ y ∂Q.measure, |y| ≤ ε) →
      ∀ n : ℕ, N ≤ n → Lstar ≤ accumulatedNoiseVariance P Q p n →
      ∀ x : ℝ, |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ) →
        c / Real.sqrt (n : ℝ) ≤ (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x + a) (x + b)) :=
  compact_twoCluster_local_mass_from_binomial I K hK hKI Lstar R a b hLstar hR hab
    (compact_binomial_lower_for_noise_window W S K hK hKI R hR)

/-- The same theorem for unbundled actual probability measures, with boundedness
supplying every moment condition automatically. -/
theorem compact_centered_measure_local_mass
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (Lstar R a b : ℝ) (hLstar : 0 < Lstar) (hR : 0 ≤ R) (hab : a < b) :
    ∃ ε > 0, ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∫ x, x ∂μ) = 0 → (∫ x, x ∂ν) = 0 →
      (∀ᵐ y ∂μ, |y| ≤ ε) → (∀ᵐ y ∂ν, |y| ≤ ε) →
      ∀ p ∈ K, ∀ n : ℕ, N ≤ n →
        Lstar ≤ (n : ℝ) * ((1 - p) * (∫ x, x ^ 2 ∂μ) + p * (∫ x, x ^ 2 ∂ν)) →
        ∀ x : ℝ, |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ) →
          c / Real.sqrt (n : ℝ) ≤
            (iidSumLaw (mixtureMeasure μ (ν.map (fun y => 1 + y)) p) n).real
              (Ioo (x + a) (x + b)) :=
  compact_centered_measure_local_mass_from_binomial I K hK hKI Lstar R a b hLstar hR hab
    (compact_binomial_lower_for_noise_window W S K hK hKI R hR)

theorem compact_accumulatedNoiseVariance_tendsto_of_flat_interval
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ) (hp : ∀ j, p j ∈ K)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ y ∂(P j).measure, |y| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ y ∂(Q j).measure, |y| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (x : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hx : Tendsto (fun j => (x j - (n j : ℝ) * p j) / Real.sqrt (n j : ℝ)) atTop (𝓝 0))
    (hflat : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (x j + d) -
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (x j))) atTop (𝓝 0)) :
    Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0) := by
  apply compact_accumulatedNoiseVariance_tendsto_of_flat_interval_from_binomial I K hK hKI
    _ P Q p ε hp hεlim hP hQ n hn hn2 x d hd hx hflat
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    compact_binomial_lower_for_noise_window W S K hK hKI 1 (by norm_num)

theorem compact_twoCluster_local_jitter_gaps
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (Lstar R : ℝ) (hLstar : 0 < Lstar) (hR : 0 ≤ R)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ) (hp : ∀ j, p j ∈ K)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ y ∂(P j).measure, |y| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ y ∂(Q j).measure, |y| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hL : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) :
    ∃ c > 0, ∀ᶠ j in atTop, ∀ x : ℝ,
      |x - (n j : ℝ) * p j| ≤ R * Real.sqrt (n j : ℝ) →
      c / Real.sqrt (n j : ℝ) ≤
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1) (x + 1 / 2) -
          cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) x ∧
      c / Real.sqrt (n j : ℝ) ≤
        cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) x -
          cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1) (x - 1 / 2) :=
  compact_twoCluster_local_jitter_gaps_from_binomial I K hK hKI Lstar R hLstar hR
    (compact_binomial_lower_for_noise_window W S K hK hKI R hR) P Q p ε hp hεlim hP hQ n hn hL

end BerryEsseen
