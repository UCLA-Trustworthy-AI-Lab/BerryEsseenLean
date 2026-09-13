import BerryEsseen.ExtremizerSupport
import BerryEsseen.SupportSeparation
import BerryEsseen.ExtremizerLimit
import BerryEsseen.PublishedWassersteinThree

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The original Proposition 4.5 compact tail, from the global Gaussian
bound and the negative cubic influence budget. The witness 10 is obtained
in the body proof; no effective appendix support bound is used. -/
theorem selected_extremizer_compact_tail (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0)) :
    ∃ J : ℕ, ∀ j : ℕ, 2 ≤ n (j + J) ∧
      (P (j + J)).measure.support ⊆ Icc (-10) 10 := by
  have he : ∀ᶠ j in atTop, 2 ≤ n j ∧ (P j).measure.support ⊆ Icc (-10) 10 := by
    filter_upwards [hn.eventually_ge_atTop 2,
      hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hj hjd
    refine ⟨hj, ?_⟩
    exact (extremizer_support_subset_ten H (P j) (n j) (by omega) (t j) (hattain j)
      (by rw [hattain j]; exact hv j) hjd.le).trans Ioo_subset_Icc_self
  obtain ⟨J, hJ⟩ := eventually_atTop.1 he
  exact ⟨J, fun j => hJ (j + J) (by omega)⟩

/-- The original support-interval conclusion, with no fixed numeric support
restriction. The shared selected-sequence hypotheses force a suitable tail. -/
theorem extremizer_support_limit_interval_general (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (v : ℕ → ℝ) (y : ℝ) (hvSupp : ∀ j, v j ∈ (P j).measure.support)
    (hy : Tendsto v atTop (𝓝 y)) :
    y ∈ Icc (-(Real.sqrt 10 / 2 * aE)) (Real.sqrt 10 / 2 * bE) := by
  obtain ⟨J, hJ⟩ := selected_extremizer_compact_tail H P n t hn hattain hv hd
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  exact extremizer_support_limit_interval H (fun j => P (j + J)) (fun j => n (j + J))
    (fun j => t (j + J)) (hn.comp hshift) (fun j => le_trans (by norm_num : 1 ≤ 2) (hJ j).1)
    (fun j => hattain _) (fun j => hv _) (hd.comp hshift) (hw.comp hshift) (hz.comp hshift)
    (fun j => ((hJ j).2).trans (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    (fun j => v (j + J)) y (fun j => hvSupp _) (hy.comp hshift)

/-- The original separation conclusion along an identified selected sequence,
with an arbitrary initial common support bound (and in fact no such bound
needed in the formal statement). -/
theorem extremizer_support_limit_separation_general
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (x y : ℕ → ℝ) (a b : ℝ) (hxsupp : ∀ j, x j ∈ (P j).measure.support)
    (hysupp : ∀ j, y j ∈ (P j).measure.support)
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b)) :
    a = b ∨ hE ≤ |a - b| := by
  obtain ⟨J, hJ⟩ := selected_extremizer_compact_tail H P n t hn hattain hv hd
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  exact extremizer_support_limit_separation H W S (fun j => P (j + J)) (fun j => n (j + J))
    (fun j => t (j + J)) (hn.comp hshift) (fun j => (hJ j).1)
    (fun j => hattain _) (fun j => hv _) (hw.comp hshift) (hz.comp hshift)
    (fun j => ((hJ j).2).trans (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
    (fun j => x (j + J)) (fun j => y (j + J)) a b
    (fun j => hxsupp _) (fun j => hysupp _) (hx.comp hshift) (hy.comp hshift)

/-- Extraction for every original selected sequence, preserving the original
indexing in the returned subsequence. The weak and third-moment limits below
are the ingredients for the separate Wasserstein-three topology interface. -/
theorem selected_extremizer_identified_subsequence
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      Tendsto (fun j => (P (u j)).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P (u j))) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P (u j))) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t (u j) / Real.sqrt (n (u j) + 1 : ℝ)) atTop (𝓝 0) := by
  obtain ⟨J, hJ⟩ := selected_extremizer_compact_tail H P n t hn hattain hv hd
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  have hv' (j : ℕ) : cE < signedRatio (P j) (n j) (t j) := by rw [hattain j]; exact hv j
  have hβ (j : ℕ) : thirdMoment (P (j + J)) ≤ 2 := by
    have hc := (extremizer_thirdMoment_cutoff H (P (j + J)) (n (j + J)) (t (j + J)) (hv' _)).le
    linarith [momentCutoff_bounds.2]
  have hb (j : ℕ) : ∀ᵐ x ∂(P (j + J)).measure, |x| ≤ 10 := by
    filter_upwards [(P (j + J)).measure.support_mem_ae] with x hx
    have hs := (hJ j).2 hx
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have hn' : Tendsto (fun j => n (j + J) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (hn.comp hshift)
  have hn2' (j : ℕ) : 2 ≤ n (j + J) + 1 := by have := (hJ j).1; omega
  have hviol (j : ℕ) : cE * thirdMoment (P (j + J)) ≤
      Real.sqrt ((n (j + J) + 1 : ℕ) : ℝ) *
        (normalizedSumCDF (P (j + J)) (n (j + J) + 1)
          (t (j + J) / Real.sqrt (n (j + J) + 1 : ℝ)) -
          normalCDF (t (j + J) / Real.sqrt (n (j + J) + 1 : ℝ))) := by
    have hh := signedRatio_violation_scaled (P (j + J)) (n (j + J) + 1) (hn2' j)
      (t (j + J)) (by simpa only [Nat.add_sub_cancel] using hv' (j + J))
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  obtain ⟨u, hu, hw, hβlim, hκlim, hz⟩ := bounded_violating_subsequence W S E
    (fun j => P (j + J)) hβ hb (fun j => n (j + J) + 1) hn' hn2'
    (fun j => t (j + J) / Real.sqrt (n (j + J) + 1 : ℝ)) hviol
  refine ⟨fun j => u j + J, ?_, hw, hβlim, hκlim, hz⟩
  intro i j hij
  exact Nat.add_lt_add_right (hu hij) J

/-- Full `lem:limit-extremizer` for the original selected-sequence hypotheses,
with actual Wasserstein-three convergence and no fixed support constant. -/
theorem selected_extremizer_wassersteinThree_subsequence
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      Tendsto (fun j => (P (u j)).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P (u j))) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P (u j))) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t (u j) / Real.sqrt (n (u j) + 1 : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun j => wassersteinThree (P (u j)).measure esseenLaw.measure) atTop (𝓝 0) := by
  obtain ⟨u, hu, hw, hβ, hκ, hz⟩ :=
    selected_extremizer_identified_subsequence H W S E P n t hn hattain hv hd
  refine ⟨u, hu, hw, hβ, hκ, hz, ?_⟩
  apply (standardized_wassersteinThree_tendsto_iff W (fun j => P (u j)) esseenLaw).2
  exact ⟨hw, by simpa only [thirdMoment_esseen] using hβ⟩

end BerryEsseen
