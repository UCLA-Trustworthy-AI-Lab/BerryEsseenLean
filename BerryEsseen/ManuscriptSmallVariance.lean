import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptSmallVarianceSetup
import BerryEsseen.ManuscriptSmallVarianceCompactness

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- Uniform selection of the original central and far error budgets. The
positive loss is retained before the supremum over all thresholds is taken. -/
theorem manuscript_small_variance_uniform_gap
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) :
    ∃ d : ℝ, 0 < d ∧ d < manuscriptParameterRadius ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ (P Q : CenteredFourthLaw) (p : ℝ), |p - pE| ≤ d →
        (∀ᵐ x ∂P.measure, |x| ≤ d) → (∀ᵐ x ∂Q.measure, |x| ≤ d) →
        ∀ n, N ≤ n → accumulatedNoiseVariance P Q p n ≤ d →
          rawNormalizedConstant (twoClusterMeasure P Q p) n ≤
            rawNormalizedConstant (bernoulliMeasure p) n -
              manuscriptSmallVarianceGap d d (accumulatedNoiseVariance P Q p n) := by
  by_contra hbad
  push_neg at hbad
  let d : ℕ → ℝ := fun j => manuscriptParameterRadius / ((j : ℝ) + 2)
  have hdpos : ∀ j, 0 < d j := fun j => div_pos manuscriptParameterRadius_pos (by positivity)
  have hdlt : ∀ j, d j < manuscriptParameterRadius := by
    intro j
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)).mpr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith only [mul_nonneg manuscriptParameterRadius_pos.le hj, manuscriptParameterRadius_pos]
  have hdlim : Tendsto d atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).atTop_add
        (tendsto_const_nhds (x := (2 : ℝ))))
  have hfailed (j : ℕ) : ∃ (P Q : CenteredFourthLaw) (p : ℝ), |p - pE| ≤ d j ∧
      (∀ᵐ x ∂P.measure, |x| ≤ d j) ∧ (∀ᵐ x ∂Q.measure, |x| ≤ d j) ∧
      ∃ n : ℕ, j + 2 ≤ n ∧ accumulatedNoiseVariance P Q p n ≤ d j ∧
        rawNormalizedConstant (bernoulliMeasure p) n -
          manuscriptSmallVarianceGap (d j) (d j) (accumulatedNoiseVariance P Q p n) <
        rawNormalizedConstant (twoClusterMeasure P Q p) n :=
    hbad (d j) (hdpos j) (hdlt j) (j + 2) (by omega)
  choose P Q p hclose hP hQ n hnj hlamupper hviol using hfailed
  have hpdata (j : ℕ) := manuscript_small_parameter_bounds (d j) (p j) (hdlt j).le (hclose j)
  have hp : ∀ j, p j ∈ Ioo 0 1 := by
    intro j
    have h := (hpdata j).1
    constructor <;> linarith [h.1, h.2]
  have hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5) := by
    intro j
    exact ⟨(hpdata j).1.1, (hpdata j).1.2.trans (by norm_num)⟩
  have hplim : Tendsto p atTop (𝓝 pE) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hdlim.eventually (gt_mem_nhds hε)] with j hj
    rw [Real.dist_eq]
    exact (hclose j).trans_lt hj
  have hn : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun j => (show j ≤ j + 2 by omega).trans (hnj j)) tendsto_id
  have hn2 : ∀ j, 2 ≤ n j := fun j => (show 2 ≤ j + 2 by omega).trans (hnj j)
  have hn1 : ∀ j, 1 ≤ n j := fun j => (by norm_num : 1 ≤ 2).trans (hn2 j)
  have hlam : Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => accumulatedNoiseVariance_nonneg (P j) (Q j) (p j)
      ⟨(hp j).1.le, (hp j).2.le⟩ (n j)) hlamupper hdlim
  have hthreshold (j : ℕ) := manuscript_small_variance_bad_threshold (P j) (Q j)
    (p j) (d j) (d j) (hp j) (hdpos j) (n j) (hn1 j) (hviol j)
  have hlampos : ∀ j, 0 < accumulatedNoiseVariance (P j) (Q j) (p j) (n j) := fun j => (hthreshold j).1
  choose k u hu hpoint using fun j => (hthreshold j).2
  exact manuscript_small_variance_bad_sequence_impossible W S B P Q p d hp hcentral hplim
    (fun j => (hdpos j).le) hdlim (fun j => (hpdata j).2.1) (fun j => (hpdata j).2.2)
    hP hQ n hn hn2 hlam hlampos (manuscript_binomial_constant_tendsto W S B p hp hplim n hn hn1)
    k u d hu hdpos hdlim hpoint

/-- Manuscript Lemma 3.3, proved by the manuscript central-loss and ordinary
binomial-envelope route. The final premises are only the published smoothing
and Bernoulli bounds; no effective stability result is invoked. -/
theorem manuscript_small_cluster_variance
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) :
    ∃ (a b ε lam : ℝ) (N : ℕ),
      a < b ∧ IsCompact (Icc a b) ∧ Icc a b ⊆ Ioo (0 : ℝ) (1 / 2) ∧
      pE ∈ Ioo a b ∧ 0 < ε ∧ 0 < lam ∧
      ∀ (P Q : CenteredFourthLaw) (p : ℝ), p ∈ Icc a b →
        (∀ᵐ x ∂P.measure, |x| ≤ ε) → (∀ᵐ x ∂Q.measure, |x| ≤ ε) →
        ∀ n, N ≤ n → accumulatedNoiseVariance P Q p n ≤ lam →
          rawNormalizedConstant (twoClusterMeasure P Q p) n ≤ rawNormalizedConstant (bernoulliMeasure p) n ∧
          rawNormalizedConstant (bernoulliMeasure p) n < cE ∧
          (0 < averageNoiseVariance P Q p →
            rawNormalizedConstant (twoClusterMeasure P Q p) n < rawNormalizedConstant (bernoulliMeasure p) n) := by
  obtain ⟨d, hd, hdrad, N, hN, hgap⟩ := manuscript_small_variance_uniform_gap W S B
  refine ⟨pE - d, pE + d, d, d, N, by linarith, isCompact_Icc, ?_, ?_, hd, hd, ?_⟩
  · intro p hp
    have hclose : |p - pE| ≤ d := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hc := (manuscript_small_parameter_bounds d p hdrad.le hclose).1
    constructor <;> linarith [hc.1, hc.2]
  · constructor <;> linarith
  · intro P Q p hp hP hQ n hn hlam
    have hclose : |p - pE| ≤ d := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hc := (manuscript_small_parameter_bounds d p hdrad.le hclose).1
    have hpI : p ∈ Ioo 0 1 := by constructor <;> linarith [hc.1, hc.2]
    have hn1 : 1 ≤ n := (by norm_num : 1 ≤ 2).trans (hN.trans hn)
    have hg := hgap P Q p hclose hP hQ n hn hlam
    have hlam0 := accumulatedNoiseVariance_nonneg P Q p ⟨hpI.1.le, hpI.2.le⟩ n
    have hgnonneg := manuscriptSmallVarianceGap_nonneg d d _ hd.le hlam0
    refine ⟨hg.trans (sub_le_self _ hgnonneg), ?_, ?_⟩
    · rw [rawNormalizedConstant_bernoulli p hpI n hn1]
      exact binomialNormalizedConstant_lt_cE B p hpI n hn1
    · intro hs
      have hlampos : 0 < accumulatedNoiseVariance P Q p n :=
        mul_pos (by exact_mod_cast (show 0 < n by omega)) hs
      exact hg.trans_lt (sub_lt_self _ (manuscriptSmallVarianceGap_pos d d _ hd hlampos))

end BerryEsseen
