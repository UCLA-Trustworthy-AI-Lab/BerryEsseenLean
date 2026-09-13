import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptUniformCentralAbsorption
import BerryEsseen.ManuscriptUniformFarBudget
import BerryEsseen.ManuscriptUniformBernoulliLower

/-! Lemma 3.3 with the successive choices in the manuscript.

The initially fixed interval is `[2/5,9/20]`.  Fix gamma, choose the central
window by the ordinary binomial envelopes, reduce the variance and support
cutoffs, shrink the parameter interval using the nearest binomial branch,
and finally take one sample-size bound for all the earlier constraints.
Neither the effective appendix nor a bad-sequence compactness argument is
used to obtain the conclusion. -/
noncomputable section
open MeasureTheory Set
namespace BerryEsseen

def manuscriptOriginalSmallVarianceGap (c γ ε lam : ℝ) : ℝ :=
  min (c * lam / Real.sqrt (3 * lam / (2 / 5) + ε ^ 2)) γ

theorem manuscriptOriginalSmallVarianceGap_nonneg (c γ ε lam : ℝ)
    (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) :
    0 ≤ manuscriptOriginalSmallVarianceGap c γ ε lam := by
  unfold manuscriptOriginalSmallVarianceGap
  exact le_min (by positivity) hγ

theorem manuscriptOriginalSmallVarianceGap_pos (c γ ε lam : ℝ)
    (hc : 0 < c) (hγ : 0 < γ) (hlam : 0 < lam) :
    0 < manuscriptOriginalSmallVarianceGap c γ ε lam := by
  unfold manuscriptOriginalSmallVarianceGap
  exact lt_min (by positivity) hγ

/-- The original uniform gap, with the parameter radius chosen separately
from the noise cutoffs and with every threshold included before the supremum. -/
theorem manuscript_original_parameters_uniform_gap
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) :
    ∃ (r d c γ : ℝ), 0 < r ∧ r < manuscriptParameterRadius ∧ 0 < d ∧ 0 < c ∧ 0 < γ ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ (P Q : CenteredFourthLaw) (p : ℝ), |p - pE| ≤ r →
          (∀ᵐ x ∂P.measure, |x| ≤ d) → (∀ᵐ x ∂Q.measure, |x| ≤ d) →
          ∀ n, N ≤ n → accumulatedNoiseVariance P Q p n ≤ d →
            rawNormalizedConstant (twoClusterMeasure P Q p) n ≤
              rawNormalizedConstant (bernoulliMeasure p) n -
                manuscriptOriginalSmallVarianceGap c γ d (accumulatedNoiseVariance P Q p n) := by
  -- I_* is fixed before every other choice, and gamma is the manuscript gap.
  let γ := (cE - phi0) / 8
  have hγ : 0 < γ := by
    dsimp only [γ]
    have hce := cE_numeric_bounds.1
    have hφ := phi0_lt_two_fifths
    linarith
  have hγeq : 8 * γ = cE - phi0 := by dsimp [γ]; ring
  -- First choose M using the ordinary uniform binomial envelopes on I_*.
  obtain ⟨M, hM, henv⟩ := binomial_envelopes_uniform_tail γ hγ
  have htail : ∀ p ∈ manuscriptInitialInterval, ∀ z : ℝ, M < |z| →
      max (binomialUpperEnvelope p z) (binomialLowerEnvelope p z) ≤ γ := by
    intro p hp z hz
    have hpI := (manuscript_initial_parameter_bounds p hp).1
    have hh := henv p ⟨hpI.1.le, hpI.2.le⟩ z hz.le
    exact max_le ((le_abs_self _).trans hh.1.le) ((le_abs_self _).trans hh.2.le)
  -- Then reduce lambda_0 and epsilon_0 together to d for both error budgets.
  obtain ⟨d, hd, hd100, hdleak, c, hc, Nc, hNc, hcentral⟩ :=
    manuscript_uniform_central_absorption W S B M γ hM hγ
  -- Shrink I using continuity of g(p), followed by its uniform binomial branch.
  obtain ⟨r, hr, hrrad, Nb, hNb, hRb⟩ := manuscript_uniform_bernoulli_lower W S γ hγ
  -- Finally choose one N satisfying the central, far, and binomial constraints.
  obtain ⟨Nf, hNf, hfar⟩ := manuscript_uniform_far_budget W S B γ hγ hγeq M hM htail d hd hd100 hdleak
  let N := max Nc (max Nb Nf)
  have hN2 : 2 ≤ N := hNb.trans ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨r, d, c, γ, hr, hrrad, hd, hc, hγ, N, hN2, ?_⟩
  intro P Q p hp hP hQ n hn hlam
  have hpcc : p ∈ manuscriptInitialInterval := (manuscript_small_parameter_bounds r p hrrad.le hp).1
  have hpI := (manuscript_initial_parameter_bounds p hpcc).1
  have hnNc : Nc ≤ n := (le_max_left Nc _).trans hn
  have hnNb : Nb ≤ n := ((le_max_left Nb Nf).trans (le_max_right Nc _)).trans hn
  have hnNf : Nf ≤ n := ((le_max_right Nb Nf).trans (le_max_right Nc _)).trans hn
  have hn1 : 1 ≤ n := hNc.trans hnNc
  have hlam0 := accumulatedNoiseVariance_nonneg P Q p ⟨hpI.1.le, hpI.2.le⟩ n
  by_cases hz : accumulatedNoiseVariance P Q p n = 0
  · have he := twoCluster_eq_bernoulli_of_zero_variance P Q p hpI n hn1 hz
    simp only [hz, manuscriptOriginalSmallVarianceGap, mul_zero, zero_div,
      min_eq_left hγ.le, sub_zero, he, le_refl]
  have hlampos : 0 < accumulatedNoiseVariance P Q p n := lt_of_le_of_ne hlam0 (Ne.symm hz)
  have hRblower := hRb p hp n hnNb
  rw [rawNormalizedConstant_twoCluster P Q p hpI n hn1]
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x, rfl⟩
  let a := Real.sqrt ((n : ℝ) * clusterVariance P Q p)
  have ha : 0 < a := Real.sqrt_pos.mpr
    (mul_pos (by exact_mod_cast (show 0 < n by omega)) (clusterVariance_pos P Q p hpI))
  let t := (n : ℝ) * p + a * x
  let k : ℤ := round t
  let u : ℝ := t - k
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hpoint : normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hpI) n
      (((k : ℝ) + u - (n : ℝ) * p) / a) ≤
      rawNormalizedConstant (bernoulliMeasure p) n -
        manuscriptOriginalSmallVarianceGap c γ d (accumulatedNoiseVariance P Q p n) := by
    by_cases hzk : |binomialZ p n k| ≤ M
    · have hh := hcentral P Q p hpcc hP hQ n hnNc k hzk hlampos hlam u hu
      exact hh.trans (sub_le_sub_left (min_le_left _ _) _)
    · have hh := hfar P Q p hpcc hP hQ n hnNf hlam k (lt_of_not_ge hzk) u hu
      have hcomp : cE - 2 * γ ≤ rawNormalizedConstant (bernoulliMeasure p) n - γ := by linarith
      exact (hh.trans hcomp).trans (sub_le_sub_left (min_le_right _ _) _)
  have he : ((k : ℝ) + u - (n : ℝ) * p) / a = x := by
    dsimp only [u, t]
    field_simp [ha.ne']
    <;> ring
  rwa [he] at hpoint

/-- Manuscript Lemma 3.3, closed by its original fixed-window parameter
choices.  The strict positive-variance comparison survives the true supremum. -/
theorem manuscript_small_cluster_variance_original_parameters
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
  obtain ⟨r, d, c, γ, hr, hrrad, hd, hc, hγ, N, hN, hgap⟩ := manuscript_original_parameters_uniform_gap W S B
  refine ⟨pE - r, pE + r, d, d, N, by linarith, isCompact_Icc, ?_, ?_, hd, hd, ?_⟩
  · intro p hp
    have hclose : |p - pE| ≤ r := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hpcc := (manuscript_small_parameter_bounds r p hrrad.le hclose).1
    constructor <;> linarith [hpcc.1, hpcc.2]
  · constructor <;> linarith
  · intro P Q p hp hP hQ n hn hlam
    have hclose : |p - pE| ≤ r := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hpcc := (manuscript_small_parameter_bounds r p hrrad.le hclose).1
    have hpI : p ∈ Ioo 0 1 := by constructor <;> linarith [hpcc.1, hpcc.2]
    have hn1 : 1 ≤ n := (by norm_num : 1 ≤ 2).trans (hN.trans hn)
    have hg := hgap P Q p hclose hP hQ n hn hlam
    have hlam0 := accumulatedNoiseVariance_nonneg P Q p ⟨hpI.1.le, hpI.2.le⟩ n
    have hgnonneg := manuscriptOriginalSmallVarianceGap_nonneg c γ d _ hc.le hγ.le hlam0
    refine ⟨hg.trans (sub_le_self _ hgnonneg), ?_, ?_⟩
    · rw [rawNormalizedConstant_bernoulli p hpI n hn1]
      exact binomialNormalizedConstant_lt_cE B p hpI n hn1
    · intro hs
      have hlampos : 0 < accumulatedNoiseVariance P Q p n :=
        mul_pos (by exact_mod_cast (show 0 < n by omega)) hs
      exact hg.trans_lt (sub_lt_self _ (manuscriptOriginalSmallVarianceGap_pos c γ d _ hc hγ hlampos))

end BerryEsseen
