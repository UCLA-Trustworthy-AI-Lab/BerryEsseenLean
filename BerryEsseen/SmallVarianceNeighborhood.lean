import BerryEsseen.RawNormalization

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem rawNormalizedConstant_twoCluster (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) :
    rawNormalizedConstant (twoClusterMeasure P Q p) n =
      sSup (range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n)) := by
  letI := twoClusterMeasure_probability P Q p ⟨hp.1.le, hp.2.le⟩
  exact rawNormalizedConstant_eq _ _ p (Real.sqrt (clusterVariance P Q p))
    (Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp))
    (standardizedTwoClusterLaw_measure P Q p hp) n hn

theorem rawNormalizedConstant_bernoulli (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) :
    rawNormalizedConstant (bernoulliMeasure p) n = binomialNormalizedConstant p n := by
  rw [← twoCluster_zero_noise, rawNormalizedConstant_twoCluster _ _ p hp n hn,
    binomialNormalizedConstant_eq_sup p hp n hn]
  rfl

theorem effectiveSmallVarianceGap_pos (lam ε : ℝ) (hlam : 0 < lam) :
    0 < effectiveSmallVarianceGap lam ε := by
  unfold effectiveSmallVarianceGap
  apply lt_min
  · have hs : 0 < 5 * lam + ε ^ 2 := by nlinarith [sq_nonneg ε]
    exact div_pos (mul_pos (by norm_num) hlam) (Real.sqrt_pos.mpr hs)
  · norm_num

theorem effective_small_variance_raw (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ≤ 1 / (10 : ℝ) ^ 12) :
    rawNormalizedConstant (twoClusterMeasure P Q p) n ≤ rawNormalizedConstant (bernoulliMeasure p) n ∧
      rawNormalizedConstant (bernoulliMeasure p) n < cE ∧
      (0 < averageNoiseVariance P Q p →
        rawNormalizedConstant (twoClusterMeasure P Q p) n < rawNormalizedConstant (bernoulliMeasure p) n) := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hn1 : 1 ≤ n := by omega
  rw [rawNormalizedConstant_twoCluster P Q p hp01 n hn1, rawNormalizedConstant_bernoulli p hp01 n hn1]
  have h := effective_small_variance S B U P Q p ε hp hε hP hQ n hn hlam
  refine ⟨h.1, h.2, ?_⟩
  intro hs
  have hpositive : 0 < accumulatedNoiseVariance P Q p n :=
    mul_pos (by exact_mod_cast (by omega : 0 < n)) hs
  have hg := effective_small_variance_positive S B U P Q p ε hp hε hP hQ n hn ⟨hpositive, hlam⟩
  exact hg.trans_lt (sub_lt_self _ (effectiveSmallVarianceGap_pos _ _ hpositive))

theorem small_cluster_variance (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound) :
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
  refine ⟨2 / 5, 9 / 20, 1 / (10 : ℝ) ^ 12, 1 / (10 : ℝ) ^ 12, 10 ^ 100,
    by norm_num, isCompact_Icc, ?_, pE_bounds, by norm_num, by norm_num, ?_⟩
  · intro p hp
    constructor <;> linarith [hp.1, hp.2]
  · intro P Q p hp hP hQ n hn hlam
    exact effective_small_variance_raw S B U P Q p _ hp (by norm_num) hP hQ n hn hlam

end BerryEsseen
