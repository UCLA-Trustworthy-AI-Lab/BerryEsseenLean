import BerryEsseen.ManuscriptEffectiveSmallVarianceCentral

/-! The original effective small-variance lemma, including the variance-scaled
error absorption. Only the published Bernoulli and nonuniform bounds remain
external inputs; smoothing and the clipping lemma are proved internally. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_effective_small_variance_absorption_budget (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (ε lam : ℝ) (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hlam : lam ∈ Ioc 0 (1 / (10 : ℝ) ^ 12)) :
    20000000 * (lam + ε ^ 2) + 100 / Real.sqrt (n : ℝ) < 21 / (10 : ℝ) ^ 6 ∧
    (1 / 600 : ℝ) < (5 / (10 : ℝ) ^ 9) / Real.sqrt (5 * lam + ε ^ 2) := by
  have hε2 : ε ^ 2 ≤ 1 / (10 : ℝ) ^ 24 := by
    have h := pow_le_pow_left₀ hε.1 hε.2 2
    norm_num at h ⊢
    exact h
  have hr := effective_binomial_root_lower n hn
  have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 100)
    (by positivity : (0 : ℝ) < 10 ^ 50) hr
  have hq : 0 < Real.sqrt (5 * lam + ε ^ 2) := Real.sqrt_pos.mpr (by have h := hlam.1; positivity)
  have hqsmall : Real.sqrt (5 * lam + ε ^ 2) ≤ 1 / 400000 := by
    have hs := Real.sq_sqrt (show 0 ≤ 5 * lam + ε ^ 2 by have h := hlam.1; positivity)
    nlinarith [hlam.2]
  constructor
  · nlinarith [hlam.2]
  · apply (lt_div_iff₀ hq).mpr
    nlinarith only [hqsmall]

theorem manuscript_effective_small_variance_absorption (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (ε lam : ℝ) (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hlam : lam ∈ Ioc 0 (1 / (10 : ℝ) ^ 12)) :
    -(1 / (10 : ℝ) ^ 8 * lam / Real.sqrt (5 * lam + ε ^ 2)) +
      20000000 * lam * (lam + ε ^ 2) + 100 * lam / Real.sqrt (n : ℝ) ≤
      -(5 / (10 : ℝ) ^ 9 * lam / Real.sqrt (5 * lam + ε ^ 2)) := by
  have hb := manuscript_effective_small_variance_absorption_budget n hn ε lam hε hlam
  have hc : 20000000 * (lam + ε ^ 2) + 100 / Real.sqrt (n : ℝ) ≤
      (5 / (10 : ℝ) ^ 9) / Real.sqrt (5 * lam + ε ^ 2) := by
    linarith only [hb.1, hb.2]
  have hm := mul_le_mul_of_nonneg_right hc hlam.1.le
  ring_nf at hm ⊢
  nlinarith only [hm]

theorem manuscript_effective_small_variance_central (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12))
    (hz : |binomialZ p n k| ≤ 5) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      binomialNormalizedConstant p n -
        5 / (10 : ℝ) ^ 9 * accumulatedNoiseVariance P Q p n /
          Real.sqrt (5 * accumulatedNoiseVariance P Q p n + ε ^ 2) := by
  have hc := manuscript_effective_small_variance_central_remainder B P Q p ε hp hε hP hQ n k hn hk hlam hz u hu
  have ha := manuscript_effective_small_variance_absorption n hn ε (accumulatedNoiseVariance P Q p n) hε hlam
  linarith only [hc, ha]

theorem manuscript_effective_small_variance_positive_pointwise
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12)) (x : ℝ) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n x ≤
      binomialNormalizedConstant p n - effectiveSmallVarianceGap (accumulatedNoiseVariance P Q p n) ε := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hn1 : 1 ≤ n := by omega
  let a := Real.sqrt ((n : ℝ) * clusterVariance P Q p)
  let t := a * x + n * p
  let k : ℤ := round t
  let u := t - k
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast (by omega : 0 < n)) (clusterVariance_pos P Q p hp01))
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hx : ((k : ℝ) + u - (n : ℝ) * p) / a = x := by
    dsimp only [u, t]
    field_simp
    <;> ring
  by_cases hz : |binomialZ p n k| ≤ 5
  · have hk := effective_binomial_central_index p hp n hn k (by linarith)
    have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.1
    have hzNat : |binomialZ p n (k.toNat : ℤ)| ≤ 5 := by rwa [hkcast]
    have hc := manuscript_effective_small_variance_central B P Q p ε hp hε hP hQ n k.toNat hn hk.2 hlam hzNat u hu
    have hkReal : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hkcast
    change normalizedDiscrepancy _ n (((k.toNat : ℝ) + u - n * p) / a) ≤ _ at hc
    rw [hkReal, hx] at hc
    apply hc.trans
    exact sub_le_sub_left (min_le_left _ _) _
  · have hs0 := averageNoiseVariance_nonneg P Q p hpcc
    have hsle := (averageNoiseVariance_le_accumulated P Q p hpcc n hn1).trans hlam.2
    have hfar := effective_small_variance_far_argument p (averageNoiseVariance P Q p) hp ⟨hs0, hsle⟩ n hn k (lt_of_not_ge hz) u hu
    have hV : p * (1 - p) + averageNoiseVariance P Q p = clusterVariance P Q p := by
      unfold clusterVariance averageNoiseVariance
      ring
    rw [hV] at hfar
    change (4.9 : ℝ) ≤ |((k : ℝ) + u - n * p) / a| at hfar
    rw [hx] at hfar
    have hD := normalizedDiscrepancy_far_four_point_nine U (standardizedTwoClusterLaw P Q p hp01) n hn1 x hfar
    have hR := (manuscript_effective_binomial_constant_lower p hp n hn).2
    have hgap : effectiveSmallVarianceGap (accumulatedNoiseVariance P Q p n) ε ≤ 1 / 10 := min_le_right _ _
    linarith only [hD, hR, hgap]

theorem manuscript_effective_small_variance_positive
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12)) :
    sSup (Set.range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) ≤
      binomialNormalizedConstant p n - effectiveSmallVarianceGap (accumulatedNoiseVariance P Q p n) ε := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact manuscript_effective_small_variance_positive_pointwise B U P Q p ε hp hε hP hQ n hn hlam x

theorem manuscript_effective_small_variance
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ≤ 1 / (10 : ℝ) ^ 12) :
    sSup (Set.range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) ≤
      binomialNormalizedConstant p n ∧ binomialNormalizedConstant p n < cE := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hn1 : 1 ≤ n := by omega
  refine ⟨?_, binomialNormalizedConstant_lt_cE B p hp01 n hn1⟩
  have hl0 := accumulatedNoiseVariance_nonneg P Q p ⟨hp01.1.le, hp01.2.le⟩ n
  by_cases hz : accumulatedNoiseVariance P Q p n = 0
  · rw [zero_noise_standardizedLaw P Q p hp01 n hn1 hz, ← binomialNormalizedConstant_eq_sup p hp01 n hn1]
  · have hpositive : 0 < accumulatedNoiseVariance P Q p n := lt_of_le_of_ne hl0 (Ne.symm hz)
    have h := manuscript_effective_small_variance_positive B U P Q p ε hp hε hP hQ n hn ⟨hpositive, hlam⟩
    exact h.trans (sub_le_self _ (effectiveSmallVarianceGap_nonneg _ _ hl0))

end BerryEsseen
