import BerryEsseen.ManuscriptFarComparison
import BerryEsseen.AppliedClusterBounds
import BerryEsseen.EffectiveGaussianTail
import BerryEsseen.PositiveBranch
import BerryEsseen.SumMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The elementary Gaussian exponential tail used for the manuscript's
separate integer indices outside the binomial support. -/
theorem manuscript_normalCDF_exponential_tail (x : ℝ) (hx : 1 ≤ x) :
    1 - normalCDF x ≤ Real.exp (-x ^ 2 / 2) := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := x) (fun y _ => normalCDF_hasDerivAt y)
    standardNormalDensity_integrable.integrableOn normalCDF_tendsto_atTop
  have he : (∫ y in Ioi x, standardNormalDensity y) =
      phi0 * ∫ y in Ioi x, Real.exp (-y ^ 2 / 2) := by
    simp_rw [standardNormalDensity_formula]
    rw [integral_const_mul]
  rw [← hi, he]
  have ht := mul_le_mul_of_nonneg_left (gaussian_tail_integral_le x (by linarith)) phi0_pos.le
  apply ht.trans
  have hφ : phi0 ≤ x := by have := phi0_lt_two_fifths; linarith
  have hmul := mul_le_mul_of_nonneg_right hφ (Real.exp_pos (-x ^ 2 / 2)).le
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by linarith : 0 < x)).mpr
  simpa only [mul_comm x] using hmul

theorem manuscript_binomial_cdf_outside (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    (∀ x : ℝ, x < 0 → cdf (binomialMeasure p n) x = 0) ∧
    (∀ x : ℝ, (n : ℝ) ≤ x → cdf (binomialMeasure p n) x = 1) := by
  constructor
  · intro x hx
    rw [binomialMeasure_cdf p hp]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [if_neg (show ¬ (j : ℝ) ≤ x by have := Nat.cast_nonneg (α := ℝ) j; linarith)]
  · intro x hx
    rw [binomialMeasure_cdf p hp, ← binomialWeight_sum p hp n]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    simp only [if_pos ((show (j : ℝ) ≤ n by exact_mod_cast hjn).trans hx)]

/-- Outside [0,n], the actual two-cluster CDF is bounded by leakage from
baseline zero or one. Its Gaussian comparison is exponentially small.
This is the manuscript's separate outside-support argument, without any
binomial envelope or nonuniform Berry--Esseen estimate. -/
theorem manuscript_twoCluster_outside_gaussian_comparison
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (hcentral : p ∈ Icc (2 / 5) (3 / 5))
    (hv : clusterVariance P Q p ≤ 1)
    (n : ℕ) (hn : 25 ≤ n) (k : ℤ) (hk : k < 0 ∨ (n : ℤ) < k)
    (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      Real.sqrt (n : ℝ) *
        (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
        (Real.exp (-(2 / 25) * (n : ℝ)) + blockLeakageBudget P Q p n k) := by
  let r := Real.sqrt (n : ℝ)
  let a := Real.sqrt ((n : ℝ) * clusterVariance P Q p)
  let z := ((k : ℝ) + u - (n : ℝ) * p) / a
  let F := cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let J := blockLeakageBudget P Q p n k
  let e := Real.exp (-(2 / 25) * (n : ℝ))
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hr5 : 5 ≤ r := by dsimp only [r]; apply (Real.le_sqrt (by norm_num) hn0.le).2; exact_mod_cast hn
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hn0 (clusterVariance_pos P Q p hp))
  have har : a ≤ r := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hv hn0.le])
  have hu' := abs_le.mp hu
  have hpI : p ∈ Icc 0 1 := ⟨hp.1.le, hp.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpI
  have hen := manuscript_block_cdf_enclosure P Q p hpI n k u hu
  have hF0 : 0 ≤ F := cdf_nonneg _ _
  have hF1 : F ≤ 1 := cdf_le_one _ _
  have hg0 : 0 ≤ normalCDF z := by simpa only [cdf_eq_real] using cdf_nonneg (gaussianReal 0 1) z
  have hg1 : normalCDF z ≤ 1 := by simpa only [cdf_eq_real] using cdf_le_one (gaussianReal 0 1) z
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have htail (w : ℝ) (hw : (2 / 5) * r ≤ w) : 1 - normalCDF w ≤ e := by
    have hw1 : 1 ≤ w := by linarith
    apply (manuscript_normalCDF_exponential_tail w hw1).trans
    apply Real.exp_le_exp.mpr
    dsimp only [e]
    nlinarith [sq_nonneg (w - (2 / 5) * r)]
  have hbound : |F - normalCDF z| ≤ e + J := by
    rcases hk with hk | hk
    · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hbase := (manuscript_binomial_cdf_outside p hpI n).1 (k : ℝ) (by linarith)
      rw [hbase, zero_add] at hen
      have hFJ : F ≤ J := hen.2
      have hz : (2 / 5) * r ≤ -z := by
        dsimp only [z]
        rw [← neg_div]
        apply (le_div_iff₀ ha).2
        have hm := mul_le_mul_of_nonneg_left har (show 0 ≤ (2 / 5) * r by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hcentral.1 hn0.le]
      have hg := htail (-z) hz
      rw [normalCDF_reflection] at hg
      rw [abs_le]
      constructor <;> linarith
    · have hkr : (n : ℝ) + 1 ≤ k := by exact_mod_cast (show (n : ℤ) + 1 ≤ k by omega)
      have hbase := (manuscript_binomial_cdf_outside p hpI n).2 ((k : ℝ) - 1) (by linarith)
      rw [hbase] at hen
      have hFlo : 1 - J ≤ F := hen.1.trans (strictCDF_le_cdf _ _)
      have hz : (2 / 5) * r ≤ z := by
        dsimp only [z]
        apply (le_div_iff₀ ha).2
        have hm := mul_le_mul_of_nonneg_left har (show 0 ≤ (2 / 5) * r by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hcentral.2 hn0.le]
      have hg := htail z hz
      rw [abs_le]
      constructor <;> linarith
  have hfac : 0 ≤ r * (Real.sqrt (clusterVariance P Q p) ^ 3 /
      clusterThirdAbsoluteMoment P Q p) := by
    exact mul_nonneg hr.le (div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (clusterThirdAbsoluteMoment_pos P Q p hp).le)
  have hm := mul_le_mul_of_nonneg_left hbound hfac
  rw [standardizedTwoCluster_discrepancy P Q p hp n (by omega)]
  simpa only [r, a, z, F, J, e, mul_div_assoc] using hm

theorem manuscript_cluster_prefactor_le_one (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Ioo 0 1) :
    Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p ≤ 1 := by
  have h := thirdMoment_ge_one (standardizedTwoClusterLaw P Q p hp)
  rw [standardizedTwoClusterLaw_third] at h
  have hσ : 0 < Real.sqrt (clusterVariance P Q p) ^ 3 :=
    pow_pos (Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp)) 3
  have hρ := clusterThirdAbsoluteMoment_pos P Q p hp
  exact (div_le_one hρ).2 (by simpa only [one_mul] using (le_div_iff₀ hσ).mp h)

/-- A uniform explicit outside-support budget, ready for the manuscript's
ordered choice of noise radii and sample-size cutoff. -/
theorem manuscript_twoCluster_outside_uniform_error (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Ioo 0 1)
    (hcentral : p ∈ Icc (2 / 5) (3 / 5)) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hv : clusterVariance P Q p ≤ 1)
    (n : ℕ) (hn : 25 ≤ n) (k : ℤ) (hk : k < 0 ∨ (n : ℤ) < k)
    (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      Real.sqrt (n : ℝ) * Real.exp (-(2 / 25) * (n : ℝ)) +
      320 * cE * (3 * (accumulatedNoiseVariance P Q p n / (2 / 5)) ^ 2 +
        ε ^ 2 * (accumulatedNoiseVariance P Q p n / (2 / 5))) := by
  let r := Real.sqrt (n : ℝ)
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let T := 3 * (accumulatedNoiseVariance P Q p n / (2 / 5)) ^ 2 +
    ε ^ 2 * (accumulatedNoiseVariance P Q p n / (2 / 5))
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hA : 0 ≤ A := div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (clusterThirdAbsoluteMoment_pos P Q p hp).le
  have hA1 : A ≤ 1 := manuscript_cluster_prefactor_le_one P Q p hp
  have hb := actual_twoCluster_leakage_bound B P Q p (2 / 5) ε (by norm_num)
    hcentral.1 (by linarith [hcentral.2]) hε hP hQ n (by omega) k
  have hlam : 0 ≤ accumulatedNoiseVariance P Q p n := by
    exact mul_nonneg (Nat.cast_nonneg _) (averageNoiseVariance_nonneg P Q p ⟨hp.1.le, hp.2.le⟩)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hleak : r * A * blockLeakageBudget P Q p n k ≤ 320 * cE * T := by
    have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg hr.le hA)
    have he : r * A * (128 * cE / ((2 / 5) * r) * T) = A * (320 * cE * T) := by
      field_simp [hr.ne']
      <;> ring
    change r * A * blockLeakageBudget P Q p n k ≤ r * A * (128 * cE / ((2 / 5) * r) * T) at hm
    rw [he] at hm
    exact hm.trans (mul_le_of_le_one_left (mul_nonneg (mul_nonneg (by norm_num) cE_pos.le) hT) hA1)
  have hgauss := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hr.le hA1)
    (Real.exp_pos (-(2 / 25) * (n : ℝ))).le
  have hc := manuscript_twoCluster_outside_gaussian_comparison P Q p hp hcentral hv n hn k hk u hu
  change normalizedDiscrepancy _ _ _ ≤ r * A *
    (Real.exp (-(2 / 25) * (n : ℝ)) + blockLeakageBudget P Q p n k) at hc
  change normalizedDiscrepancy _ _ _ ≤ r * Real.exp (-(2 / 25) * (n : ℝ)) + 320 * cE * T
  nlinarith only [hc, hleak, hgauss]

/-- The final sample-size choice absorbs the original Gaussian exponential
tail uniformly; its cutoff is independent of p and both noise laws. -/
theorem manuscript_outside_gaussian_cutoff (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, 25 ≤ N ∧ ∀ n ≥ N,
      Real.sqrt (n : ℝ) * Real.exp (-(2 / 25) * (n : ℝ)) < δ := by
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * Real.exp (-(2 / 25) * (n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_apply] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (2 / 25) (by norm_num)).comp
        tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  exact ⟨max N 25, le_max_right _ _, fun n hn => hN n ((le_max_left _ _).trans hn)⟩

end BerryEsseen
