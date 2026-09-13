import BerryEsseen.ManuscriptEffectiveSmallVarianceNormalization
import BerryEsseen.ManuscriptEffectiveSmallVarianceMoments
import BerryEsseen.ManuscriptEffectiveCentralDerivative
import BerryEsseen.ManuscriptGaussianClusterComparison

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_effective_central_normalized_comparison (B : PublishedBernoulliBound) (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ 1 / (10 : ℝ) ^ 12)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hb : 0 < binomialWeight p n k)
    (hsmall : (twoNoiseBlock P Q n k).fourthMoment ≤ 1 / 160000)
    (hd : ∀ u : ℝ, |u| ≤ 3 / 5 →
      3 / 4 ≤ deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ∧
      deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ≤ 5 / 4)
    (u : ℝ) (hu : |u| ≤ 1 / 2) :
    let r := Real.sqrt (n : ℝ)
    let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
    let A0 := Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      binomialNormalizedConstant p n +
      100 * r * averageNoiseVariance P Q p -
      3 / 8 * r * A * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
      176000 * r * A * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment +
      r * A * blockLeakageBudget P Q p n k := by
  dsimp only
  let r := Real.sqrt (n : ℝ)
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let A0 := Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))
  let Rb := binomialNormalizedConstant p n
  let E := 100 * r * averageNoiseVariance P Q p
  let F := cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let Fl := strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let G := normalCDF (((k : ℝ) - n * p + u) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  let G0 := normalCDF (((k : ℝ) - n * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  let b := binomialWeight p n k
  let F0 := ∑ j ∈ Finset.range k, binomialWeight p n j
  let W := twoNoiseBlock P Q n k
  let J := blockLeakageBudget P Q p n k
  have hp01 := (effective_binomial_parameters p hp).1
  have hpI : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpI
  have hAf : 0 ≤ r * A := by
    have := (clusterThirdAbsoluteMoment_pos P Q p hp01).le
    dsimp only [r, A]
    positivity
  have hcomp := manuscript_twoCluster_gaussian_central_comparison P Q p hpI n k hk hb hsmall hd u hu
  dsimp only at hcomp
  simp only [add_zero] at hcomp
  change (F - G ≤ F0 + b - G0 - 3 / 8 * b * W.absoluteMoment + 176000 * b * W.fourthMoment + J) ∧
    (G - Fl ≤ G0 - F0 - 3 / 8 * b * W.absoluteMoment + 176000 * b * W.fourthMoment + J) at hcomp
  have hR := manuscript_effective_perturbed_binomial_branch_bound B P Q p ε hp hε hP hQ hs n hn k
    (cdf (binomialMeasure p n) k) (binomialDiscrepancy_le_Kolmogorov p hpI n k)
  rw [binomialMeasure_cdf_integer p hpI n k hk, Finset.sum_range_succ] at hR
  change |r * A * (F0 + b - G0)| ≤ Rb + E at hR
  have hL := manuscript_effective_perturbed_binomial_branch_bound B P Q p ε hp hε hP hQ hs n hn k F0
    (binomial_left_branch_le_Kolmogorov p hpI n k hk)
  change |r * A * (F0 - G0)| ≤ Rb + E at hL
  have hR' := (abs_le.1 hR).2
  have hL' := (abs_le.1 hL).1
  have hright := mul_le_mul_of_nonneg_left hcomp.1 hAf
  have hleft := mul_le_mul_of_nonneg_left hcomp.2 hAf
  have hFl : Fl ≤ F := strictCDF_le_cdf _ _
  have hFl' := mul_le_mul_of_nonneg_left hFl hAf
  have habs : |r * A * (F - G)| ≤ Rb + E - 3 / 8 * r * A * b * W.absoluteMoment +
      176000 * r * A * b * W.fourthMoment + r * A * J := by
    rw [abs_le]
    constructor <;> nlinarith only [hright, hleft, hR', hL', hFl']
  rw [abs_mul (r * A) _, abs_of_nonneg hAf] at habs
  rw [standardizedTwoCluster_discrepancy P Q p hp01 n hn]
  have ht : (k : ℝ) + u - n * p = (k : ℝ) - n * p + u := by ring
  rw [ht]
  simpa only [mul_div_assoc] using habs

theorem manuscript_effective_small_variance_central_remainder (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12))
    (hz : |binomialZ p n k| ≤ 5) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      binomialNormalizedConstant p n -
        1 / (10 : ℝ) ^ 8 * accumulatedNoiseVariance P Q p n /
          Real.sqrt (5 * accumulatedNoiseVariance P Q p n + ε ^ 2) +
      20000000 * accumulatedNoiseVariance P Q p n * (accumulatedNoiseVariance P Q p n + ε ^ 2) +
      100 * accumulatedNoiseVariance P Q p n / Real.sqrt (n : ℝ) := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hn1 : 1 ≤ n := by omega
  let r := Real.sqrt (n : ℝ)
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let b := binomialWeight p n k
  let lam := accumulatedNoiseVariance P Q p n
  let q := Real.sqrt (5 * lam + ε ^ 2)
  let W := twoNoiseBlock P Q n k
  let D4 := manuscriptEffectiveFourthBudget lam ε
  have hs0 := averageNoiseVariance_nonneg P Q p hpcc
  have hsle := (averageNoiseVariance_le_accumulated P Q p hpcc n hn1).trans hlam.2
  have hd := manuscript_effective_central_gaussian_derivative p (averageNoiseVariance P Q p)
    hp ⟨hs0, hsle⟩ n k hn (by simpa only [accumulatedNoiseVariance] using hlam.2) hk hz
  have hsmall := manuscript_effective_noise_fourth_small P Q p ε hp hε hP hQ n k hk hlam.2
  have hc := manuscript_effective_central_normalized_comparison B P Q p ε hp hε hP hQ hsle
    n k hn1 hk hd.1 hsmall hd.2 u hu
  dsimp only at hc
  have hA : A ∈ Icc (1 / 2) 2 := by
    have h := manuscript_effective_cluster_prefactor_bounds P Q p ε hp hε hP hQ hsle
    exact ⟨h.1.le, h.2.le⟩
  have hA0 : 0 < A := by linarith [hA.1]
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hq : 0 < q := Real.sqrt_pos.mpr (by have h : 0 < lam := hlam.1; positivity)
  have hb0 : 0 < b := hd.1
  have hbLower := (manuscript_effective_binomial_central p hp n hn k hk hz).2.2
  have hbUpper := manuscript_effective_binomial_mass_upper p hp n k hn1
  have hrbLower : 1 / (10 : ℝ) ^ 6 ≤ r * b := by
    have hh := (div_le_iff₀ hr).mp hbLower
    nlinarith only [hh]
  have hrbUpper : r * b ≤ 2 := by
    have hh := (le_div_iff₀ hr).mp hbUpper
    nlinarith only [hh]
  have hArbLower := mul_le_mul hA.1 hrbLower
    (by positivity : (0 : ℝ) ≤ 1 / 10 ^ 6) hA0.le
  have hArbUpper := mul_le_mul hA.2 hrbUpper (mul_pos hr hb0).le (by norm_num : (0 : ℝ) ≤ 2)
  have habs := manuscript_effective_noise_absolute_central P Q p ε hp hε.1 hP hQ n k hn hk hz hlam.1
  change lam / (2 * q) ≤ W.absoluteMoment at habs
  have hLoss : 1 / (10 : ℝ) ^ 8 * lam / q ≤ 3 / 8 * r * A * b * W.absoluteMoment := by
    have hcoef : 1 / (10 : ℝ) ^ 8 ≤ 3 / 16 * A * (r * b) := by nlinarith only [hArbLower]
    have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 3 / 8 * r * A * b)
    have h2 := mul_le_mul_of_nonneg_right hcoef (div_nonneg hlam.1.le hq.le)
    change 1 / (10 : ℝ) ^ 8 * (lam / q) ≤ 3 / 16 * A * (r * b) * (lam / q) at h2
    have hid : 3 / 8 * r * A * b * (lam / (2 * q)) = 3 / 16 * A * (r * b) * (lam / q) := by ring
    rw [hid] at h1
    convert h2.trans h1 using 1 <;> ring
  have hf := manuscript_effective_noise_fourth P Q p ε hp hε.1 hP hQ n k hk
  change W.fourthMoment ≤ D4 at hf
  have hD4 : 0 ≤ D4 := by dsimp [D4, manuscriptEffectiveFourthBudget]; have h : 0 < lam := hlam.1; positivity
  have hLeak := manuscript_effective_leakage_bound P Q p ε hp hε.1 hP hQ n hn1 k
  change blockLeakageBudget P Q p n k ≤ 80 * D4 / r at hLeak
  have hError : 176000 * r * A * b * W.fourthMoment + r * A * blockLeakageBudget P Q p n k ≤
      20000000 * lam * (lam + ε ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 176000 * r * A * b)
    have h2 := mul_le_mul_of_nonneg_right hArbUpper hD4
    have h3 := mul_le_mul_of_nonneg_left hLeak (mul_pos hr hA0).le
    have h4 := mul_le_mul_of_nonneg_right hA.2 hD4
    have he : r * A * (80 * D4 / r) = 80 * A * D4 := by field_simp
    rw [he] at h3
    have heD : D4 = 20 * lam * (lam + ε ^ 2) := rfl
    have hm : 0 ≤ lam * (lam + ε ^ 2) := by have h : 0 < lam := hlam.1; positivity
    nlinarith only [h1, h2, h3, h4, heD, hm]
  have hNorm : 100 * r * averageNoiseVariance P Q p = 100 * lam / r := by
    apply (eq_div_iff hr.ne').mpr
    change 100 * Real.sqrt (n : ℝ) * averageNoiseVariance P Q p * Real.sqrt (n : ℝ) =
      100 * ((n : ℝ) * averageNoiseVariance P Q p)
    calc
      _ = 100 * averageNoiseVariance P Q p * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]; ring
  change _ ≤ binomialNormalizedConstant p n + 100 * r * averageNoiseVariance P Q p -
    3 / 8 * r * A * b * W.absoluteMoment + 176000 * r * A * b * W.fourthMoment +
      r * A * blockLeakageBudget P Q p n k at hc
  rw [hNorm] at hc
  change _ ≤ binomialNormalizedConstant p n - 1 / (10 : ℝ) ^ 8 * lam / q +
    20000000 * lam * (lam + ε ^ 2) + 100 * lam / r
  linarith only [hc, hLoss, hError]

end BerryEsseen
