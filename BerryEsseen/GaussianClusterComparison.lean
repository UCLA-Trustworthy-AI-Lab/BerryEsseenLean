import BerryEsseen.CentralGaussianDerivative
import BerryEsseen.ClusterCentralComparison
import BerryEsseen.ClusterNormalization

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem clusterGaussianIncrement_differentiable (p : ℝ) (n k : ℕ) (s : ℝ) :
    Differentiable ℝ (clusterGaussianIncrement p n k s) :=
  fun u => (gaussian_increment_hasDerivAt _ _ _ u).differentiableAt

theorem twoCluster_gaussian_central_comparison (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n k : ℕ) (hk : k ≤ n) (hb : 0 < binomialWeight p n k)
    (hd : ∀ u : ℝ, |u| ≤ 3 / 5 →
      3 / 4 ≤ deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ∧
      deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ≤ 5 / 4)
    (u : ℝ) (hu : |u| ≤ 1 / 2) :
    let G := fun w : ℝ => normalCDF (((k : ℝ) - n * p + w) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
    (cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) - G u ≤
      (∑ j ∈ Finset.range k, binomialWeight p n j) + binomialWeight p n k - G 0 -
        3 / 8 * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
        11000 * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment + blockLeakageBudget P Q p n k) ∧
    (G u - strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ≤
      G 0 - (∑ j ∈ Finset.range k, binomialWeight p n j) -
        3 / 8 * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
        11000 * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment + blockLeakageBudget P Q p n k) := by
  dsimp only
  let G := fun w : ℝ => normalCDF (((k : ℝ) - n * p + w) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  have he : (fun w => (G w - G 0) / binomialWeight p n k) =
      clusterGaussianIncrement p n k (averageNoiseVariance P Q p) := by
    funext w
    simp only [G, clusterGaussianIncrement, add_zero, clusterVariance, averageNoiseVariance, add_assoc]
  have hf := clusterGaussianIncrement_differentiable p n k (averageNoiseVariance P Q p)
  exact twoCluster_central_comparison P Q p hp n k hk hb G
    (by rw [he]; exact hf.continuous.continuousOn)
    (by rw [he]; exact hf.differentiableOn)
    (by rw [he]; intro w hw; exact hd w (abs_le.2 ⟨hw.1.le, hw.2.le⟩)) u hu

theorem perturbed_binomial_branch_bound (S : PublishedBernoulliBound) (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Ioo 0 1) (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n : ℕ) (hn : 1 ≤ n) (t F : ℝ)
    (hF : |F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| ≤ binomialKolmogorov p n) :
    |Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
      (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)))| ≤
      Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) * binomialKolmogorov p n +
      (56 * cE + 48 * phi0) / (p * (1 - p)) * Real.sqrt (n : ℝ) * averageNoiseVariance P Q p := by
  have h := actual_cluster_normalization_error P Q p ε hp hεp hεq hP hQ hs n hn t F
    (hF.trans (S.strict_bound p hp n hn).le)
  have hA : 0 ≤ Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) := by
    have hp0 := hp.1.le
    have hq0 := (sub_pos.2 hp.2).le
    positivity
  have hB := mul_le_mul_of_nonneg_left hF hA
  have htriangle := abs_add_le
    (Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
      (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))) -
    Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) *
      (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))))
    (Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) *
      (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))))
  rw [sub_add_cancel, abs_mul (Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)))) _, abs_of_nonneg hA] at htriangle
  linarith


theorem twoCluster_central_normalized_comparison (S : PublishedBernoulliBound) (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Ioo 0 1) (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hb : 0 < binomialWeight p n k)
    (hd : ∀ u : ℝ, |u| ≤ 3 / 5 →
      3 / 4 ≤ deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ∧
      deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ≤ 5 / 4)
    (u : ℝ) (hu : |u| ≤ 1 / 2) :
    let r := Real.sqrt (n : ℝ)
    let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
    let A0 := Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      r * A0 * binomialKolmogorov p n +
      (56 * cE + 48 * phi0) / (p * (1 - p)) * r * averageNoiseVariance P Q p -
      3 / 8 * r * A * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
      11000 * r * A * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment +
      r * A * blockLeakageBudget P Q p n k := by
  dsimp only
  let r := Real.sqrt (n : ℝ)
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let A0 := Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))
  let Rb := r * A0 * binomialKolmogorov p n
  let E := (56 * cE + 48 * phi0) / (p * (1 - p)) * r * averageNoiseVariance P Q p
  let F := cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let Fl := strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let G := normalCDF (((k : ℝ) - n * p + u) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  let G0 := normalCDF (((k : ℝ) - n * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  let b := binomialWeight p n k
  let F0 := ∑ j ∈ Finset.range k, binomialWeight p n j
  let W := twoNoiseBlock P Q n k
  let J := blockLeakageBudget P Q p n k
  have hpI : p ∈ Icc 0 1 := ⟨hp.1.le, hp.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpI
  have hAf : 0 ≤ r * A := by
    have := (clusterThirdAbsoluteMoment_pos P Q p hp).le
    dsimp only [r, A]
    positivity
  have hcomp := twoCluster_gaussian_central_comparison P Q p hpI n k hk hb hd u hu
  dsimp only at hcomp
  simp only [add_zero] at hcomp
  change (F - G ≤ F0 + b - G0 - 3 / 8 * b * W.absoluteMoment + 11000 * b * W.fourthMoment + J) ∧
    (G - Fl ≤ G0 - F0 - 3 / 8 * b * W.absoluteMoment + 11000 * b * W.fourthMoment + J) at hcomp
  have hR := perturbed_binomial_branch_bound S P Q p ε hp hεp hεq hP hQ hs n hn k
    (cdf (binomialMeasure p n) k) (binomialDiscrepancy_le_Kolmogorov p hpI n k)
  rw [binomialMeasure_cdf_integer p hpI n k hk, Finset.sum_range_succ] at hR
  change |r * A * (F0 + b - G0)| ≤ Rb + E at hR
  have hL := perturbed_binomial_branch_bound S P Q p ε hp hεp hεq hP hQ hs n hn k F0
    (binomial_left_branch_le_Kolmogorov p hpI n k hk)
  change |r * A * (F0 - G0)| ≤ Rb + E at hL
  have hR' := (abs_le.1 hR).2
  have hL' := (abs_le.1 hL).1
  have hright := mul_le_mul_of_nonneg_left hcomp.1 hAf
  have hleft := mul_le_mul_of_nonneg_left hcomp.2 hAf
  have hFl : Fl ≤ F := strictCDF_le_cdf _ _
  have hFl' := mul_le_mul_of_nonneg_left hFl hAf
  have habs : |r * A * (F - G)| ≤ Rb + E - 3 / 8 * r * A * b * W.absoluteMoment +
      11000 * r * A * b * W.fourthMoment + r * A * J := by
    rw [abs_le]
    constructor <;> nlinarith only [hright, hleft, hR', hL', hFl']
  rw [abs_mul (r * A) _, abs_of_nonneg hAf] at habs
  rw [standardizedTwoCluster_discrepancy P Q p hp n hn]
  have ht : (k : ℝ) + u - n * p = (k : ℝ) - n * p + u := by ring
  rw [ht]
  simpa only [mul_div_assoc] using habs

end BerryEsseen
