import BerryEsseen.CentralClusterBudget
import BerryEsseen.ManuscriptGaussianClusterComparison

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-! All central positive error terms retain their accumulated-variance factor. -/

def manuscriptClusterCentralLossCoefficient (P Q : CenteredFourthLaw) (p : ℝ) (n k : ℕ) : ℝ :=
  3 / 16 * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
    (Real.sqrt (n : ℝ) * binomialWeight p n k)

def manuscriptClusterCentralErrorCoefficient (P Q : CenteredFourthLaw) (p δ ε : ℝ) (n k : ℕ) : ℝ :=
  (56 * cE + 48 * phi0) / (p * (1 - p) * Real.sqrt (n : ℝ)) +
  (176000 * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
      (Real.sqrt (n : ℝ) * binomialWeight p n k) +
    128 * cE * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) / δ) *
  (3 * accumulatedNoiseVariance P Q p n / δ ^ 2 + ε ^ 2 / δ)

theorem manuscript_twoCluster_central_error_budget (S : PublishedBernoulliBound) (P Q : CenteredFourthLaw)
    (p δ ε M : ℝ) (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hb : 0 < binomialWeight p n k)
    (hsmall : (twoNoiseBlock P Q n k).fourthMoment ≤ 1 / 160000)
    (hd : ∀ u : ℝ, |u| ≤ 3 / 5 →
      3 / 4 ≤ deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ∧
      deriv (clusterGaussianIncrement p n k (averageNoiseVariance P Q p)) u ≤ 5 / 4)
    (hcentral : |(k : ℝ) - n * p| ≤ M * Real.sqrt (n : ℝ))
    (hlarge : 2 * M ≤ δ * Real.sqrt (n : ℝ))
    (hlam : 0 < accumulatedNoiseVariance P Q p n) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p ⟨by linarith, by linarith⟩) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) * binomialKolmogorov p n -
      manuscriptClusterCentralLossCoefficient P Q p n k * accumulatedNoiseVariance P Q p n /
        Real.sqrt (3 * accumulatedNoiseVariance P Q p n / δ + ε ^ 2) +
      accumulatedNoiseVariance P Q p n * manuscriptClusterCentralErrorCoefficient P Q p δ ε n k := by
  have hpI : p ∈ Ioo 0 1 := ⟨by linarith, by linarith⟩
  let r := Real.sqrt (n : ℝ)
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let b := binomialWeight p n k
  let lam := accumulatedNoiseVariance P Q p n
  let v := p * (1 - p)
  let D := 3 * lam / δ ^ 2 + ε ^ 2 / δ
  let q := Real.sqrt (3 * lam / δ + ε ^ 2)
  let W := twoNoiseBlock P Q n k
  let J := blockLeakageBudget P Q p n k
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := Real.sqrt_pos.2 hn0
  have hv : 0 < v := mul_pos hpI.1 (sub_pos.2 hpI.2)
  have hA : 0 < A := div_pos (pow_pos (Real.sqrt_pos.2 (clusterVariance_pos P Q p hpI)) 3)
    (clusterThirdAbsoluteMoment_pos P Q p hpI)
  have hb0 : 0 < b := hb
  have hq0 : 0 < q := Real.sqrt_pos.2 (by dsimp only [lam]; positivity)
  have heD : 3 * (lam / δ) ^ 2 + ε ^ 2 * (lam / δ) = lam * D := by dsimp only [D]; ring
  have hfour := noise_fourth_uniform_bound P Q p δ ε hδ hp hq hε hP hQ n k hk
  change W.fourthMoment ≤ 3 * (lam / δ) ^ 2 + ε ^ 2 * (lam / δ) at hfour
  rw [heD] at hfour
  have hleak := actual_twoCluster_leakage_bound S P Q p δ ε hδ hp hq hε hP hQ n hn k
  change J ≤ (128 * cE / (δ * r)) * (3 * (lam / δ) ^ 2 + ε ^ 2 * (lam / δ)) at hleak
  rw [heD] at hleak
  have habs := noise_absoluteMoment_central_lower P Q p δ ε M hδ hp hq hε hM hP hQ n k hn hk hcentral hlarge hlam
  change lam / (2 * q) ≤ W.absoluteMoment at habs
  have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ 3 / 8 * r * A * b)
  have h2 := mul_le_mul_of_nonneg_left hfour (by positivity : 0 ≤ 176000 * r * A * b)
  have h3 := mul_le_mul_of_nonneg_left hleak (by positivity : 0 ≤ r * A)
  have hcomp := manuscript_twoCluster_central_normalized_comparison S P Q p ε hpI hεp hεq hP hQ hs n k hn hk hb hsmall hd u hu
  dsimp only at hcomp
  apply hcomp.trans
  change _ ≤ _
  have hnorm : (56 * cE + 48 * phi0) / v * r * averageNoiseVariance P Q p =
      lam * ((56 * cE + 48 * phi0) / (v * r)) := by
    dsimp only [lam, accumulatedNoiseVariance, averageNoiseVariance, r]
    field_simp [hv.ne', hr.ne']
    rw [Real.sq_sqrt hn0.le]
    ring
  have hleakid : r * A * (128 * cE / (δ * r) * (lam * D)) = lam * (128 * cE * A / δ) * D := by
    field_simp [hr.ne', hδ.ne'] <;> ring
  rw [hleakid] at h3
  change _ + (56 * cE + 48 * phi0) / v * r * averageNoiseVariance P Q p -
      3 / 8 * r * A * b * W.absoluteMoment + 176000 * r * A * b * W.fourthMoment + r * A * J ≤ _
  rw [hnorm]
  change _ ≤ _ - (3 / 16 * A * (r * b)) * lam / q +
    lam * ((56 * cE + 48 * phi0) / (v * r) + (176000 * A * (r * b) + 128 * cE * A / δ) * D)
  have hlossid : 3 / 8 * r * A * b * (lam / (2 * q)) = (3 / 16 * A * (r * b)) * lam / q := by ring
  rw [hlossid] at h1
  nlinarith only [h1, h2, h3]


end BerryEsseen
