import BerryEsseen.NormalizationPerturbation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def averageNoiseVariance (P Q : CenteredFourthLaw) (p : ℝ) : ℝ :=
  (1 - p) * P.secondMoment + p * Q.secondMoment

theorem averageNoiseVariance_nonneg (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    0 ≤ averageNoiseVariance P Q p := add_nonneg
      (mul_nonneg (sub_nonneg.2 hp.2) P.secondMoment_nonneg) (mul_nonneg hp.1 Q.secondMoment_nonneg)

theorem bernoulli_variance_tau_bounds (p : ℝ) (hp : p ∈ Ioo 0 1) :
    p * (1 - p) ∈ Ioc (0 : ℝ) 1 ∧ p ^ 2 + (1 - p) ^ 2 ∈ Icc (1 / 2 : ℝ) 1 := by
  have hv : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.2 hp.2)
  constructor
  · exact ⟨hv, by nlinarith [sq_nonneg (p - 1 / 2)]⟩
  · constructor <;> nlinarith [sq_nonneg (p - 1 / 2)]

theorem actual_cluster_normalization_error (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Ioo 0 1)
    (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n : ℕ) (hn : 1 ≤ n) (t F : ℝ)
    (hBE : |F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| ≤
      cE * (p ^ 2 + (1 - p) ^ 2) / Real.sqrt ((n : ℝ) * p * (1 - p))) :
    |Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
        (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))) -
      Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) *
        (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))))| ≤
      (56 * cE + 48 * phi0) / (p * (1 - p)) * Real.sqrt (n : ℝ) * averageNoiseVariance P Q p := by
  have hs0 := averageNoiseVariance_nonneg P Q p ⟨hp.1.le, hp.2.le⟩
  have hb := bernoulli_variance_tau_bounds p hp
  have hρ : |clusterThirdAbsoluteMoment P Q p - p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)| ≤
      4 * averageNoiseVariance P Q p := by
    have h := twoCluster_abs_third_error P Q p ε ⟨hp.1.le, hp.2.le⟩ hεp hεq hP hQ
    change |clusterThirdAbsoluteMoment P Q p - _| ≤ (3 + ε) * averageNoiseVariance P Q p at h
    have hε : ε ≤ 1 := hεp.trans hp.2.le
    nlinarith [mul_le_mul_of_nonneg_right hε hs0]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have harg (v : ℝ) : ((t - (n : ℝ) * p) / Real.sqrt (n : ℝ)) / Real.sqrt v =
      (t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * v) := by
    rw [div_div, Real.sqrt_mul hn0.le]
  have he : clusterVariance P Q p = p * (1 - p) + averageNoiseVariance P Q p := by
    unfold clusterVariance averageNoiseVariance
    ring
  have h := normalized_branch_difference_bound (p * (1 - p)) (averageNoiseVariance P Q p)
    (p ^ 2 + (1 - p) ^ 2) (clusterThirdAbsoluteMoment P Q p) hb.1 hb.2 ⟨hs0, hs⟩ hρ n hn
    ((t - (n : ℝ) * p) / Real.sqrt (n : ℝ)) F (by
      rw [harg, ← mul_assoc]
      exact hBE)
  rw [harg, harg, ← he] at h
  simpa only [mul_assoc] using h

end BerryEsseen
