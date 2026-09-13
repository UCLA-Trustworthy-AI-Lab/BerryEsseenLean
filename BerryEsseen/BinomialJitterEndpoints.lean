import BerryEsseen.BernoulliLimits
import BerryEsseen.BinomialJitter
import BerryEsseen.StandardizedJitter

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def binomialZ (p : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  ((k : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))

theorem binomialZ_scaling (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    Real.sqrt (n : ℝ) * binomialZ p n k = ((k : ℝ) - n * p) / Real.sqrt (p * (1 - p)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv := mul_pos hp.1 (sub_pos.2 hp.2)
  rw [binomialZ, mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le]
  field_simp [(Real.sqrt_pos.2 hn0).ne', (Real.sqrt_pos.2 hv).ne']

theorem binomial_jitter_endpoint_right (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (h : ℝ) (hh : 0 < h) :
    cdf (iidSumLaw (standardizedBernoulliLaw p hp).measure n ∗ uniformJitter h)
      (Real.sqrt (n : ℝ) * binomialZ p n k + h / 2) =
      cdf (binomialMeasure p n ∗ uniformJitter (Real.sqrt (p * (1 - p)) * h))
        ((k : ℝ) + (Real.sqrt (p * (1 - p)) * h) / 2) := by
  letI := bernoulliMeasure_probability p ⟨hp.1.le, hp.2.le⟩
  rw [binomialZ_scaling p hp n hn k, standardizedBernoulliLaw, standardizedTwoClusterLaw_measure,
    zero_clusterVariance, twoCluster_zero_noise]
  exact standardized_jitter_cdf _ _ _ _ (Real.sqrt_pos.2 (mul_pos hp.1 (sub_pos.2 hp.2))) hh n k

theorem binomial_jitter_endpoint_left (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (h : ℝ) (hh : 0 < h) :
    cdf (iidSumLaw (standardizedBernoulliLaw p hp).measure n ∗ uniformJitter h)
      (Real.sqrt (n : ℝ) * binomialZ p n k - h / 2) =
      cdf (binomialMeasure p n ∗ uniformJitter (Real.sqrt (p * (1 - p)) * h))
        ((k : ℝ) - (Real.sqrt (p * (1 - p)) * h) / 2) := by
  letI := bernoulliMeasure_probability p ⟨hp.1.le, hp.2.le⟩
  rw [binomialZ_scaling p hp n hn k, standardizedBernoulliLaw, standardizedTwoClusterLaw_measure,
    zero_clusterVariance, twoCluster_zero_noise]
  exact standardized_jitter_cdf_left _ _ _ _ (Real.sqrt_pos.2 (mul_pos hp.1 (sub_pos.2 hp.2))) hh n k

theorem binomial_jitter_width_tendsto (p : ℕ → ℝ) (hlim : Tendsto p atTop (𝓝 pE)) :
    Tendsto (fun j => Real.sqrt (p j * (1 - p j)) * hE) atTop (𝓝 (1 : ℝ)) := by
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  have h := ((hlim.mul hq).sqrt).mul_const hE
  have he : Real.sqrt (pE * (1 - pE)) * hE = 1 := by
    change sigmaE * (1 / sigmaE) = 1
    field_simp [sigmaE_pos.ne']
  rwa [he] at h

end BerryEsseen
