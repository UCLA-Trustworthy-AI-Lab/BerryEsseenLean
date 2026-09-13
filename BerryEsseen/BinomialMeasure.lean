import BerryEsseen.ClusterCentralComparison
import BerryEsseen.GaussianBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace BerryEsseen

def bernoulliMeasure (p : ℝ) : Measure ℝ := mixtureMeasure (Measure.dirac 0) (Measure.dirac 1) p

def binomialMeasure (p : ℝ) (n : ℕ) : Measure ℝ := iidSumLaw (bernoulliMeasure p) n

theorem bernoulliMeasure_probability (p : ℝ) (hp : p ∈ Icc 0 1) :
    IsProbabilityMeasure (bernoulliMeasure p) := mixtureMeasure_probability _ _ p hp

theorem binomialMeasure_probability (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    IsProbabilityMeasure (binomialMeasure p n) := by
  letI := bernoulliMeasure_probability p hp
  exact iidSumLaw_isProbabilityMeasure _ _

theorem iidSumLaw_dirac (a : ℝ) (n : ℕ) : iidSumLaw (Measure.dirac a) n = Measure.dirac ((n : ℝ) * a) := by
  induction n with
  | zero => simp [iidSumLaw]
  | succ n ih =>
    change Measure.dirac a ∗ iidSumLaw (Measure.dirac a) n = _
    rw [ih, Measure.dirac_conv_dirac]
    congr 1
    push_cast
    ring

theorem binomialMeasure_blocks (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    binomialMeasure p n = ∑ j ∈ Finset.range (n + 1), blockWeight p n j • Measure.dirac (j : ℝ) := by
  rw [binomialMeasure, bernoulliMeasure, iidSumLaw_mixture_blocks _ _ p hp]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [weightedConvolutionBlock, iidSumLaw_dirac, mul_zero, mul_one, Measure.dirac_conv_dirac, zero_add]

theorem binomialWeight_sum (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), binomialWeight p n j) = 1 := by
  letI := binomialMeasure_probability p hp n
  have h := congrArg (fun μ : Measure ℝ => μ univ) (binomialMeasure_blocks p hp n)
  change (binomialMeasure p n) univ = (∑ j ∈ Finset.range (n + 1), blockWeight p n j • Measure.dirac (j : ℝ)) univ at h
  rw [measure_univ, Measure.finset_sum_apply] at h
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one] at h
  have hh := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_one, ENNReal.toReal_sum (fun j hj => blockWeight_ne_top p n j)] at hh
  simpa only [blockWeight_toReal p hp, binomialWeight] using hh.symm

theorem binomialMeasure_cdf (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    cdf (binomialMeasure p n) t =
      ∑ j ∈ Finset.range (n + 1), if (j : ℝ) ≤ t then binomialWeight p n j else 0 := by
  letI := binomialMeasure_probability p hp n
  rw [cdf_eq_real, Measure.real, binomialMeasure_blocks p hp, Measure.finset_sum_apply]
  rw [ENNReal.toReal_sum (by
    intro j hj
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (blockWeight_ne_top p n j) (by finiteness))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, blockWeight_toReal p hp]
  by_cases h : (j : ℝ) ≤ t
  · rw [Measure.dirac_apply_of_mem (show (j : ℝ) ∈ Iic t from h)]
    simp [h, binomialWeight]
  · rw [Measure.dirac_apply' _ measurableSet_Iic]
    simp only [Set.indicator_of_notMem (show (j : ℝ) ∉ Iic t from h)]
    simp [h]

theorem binomialMeasure_cdf_integer (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) (hk : k ≤ n) :
    cdf (binomialMeasure p n) k = ∑ j ∈ Finset.range (k + 1), binomialWeight p n j := by
  rw [binomialMeasure_cdf p hp]
  have he : ∀ j : ℕ, (if (j : ℝ) ≤ (k : ℝ) then binomialWeight p n j else 0) =
      if j < k + 1 then binomialWeight p n j else 0 := by
    intro j
    have hh : ((j : ℝ) ≤ (k : ℝ)) ↔ j < k + 1 := by norm_cast; omega
    simp only [hh]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem twoCluster_zero_noise (p : ℝ) :
    twoClusterMeasure CenteredFourthLaw.zero CenteredFourthLaw.zero p = bernoulliMeasure p := by
  unfold twoClusterMeasure bernoulliMeasure CenteredFourthLaw.zero
  rw [Measure.map_dirac (by fun_prop : Measurable (fun x : ℝ => 1 + x))]
  simp only [add_zero]

end BerryEsseen
