import BerryEsseen.MixtureBlocks
import BerryEsseen.BlockTailBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace BerryEsseen

def binomialWeight (p : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem binomialWeight_nonneg (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) :
    0 ≤ binomialWeight p n k := by
  unfold binomialWeight
  have hp0 := hp.1
  have hq : 0 ≤ 1 - p := by linarith [hp.2]
  positivity

def blockApproximation (P Q : CenteredFourthLaw) (p : ℝ) (n : ℕ) (k : ℤ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), binomialWeight p n j *
    (if (j : ℤ) = k then cdf (twoNoiseBlock P Q n j).measure u else if (j : ℤ) < k then 1 else 0)

def blockLeakageBudget (P Q : CenteredFourthLaw) (p : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℤ) ≠ k),
    binomialWeight p n j * (twoNoiseBlock P Q n j).fourthMoment / (|(j : ℝ) - k| - 1 / 2) ^ 4

theorem twoCluster_cdf_block_leakage (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (k : ℤ) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) - blockApproximation P Q p n k u| ≤
      blockLeakageBudget P Q p n k := by
  classical
  rw [iidSumLaw_twoCluster_cdf P Q p hp]
  change |(∑ j ∈ Finset.range (n + 1), binomialWeight p n j * _) - _| ≤ _
  unfold blockApproximation blockLeakageBudget
  rw [← Finset.sum_sub_distrib]
  apply (le_trans (Finset.abs_sum_le_sum_abs _ _))
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjk : (j : ℤ) = k
  · simp only [ne_eq, hjk, if_pos, not_true_eq_false, if_false]
    have hjr : (j : ℝ) = k := by exact_mod_cast hjk
    simp [hjr]
  · simp only [ne_eq, hjk, if_false, not_false_eq_true, if_true]
    rw [← mul_sub, abs_mul, abs_of_nonneg (binomialWeight_nonneg p hp n j), mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (binomialWeight_nonneg p hp n j)
    simpa only [Int.cast_natCast] using integer_block_cdf_error_bound (twoNoiseBlock P Q n j) (j : ℤ) k u hu hjk

theorem blockApproximation_central (P Q : CenteredFourthLaw) (p : ℝ) (n k : ℕ)
    (hk : k ≤ n) (u : ℝ) :
    blockApproximation P Q p n k u =
      (∑ j ∈ Finset.range k, binomialWeight p n j) +
        binomialWeight p n k * cdf (twoNoiseBlock P Q n k).measure u := by
  classical
  unfold blockApproximation
  have hsplit : ∀ j : ℕ,
      binomialWeight p n j * (if (j : ℤ) = (k : ℤ) then cdf (twoNoiseBlock P Q n j).measure u else if (j : ℤ) < (k : ℤ) then 1 else 0) =
      (if j < k then binomialWeight p n j else 0) +
        (if j = k then binomialWeight p n k * cdf (twoNoiseBlock P Q n k).measure u else 0) := by
    intro j
    by_cases hjk : j = k
    · subst j; simp
    · simp [hjk, mul_ite]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_range, show k < n + 1 by omega, if_true]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Strict CDF, retaining atom information needed for the negative branch. -/
def strictCDF (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Iio t)

theorem strictCDF_nonneg (μ : Measure ℝ) (t : ℝ) : 0 ≤ strictCDF μ t := ENNReal.toReal_nonneg

theorem strictCDF_le_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    strictCDF μ t ≤ cdf μ t := by
  rw [cdf_eq_real]
  exact measureReal_mono Iio_subset_Iic_self (by finiteness)

theorem strictCDF_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    strictCDF μ t ≤ 1 := (strictCDF_le_cdf μ t).trans (cdf_le_one μ t)

theorem strictCDF_shift (μ : Measure ℝ) [IsProbabilityMeasure μ] (a t : ℝ) :
    strictCDF (μ.map (fun x => a + x)) t = strictCDF μ (t - a) := by
  unfold strictCDF Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  congr 2
  ext x
  simp only [mem_preimage, mem_Iio]
  constructor <;> intro h <;> linarith

theorem iidSumLaw_twoCluster_strictCDF (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) t =
      ∑ k ∈ Finset.range (n + 1), binomialWeight p n k *
        strictCDF (twoNoiseBlock P Q n k).measure (t - k) := by
  letI : IsProbabilityMeasure (Q.measure.map (fun x => 1 + x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  unfold twoClusterMeasure strictCDF
  rw [iidSumLaw_mixture_blocks _ _ p hp n, Measure.real, Measure.finset_sum_apply]
  rw [ENNReal.toReal_sum (by
    intro k hk
    simp only [weightedConvolutionBlock, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (blockWeight_ne_top _ _ _) (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [weightedConvolutionBlock, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    blockWeight_toReal p hp]
  change binomialWeight p n k * strictCDF (iidSumLaw P.measure (n - k) ∗ iidSumLaw (Q.measure.map (fun x => 1 + x)) k) t = _
  rw [iidSumLaw_shift, mul_one, conv_upper_shift, strictCDF_shift]
  simp only [twoNoiseBlock, CenteredFourthLaw.conv, CenteredFourthLaw.iid_measure, strictCDF]

theorem CenteredFourthLaw.strictCDF_right_tail_bound (P : CenteredFourthLaw) (t d : ℝ)
    (hd : 0 < d) (ht : d ≤ t) : 1 - strictCDF P.measure t ≤ P.fourthMoment / d ^ 4 := by
  have he : 1 - strictCDF P.measure t = P.measure.real (Ici t) := by
    rw [strictCDF, ← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio]
  rw [he]
  apply le_trans ?_ (P.fourth_tail_bound d hd)
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  change d ≤ |x|
  exact ht.trans ((show t ≤ x from hx).trans (le_abs_self x))

theorem integer_block_strictCDF_error_bound (P : CenteredFourthLaw) (j k : ℤ) (u : ℝ)
    (hu : |u| ≤ 1 / 2) (hjk : j ≠ k) :
    |strictCDF P.measure ((k : ℝ) + u - j) - (if j < k then 1 else 0)| ≤
      P.fourthMoment / (|(j : ℝ) - k| - 1 / 2) ^ 4 := by
  have hu' := abs_le.1 hu
  rcases lt_or_gt_of_ne hjk with hjk | hjk
  · rw [if_pos hjk, abs_of_neg (by exact_mod_cast sub_neg.2 hjk : (j : ℝ) - k < 0)]
    have hdiff : (1 : ℝ) ≤ (k : ℝ) - j := by exact_mod_cast (show (1 : ℤ) ≤ k - j by omega)
    rw [abs_of_nonpos (by linarith [strictCDF_le_one P.measure ((k : ℝ) + u - j)])]
    have h := P.strictCDF_right_tail_bound ((k : ℝ) + u - j) ((k : ℝ) - j - 1 / 2) (by linarith) (by linarith)
    convert h using 1 <;> ring
  · rw [if_neg (not_lt_of_gt hjk), sub_zero, abs_of_nonneg (strictCDF_nonneg _ _),
      abs_of_pos (by exact_mod_cast sub_pos.2 hjk : 0 < (j : ℝ) - k)]
    have hdiff : (1 : ℝ) ≤ (j : ℝ) - k := by exact_mod_cast (show (1 : ℤ) ≤ j - k by omega)
    exact (strictCDF_le_cdf _ _).trans (P.cdf_left_tail_bound ((k : ℝ) + u - j) ((j : ℝ) - k - 1 / 2) (by linarith) (by linarith))

def strictBlockApproximation (P Q : CenteredFourthLaw) (p : ℝ) (n : ℕ) (k : ℤ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), binomialWeight p n j *
    (if (j : ℤ) = k then strictCDF (twoNoiseBlock P Q n j).measure u else if (j : ℤ) < k then 1 else 0)

theorem twoCluster_strictCDF_block_leakage (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (k : ℤ) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) - strictBlockApproximation P Q p n k u| ≤
      blockLeakageBudget P Q p n k := by
  classical
  rw [iidSumLaw_twoCluster_strictCDF P Q p hp]
  unfold strictBlockApproximation blockLeakageBudget
  rw [← Finset.sum_sub_distrib]
  apply (le_trans (Finset.abs_sum_le_sum_abs _ _))
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjk : (j : ℤ) = k
  · simp only [ne_eq, hjk, if_pos, not_true_eq_false, if_false]
    have hjr : (j : ℝ) = k := by exact_mod_cast hjk
    simp [hjr]
  · simp only [ne_eq, hjk, if_false, not_false_eq_true, if_true]
    rw [← mul_sub, abs_mul, abs_of_nonneg (binomialWeight_nonneg p hp n j), mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (binomialWeight_nonneg p hp n j)
    simpa only [Int.cast_natCast] using integer_block_strictCDF_error_bound (twoNoiseBlock P Q n j) (j : ℤ) k u hu hjk

theorem strictBlockApproximation_central (P Q : CenteredFourthLaw) (p : ℝ) (n k : ℕ)
    (hk : k ≤ n) (u : ℝ) :
    strictBlockApproximation P Q p n k u =
      (∑ j ∈ Finset.range k, binomialWeight p n j) +
        binomialWeight p n k * strictCDF (twoNoiseBlock P Q n k).measure u := by
  classical
  unfold strictBlockApproximation
  have hsplit : ∀ j : ℕ,
      binomialWeight p n j * (if (j : ℤ) = (k : ℤ) then strictCDF (twoNoiseBlock P Q n j).measure u else if (j : ℤ) < (k : ℤ) then 1 else 0) =
      (if j < k then binomialWeight p n j else 0) +
        (if j = k then binomialWeight p n k * strictCDF (twoNoiseBlock P Q n k).measure u else 0) := by
    intro j
    by_cases hjk : j = k
    · subst j; simp
    · simp [hjk, mul_ite]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_range, show k < n + 1 by omega, if_true]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega


end BerryEsseen
