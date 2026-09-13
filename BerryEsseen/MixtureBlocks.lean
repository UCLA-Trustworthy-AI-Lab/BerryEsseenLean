import BerryEsseen.CenteredFourthMoments

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BerryEsseen

def mixtureMeasure (μ ν : Measure ℝ) (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • μ + ENNReal.ofReal p • ν

theorem mixtureMeasure_probability (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ∈ Icc 0 1) : IsProbabilityMeasure (mixtureMeasure μ ν p) := by
  constructor
  simp only [mixtureMeasure, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith [hp.2]) hp.1]
  norm_num

theorem iidSumLaw_add (μ : Measure ℝ) [IsProbabilityMeasure μ] (n m : ℕ) :
    iidSumLaw μ (n + m) = iidSumLaw μ n ∗ iidSumLaw μ m := by
  induction n with
  | zero => simp only [zero_add, iidSumLaw, Measure.dirac_zero_conv]
  | succ n ih =>
    rw [Nat.succ_add]
    change μ ∗ iidSumLaw μ (n + m) = (μ ∗ iidSumLaw μ n) ∗ iidSumLaw μ m
    rw [ih, Measure.conv_assoc]

def blockWeight (p : ℝ) (n k : ℕ) : ℝ≥0∞ :=
  (n.choose k : ℝ≥0∞) * ENNReal.ofReal p ^ k * ENNReal.ofReal (1 - p) ^ (n - k)

def weightedConvolutionBlock (μ ν : Measure ℝ) (p : ℝ) (n k : ℕ) : Measure ℝ :=
  blockWeight p n k • (iidSumLaw μ (n - k) ∗ iidSumLaw ν k)

theorem weightedConvolutionBlock_outside (μ ν : Measure ℝ) (p : ℝ) (n k : ℕ) (hk : n < k) :
    weightedConvolutionBlock μ ν p n k = 0 := by
  simp [weightedConvolutionBlock, blockWeight, Nat.choose_eq_zero_of_lt hk]

theorem weightedConvolutionBlock_zero (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (n : ℕ) : weightedConvolutionBlock μ ν p n 0 =
      ENNReal.ofReal (1 - p) ^ n • iidSumLaw μ n := by
  simp [weightedConvolutionBlock, blockWeight, iidSumLaw]

theorem weightedConvolutionBlock_last (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (n : ℕ) : weightedConvolutionBlock μ ν p n n =
      ENNReal.ofReal p ^ n • iidSumLaw ν n := by
  simp [weightedConvolutionBlock, blockWeight, iidSumLaw]

theorem weightedConvolutionBlock_succ_zero (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (n : ℕ) : weightedConvolutionBlock μ ν p (n + 1) 0 =
      ENNReal.ofReal (1 - p) • (μ ∗ weightedConvolutionBlock μ ν p n 0) := by
  rw [weightedConvolutionBlock_zero, weightedConvolutionBlock_zero, Measure.conv_smul_right, smul_smul]
  rw [pow_succ']
  rfl

theorem blockWeight_pascal (p : ℝ) (n k : ℕ) (hk : k < n) :
    blockWeight p (n + 1) (k + 1) =
      ENNReal.ofReal (1 - p) * blockWeight p n (k + 1) + ENNReal.ofReal p * blockWeight p n k := by
  have hn : n + 1 - (k + 1) = n - k := by omega
  have hnk : n - k = n - (k + 1) + 1 := by omega
  unfold blockWeight
  rw [Nat.choose_succ_succ, Nat.cast_add, hn, hnk, pow_succ']
  ring

theorem convolve_lower_block (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℕ) :
    μ ∗ (iidSumLaw μ a ∗ iidSumLaw ν b) = iidSumLaw μ (a + 1) ∗ iidSumLaw ν b := by
  exact (Measure.conv_assoc _ _ _).symm

theorem convolve_upper_block (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a b : ℕ) :
    ν ∗ (iidSumLaw μ a ∗ iidSumLaw ν b) = iidSumLaw μ a ∗ iidSumLaw ν (b + 1) := by
  rw [← Measure.conv_assoc, Measure.conv_comm ν (iidSumLaw μ a), Measure.conv_assoc]
  rfl

theorem weightedConvolutionBlock_pascal (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (n k : ℕ) : weightedConvolutionBlock μ ν p (n + 1) (k + 1) =
      ENNReal.ofReal (1 - p) • (μ ∗ weightedConvolutionBlock μ ν p n (k + 1)) +
      ENNReal.ofReal p • (ν ∗ weightedConvolutionBlock μ ν p n k) := by
  rcases lt_trichotomy k n with hk | rfl | hk
  · have hn : n + 1 - (k + 1) = n - k := by omega
    have hnk : n - (k + 1) + 1 = n - k := by omega
    unfold weightedConvolutionBlock
    rw [Measure.conv_smul_right, Measure.conv_smul_right, convolve_lower_block, convolve_upper_block,
      hn, hnk, smul_smul, smul_smul, ← add_smul, ← blockWeight_pascal p n k hk]
  · rw [weightedConvolutionBlock_last, weightedConvolutionBlock_last,
      weightedConvolutionBlock_outside _ _ _ _ _ (by omega)]
    simp only [Measure.conv_zero, smul_zero, zero_add, Measure.conv_smul_right, smul_smul, pow_succ']
    rfl
  · rw [weightedConvolutionBlock_outside _ _ _ _ _ (by omega),
      weightedConvolutionBlock_outside _ _ _ _ _ (by omega),
      weightedConvolutionBlock_outside _ _ _ _ _ hk]
    simp

theorem sfinite_finset_sum (s : Finset ℕ) (ν : ℕ → Measure ℝ) [∀ k, SFinite (ν k)] :
    SFinite (∑ k ∈ s, ν k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    letI := ih
    infer_instance

theorem conv_finset_sum (μ : Measure ℝ) [SFinite μ] (s : Finset ℕ) (ν : ℕ → Measure ℝ)
    [∀ k, SFinite (ν k)] : μ ∗ ∑ k ∈ s, ν k = ∑ k ∈ s, μ ∗ ν k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    letI := sfinite_finset_sum s ν
    rw [Finset.sum_insert ha, Measure.conv_add, ih, Finset.sum_insert ha]

theorem iidSumLaw_mixture_blocks (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    iidSumLaw (mixtureMeasure μ ν p) n = ∑ k ∈ Finset.range (n + 1), weightedConvolutionBlock μ ν p n k := by
  letI := mixtureMeasure_probability μ ν p hp
  induction n with
  | zero => simp [weightedConvolutionBlock_zero, iidSumLaw]
  | succ n ih =>
    letI : ∀ k, SFinite (weightedConvolutionBlock μ ν p n k) := fun k => by unfold weightedConvolutionBlock; infer_instance
    letI := sfinite_finset_sum (Finset.range (n + 1)) (weightedConvolutionBlock μ ν p n)
    change mixtureMeasure μ ν p ∗ iidSumLaw (mixtureMeasure μ ν p) n = _
    rw [ih, mixtureMeasure, Measure.add_conv, Measure.conv_smul_left, Measure.conv_smul_left,
      conv_finset_sum, conv_finset_sum, Finset.smul_sum, Finset.smul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp_rw [weightedConvolutionBlock_pascal]
    rw [Finset.sum_add_distrib, weightedConvolutionBlock_succ_zero]
    have hq : (∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (1 - p) • (μ ∗ weightedConvolutionBlock μ ν p n k)) =
        (∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (1 - p) • (μ ∗ weightedConvolutionBlock μ ν p n (k + 1))) +
          ENNReal.ofReal (1 - p) • (μ ∗ weightedConvolutionBlock μ ν p n 0) := by
      have he := Finset.sum_range_succ' (fun k => ENNReal.ofReal (1 - p) • (μ ∗ weightedConvolutionBlock μ ν p n k)) (n + 1)
      rw [Finset.sum_range_succ, weightedConvolutionBlock_outside _ _ _ _ _ (by omega)] at he
      simpa only [Measure.conv_zero, smul_zero, add_zero] using he
    rw [hq]
    abel

theorem blockWeight_ne_top (p : ℝ) (n k : ℕ) : blockWeight p n k ≠ ⊤ := by
  unfold blockWeight
  finiteness

theorem blockWeight_toReal (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) :
    (blockWeight p n k).toReal = (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
  simp [blockWeight, ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal (sub_nonneg.2 hp.2)]

theorem iidSumLaw_mixture_cdf (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    ProbabilityTheory.cdf (iidSumLaw (mixtureMeasure μ ν p) n) t =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) *
        ProbabilityTheory.cdf (iidSumLaw μ (n - k) ∗ iidSumLaw ν k) t := by
  letI := mixtureMeasure_probability μ ν p hp
  rw [ProbabilityTheory.cdf_eq_real, Measure.real, iidSumLaw_mixture_blocks μ ν p hp n, Measure.finset_sum_apply]
  rw [ENNReal.toReal_sum (by
    intro k hk
    simp only [weightedConvolutionBlock, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (blockWeight_ne_top _ _ _) (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [weightedConvolutionBlock, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    blockWeight_toReal p hp, ProbabilityTheory.cdf_eq_real, Measure.real]

theorem iidSumLaw_shift (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (n : ℕ) :
    iidSumLaw (μ.map (fun x => a + x)) n = (iidSumLaw μ n).map (fun x => (n : ℝ) * a + x) := by
  simpa only [standardizedMeasure, div_one, mul_neg, sub_neg_eq_add, add_comm] using
    iidSumLaw_standardizedMeasure μ (-a) 1 n

theorem conv_upper_shift (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : ℝ) :
    μ ∗ ν.map (fun x => a + x) = (μ ∗ ν).map (fun x => a + x) := by
  rw [← Measure.dirac_conv a ν, ← Measure.conv_assoc, Measure.conv_comm μ (Measure.dirac a),
    Measure.conv_assoc, Measure.dirac_conv]

theorem cdf_shift (μ : Measure ℝ) [IsProbabilityMeasure μ] (a t : ℝ) :
    ProbabilityTheory.cdf (μ.map (fun x => a + x)) t = ProbabilityTheory.cdf μ (t - a) := by
  letI : IsProbabilityMeasure (μ.map (fun x => a + x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, Measure.real, Measure.real,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro h <;> linarith

/-- A row with arbitrary centered conditional noise in each of two label classes. -/
def twoClusterMeasure (P Q : CenteredFourthLaw) (p : ℝ) : Measure ℝ :=
  mixtureMeasure P.measure (Q.measure.map (fun x => 1 + x)) p

theorem iidSumLaw_twoCluster_cdf (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    ProbabilityTheory.cdf (iidSumLaw (twoClusterMeasure P Q p) n) t =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) *
        ProbabilityTheory.cdf (twoNoiseBlock P Q n k).measure (t - k) := by
  letI : IsProbabilityMeasure (Q.measure.map (fun x => 1 + x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [twoClusterMeasure, iidSumLaw_mixture_cdf _ _ p hp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iidSumLaw_shift, mul_one, conv_upper_shift, cdf_shift]
  simp only [twoNoiseBlock, CenteredFourthLaw.conv, CenteredFourthLaw.iid_measure]

end BerryEsseen
