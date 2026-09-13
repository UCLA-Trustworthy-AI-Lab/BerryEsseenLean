import BerryEsseen.EffectiveLocalMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def appendixNStar : ℕ := Nat.ceil (Real.exp appendixA)
def appendixClusterGap : ℝ := Real.exp (-5000000000000)
def appendixClusterCutoff : ℝ := Real.exp (10000000000000)

theorem appendix_sample_size_bounds (n : ℕ) (hn : appendixNStar ≤ n) :
    10 ^ 100 ≤ n ∧ Real.exp (50000000000000) ≤ Real.sqrt (n : ℝ) := by
  have hceil := (Nat.le_ceil (Real.exp appendixA)).trans (show (appendixNStar : ℝ) ≤ n by exact_mod_cast hn)
  have he2 : (2 : ℝ) ^ 1000 ≤ Real.exp 1000 := by
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 1000
  have hExp : Real.exp 1000 ≤ Real.exp appendixA := Real.exp_le_exp.mpr (by norm_num [appendixA])
  have hpowers : (10 : ℝ) ^ 100 ≤ (2 : ℝ) ^ 1000 := by
    simpa only [← pow_mul, Nat.reduceMul] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10)
      (show (10 : ℝ) ≤ 2 ^ 10 by norm_num) 100
  have hN : (10 : ℝ) ^ 100 ≤ n := hpowers.trans (he2.trans (hExp.trans hceil))
  refine ⟨by exact_mod_cast hN, ?_⟩
  apply (Real.le_sqrt (Real.exp_pos _).le (Nat.cast_nonneg n)).mpr
  have he : Real.exp (50000000000000) ^ 2 = Real.exp appendixA := by
    rw [← Real.exp_nat_mul]
    norm_num [appendixA]
  rw [he]
  exact hceil

theorem exponential_sixteenth_bound (K x : ℝ) (hx : 0 ≤ x)
    (hbudget : 16 * K ≤ 1 + x + x ^ 2 / 2) : K * Real.exp (-x) ≤ 1 / 16 := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.quadratic_le_exp_of_nonneg hx
  linarith

theorem exponential_relative_sixteenth (K a d : ℝ) (hx : 0 ≤ a - d)
    (hbudget : 16 * K ≤ 1 + (a - d) + (a - d) ^ 2 / 2) :
    K * Real.exp (-a) ≤ Real.exp (-d) / 16 := by
  have h := mul_le_mul_of_nonneg_right (exponential_sixteenth_bound K (a - d) hx hbudget) (Real.exp_pos (-d)).le
  have hid : K * Real.exp (-(a - d)) * Real.exp (-d) = K * Real.exp (-a) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hid] at h
  convert h using 1 <;> ring

theorem appendix_noise_and_cutoff_bounds :
    Real.exp (-appendixA) ≤ 1 / (10 : ℝ) ^ 12 ∧ 10 ≤ appendixClusterCutoff ∧
      Real.exp (-appendixA) ≤ (100 * appendixClusterCutoff)⁻¹ := by
  have hE : (10 : ℝ) ^ 12 ≤ Real.exp appendixA := by
    have h := Real.add_one_le_exp appendixA
    norm_num [appendixA] at h ⊢
    linarith
  have hn : Real.exp (-appendixA) ≤ 1 / (10 : ℝ) ^ 12 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hE
  refine ⟨hn, ?_, ?_⟩
  · unfold appendixClusterCutoff
    linarith [Real.add_one_le_exp (10000000000000 : ℝ)]
  · have ht : 0 < 100 * appendixClusterCutoff := by unfold appendixClusterCutoff; positivity
    rw [inv_eq_one_div]
    apply (le_div_iff₀ ht).mpr
    have h := exponential_sixteenth_bound 100 90000000000000 (by norm_num) (by norm_num)
    have he : Real.exp (-appendixA) * (100 * appendixClusterCutoff) = 100 * Real.exp (-90000000000000) := by
      unfold appendixClusterCutoff appendixA
      rw [show Real.exp (-((10 : ℝ) ^ 14)) * (100 * Real.exp 10000000000000) =
        100 * (Real.exp (-((10 : ℝ) ^ 14)) * Real.exp 10000000000000) by ring, ← Real.exp_add]
      norm_num
    rw [he]
    linarith

theorem effective_cluster_final_budget (n : ℕ) (hn : appendixNStar ≤ n) (s : ℝ)
    (hs : s ≤ Real.exp (-appendixA) ^ 2) :
    effectiveClusterError n (Real.exp (-appendixA)) appendixClusterCutoff +
      4 / Real.sqrt (n : ℝ) + 20 * s ≤ appendixClusterGap / 2 := by
  let r := Real.sqrt (n : ℝ)
  have hr := (appendix_sample_size_bounds n hn).2
  have hinv : 1 / r ≤ Real.exp (-50000000000000) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hr
  have hlog : Real.log appendixClusterCutoff = 10000000000000 := Real.log_exp _
  have hε2 : Real.exp (-appendixA) ^ 2 = Real.exp (-200000000000000) := by
    rw [← Real.exp_nat_mul]
    norm_num [appendixA]
  have hεT : Real.exp (-appendixA) ^ 2 * appendixClusterCutoff ^ 2 = Real.exp (-180000000000000) := by
    rw [hε2, appendixClusterCutoff, ← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have hTinv : 50 / appendixClusterCutoff = 50 * Real.exp (-10000000000000) := by
    rw [appendixClusterCutoff, Real.exp_neg, div_eq_mul_inv]
  have hlow : 4 * (1 + Real.log appendixClusterCutoff) / r + 4 / r ≤
      40000000000008 * Real.exp (-50000000000000) := by
    rw [hlog, ← add_div]
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 40000000000008)
    convert h using 1 <;> ring
  have hsmall : 20 * s ≤ 20 * Real.exp (-200000000000000) := by rw [hε2] at hs; linarith
  have h1 := exponential_relative_sixteenth 40000000000008 50000000000000 5000000000000 (by norm_num) (by norm_num)
  have h2 := exponential_relative_sixteenth 20000000000002 180000000000000 5000000000000 (by norm_num) (by norm_num)
  have h3 := exponential_relative_sixteenth 50 10000000000000 5000000000000 (by norm_num) (by norm_num)
  have h4 := exponential_relative_sixteenth 20 200000000000000 5000000000000 (by norm_num) (by norm_num)
  have hnoise : 2 * Real.exp (-appendixA) ^ 2 * appendixClusterCutoff ^ 2 * (1 + Real.log appendixClusterCutoff) =
      20000000000002 * Real.exp (-180000000000000) := by
    rw [mul_assoc 2, hεT, hlog]
    ring
  unfold effectiveClusterError
  rw [hnoise, hTinv]
  change 4 * (1 + Real.log appendixClusterCutoff) / r + 20000000000002 * Real.exp (-180000000000000) +
    50 * Real.exp (-10000000000000) + 4 / r + 20 * s ≤ appendixClusterGap / 2
  unfold appendixClusterGap
  nlinarith only [hlow, hsmall, h1, h2, h3, h4, Real.exp_pos (-5000000000000)]

end BerryEsseen
