import BerryEsseen.EffectiveClusterBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_effective_cluster_error_budget (n : ℕ) (hn : appendixNStar ≤ n) :
    effectiveClusterError n (Real.exp (-appendixA)) appendixClusterCutoff ≤ appendixClusterGap / 4 := by
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
  have hlow : 4 * (1 + Real.log appendixClusterCutoff) / r ≤
      40000000000004 * Real.exp (-50000000000000) := by
    rw [hlog]
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 40000000000004)
    convert h using 1 <;> ring
  have h1 := exponential_relative_sixteenth 40000000000004 50000000000000 5000000000000 (by norm_num) (by norm_num)
  have h2 := exponential_relative_sixteenth 20000000000002 180000000000000 5000000000000 (by norm_num) (by norm_num)
  have h3 := exponential_relative_sixteenth 50 10000000000000 5000000000000 (by norm_num) (by norm_num)
  have hnoise : 2 * Real.exp (-appendixA) ^ 2 * appendixClusterCutoff ^ 2 * (1 + Real.log appendixClusterCutoff) =
      20000000000002 * Real.exp (-180000000000000) := by
    rw [mul_assoc 2, hεT, hlog]
    ring
  unfold effectiveClusterError
  rw [hnoise, hTinv]
  change 4 * (1 + Real.log appendixClusterCutoff) / r + 20000000000002 * Real.exp (-180000000000000) +
    50 * Real.exp (-10000000000000) ≤ appendixClusterGap / 4
  unfold appendixClusterGap
  nlinarith only [hlow, h1, h2, h3, Real.exp_pos (-5000000000000)]

theorem manuscript_effective_cluster_shift_moment_budget (n : ℕ) (hn : appendixNStar ≤ n) (s : ℝ)
    (hs : s ≤ Real.exp (-appendixA) ^ 2) :
    2 / Real.sqrt (n : ℝ) + 100 * s ≤ appendixClusterGap / 4 := by
  have hr := (appendix_sample_size_bounds n hn).2
  have hinv : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-50000000000000) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hr
  have hε2 : Real.exp (-appendixA) ^ 2 = Real.exp (-200000000000000) := by
    rw [← Real.exp_nat_mul]
    norm_num [appendixA]
  rw [hε2] at hs
  have h1 := exponential_relative_sixteenth 2 50000000000000 5000000000000 (by norm_num) (by norm_num)
  have h2 := exponential_relative_sixteenth 100 200000000000000 5000000000000 (by norm_num) (by norm_num)
  unfold appendixClusterGap
  simp only [div_eq_mul_inv] at hinv ⊢
  nlinarith only [hinv, hs, h1, h2, Real.exp_pos (-5000000000000)]

end BerryEsseen
