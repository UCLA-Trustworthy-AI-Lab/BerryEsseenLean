import BerryEsseen.EffectiveClusterBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def appendixNConf : ℕ := Nat.ceil (Real.exp (1000 * appendixA))
def appendixGlobalCutoff : ℝ := Real.exp (20 * appendixA)
def appendixRetention : ℝ := Real.exp (-100 * appendixA)
def appendixGlobalGap : ℝ := (10 : ℝ) ^ (-20 : ℤ) * appendixRetention ^ 2
def appendixDerivativeError : ℝ := (10 : ℝ) ^ 10 * appendixRetention * appendixGlobalCutoff ^ 2

theorem log_le_square_root (x : ℝ) (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 2 by positivity)
  rw [Real.log_div hs.ne' (by norm_num), Real.log_sqrt hx.le] at h
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

theorem appendix_conf_sample_size (n : ℕ) (hn : appendixNConf ≤ n) :
    appendixNStar ≤ n ∧ Real.exp (250 * appendixA) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := by
  have hceil := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor
  · apply Nat.ceil_le.mpr
    exact (Real.exp_le_exp.mpr (by norm_num [appendixA] : appendixA ≤ 1000 * appendixA)).trans hceil
  · apply (Real.le_sqrt (Real.exp_pos _).le (Real.sqrt_nonneg _)).mpr
    rw [← Real.exp_nat_mul]
    apply (Real.le_sqrt (Real.exp_pos _).le hn0).mpr
    rw [← Real.exp_nat_mul]
    convert hceil using 1 <;> ring

theorem appendix_rounding_error_decay (n : ℕ) (hn : appendixNConf ≤ n) :
    5 * Real.sqrt (Real.log (n : ℝ) / n) ≤ 5 * Real.exp (-250 * appendixA) := by
  have hb := appendix_conf_sample_size n hn
  have hnNat := (appendix_sample_size_bounds n hb.1).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hss : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_pos.mpr hs
  have hs2 := Real.sq_sqrt hn0.le
  have hss2 := Real.sq_sqrt hs.le
  have hratio : Real.log (n : ℝ) / n ≤ (1 / Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 := by
    calc
      Real.log (n : ℝ) / n ≤ Real.sqrt (n : ℝ) / n := div_le_div_of_nonneg_right (log_le_square_root n hn0) hn0.le
      _ = (1 / Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 := by
        rw [one_div_pow, hss2]
        apply (div_eq_div_iff hn0.ne' hs.ne').mpr
        nlinarith only [hs2]
  have hr : Real.sqrt (Real.log (n : ℝ) / n) ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) := by
    have h := Real.sqrt_le_sqrt hratio
    simpa only [Real.sqrt_sq (show 0 ≤ 1 / Real.sqrt (Real.sqrt (n : ℝ)) by positivity)] using h
  have hinv : 1 / Real.sqrt (Real.sqrt (n : ℝ)) ≤ Real.exp (-250 * appendixA) := by
    rw [show -250 * appendixA = -(250 * appendixA) by ring, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hb.2
  linarith

theorem appendix_retention_bounds :
    0 < appendixRetention ∧ 2000 * appendixRetention < 1 ∧ (10 : ℝ) ^ 5 * appendixRetention ≤ 1 := by
  have h := exponential_sixteenth_bound ((10 : ℝ) ^ 5) (100 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have he : Real.exp (-(100 * appendixA)) = appendixRetention := by unfold appendixRetention; congr 1; ring
  rw [he] at h
  have hp : 0 < appendixRetention := Real.exp_pos _
  exact ⟨hp, by nlinarith, by linarith⟩

theorem appendix_rounding_below_retention (n : ℕ) (hn : appendixNConf ≤ n) :
    5 * Real.sqrt (Real.log (n : ℝ) / n) ≤ appendixRetention := by
  have h := exponential_relative_sixteenth 5 (250 * appendixA) (100 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have he : Real.exp (-(100 * appendixA)) = appendixRetention := by unfold appendixRetention; congr 1; ring
  have he' : Real.exp (-(250 * appendixA)) = Real.exp (-250 * appendixA) := by congr 1; ring
  rw [he, he'] at h
  have hd := appendix_rounding_error_decay n hn
  nlinarith only [hd, h, appendix_retention_bounds.1]

end BerryEsseen
