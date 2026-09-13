import BerryEsseen.EffectiveRoundedMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem appendix_global_gap_formula : appendixGlobalGap =
    (1 / (10 : ℝ) ^ 20) * Real.exp (-200 * appendixA) := by
  have he : appendixRetention ^ 2 = Real.exp (-200 * appendixA) := by
    unfold appendixRetention
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [appendixGlobalGap, he]
  norm_num

theorem manuscript_log_div_self_antitone :
    AntitoneOn (fun x : ℝ => Real.log x / x) {x | Real.exp 1 ≤ x} := by
  intro x hx y hy hxy
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hy0 : 0 < y := (Real.exp_pos 1).trans_le hy
  have hlogx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hyx : 0 ≤ y / x - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hx0]
    simpa using hxy
  rw [div_le_iff₀ hy0, ← sub_le_sub_iff_right (Real.log x)]
  calc
    Real.log y - Real.log x = Real.log (y / x) := by rw [Real.log_div hy0.ne' hx0.ne']
    _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    _ ≤ Real.log x * (y / x - 1) := le_mul_of_one_le_left hyx hlogx
    _ = Real.log x / x * y - Real.log x := by ring

/-- Original rounding budget at the exact lower sample threshold. -/
theorem manuscript_rounding_error_at_threshold (n : ℕ) (hn : appendixNConf ≤ n) :
    Real.sqrt (Real.log (n : ℝ) / n) ≤ Real.sqrt (1000 * appendixA) * Real.exp (-500 * appendixA) := by
  have hnexp := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have he : Real.exp 1 ≤ Real.exp (1000 * appendixA) :=
    Real.exp_le_exp.mpr (by norm_num [appendixA])
  have hmono := manuscript_log_div_self_antitone he (he.trans hnexp) hnexp
  dsimp only at hmono
  rw [Real.log_exp] at hmono
  have hs := Real.sqrt_le_sqrt hmono
  have heq : Real.sqrt (1000 * appendixA / Real.exp (1000 * appendixA)) =
      Real.sqrt (1000 * appendixA) * Real.exp (-500 * appendixA) := by
    have he : Real.exp (1000 * appendixA) = Real.exp (500 * appendixA) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [Real.sqrt_div (by norm_num [appendixA]), he, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos _), div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  rwa [heq] at hs

theorem manuscript_global_rounding_frequency_exact (n : ℕ) (hn : appendixNConf ≤ n) :
    appendixGlobalCutoff * (5 * Real.sqrt (Real.log (n : ℝ) / n)) ≤
      5 * Real.sqrt (1000 * appendixA) * Real.exp (-480 * appendixA) := by
  have hh := mul_le_mul_of_nonneg_left (manuscript_rounding_error_at_threshold n hn)
    (show 0 ≤ 5 * appendixGlobalCutoff by unfold appendixGlobalCutoff; positivity)
  have he : (5 * appendixGlobalCutoff) *
      (Real.sqrt (1000 * appendixA) * Real.exp (-500 * appendixA)) =
      5 * Real.sqrt (1000 * appendixA) * Real.exp (-480 * appendixA) := by
    unfold appendixGlobalCutoff
    rw [show 5 * Real.exp (20 * appendixA) *
      (Real.sqrt (1000 * appendixA) * Real.exp (-500 * appendixA)) =
      5 * Real.sqrt (1000 * appendixA) *
        (Real.exp (20 * appendixA) * Real.exp (-500 * appendixA)) by ring, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hh
  nlinarith only [hh]

theorem manuscript_global_rounding_frequency_strict :
    5 * Real.sqrt (1000 * appendixA) * Real.exp (-480 * appendixA) < appendixGlobalGap := by
  have hs : Real.sqrt (1000 * appendixA) ≤ (10 : ℝ) ^ 9 := by
    exact (Real.sqrt_le_iff).mpr ⟨by positivity, by norm_num [appendixA]⟩
  have hs' := mul_le_mul_of_nonneg_right hs (show 0 ≤ 5 * Real.exp (-480 * appendixA) by positivity)
  have hsmall := exponential_relative_sixteenth (5 * (10 : ℝ) ^ 9 * (10 : ℝ) ^ 20)
    (480 * appendixA) (200 * appendixA) (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(480 * appendixA) = -480 * appendixA by ring,
    show -(200 * appendixA) = -200 * appendixA by ring] at hsmall
  rw [appendix_global_gap_formula]
  nlinarith only [hs', hsmall, Real.exp_pos (-200 * appendixA)]

theorem appendix_global_rounding_frequency_budget (n : ℕ) (hn : appendixNConf ≤ n) :
    appendixGlobalCutoff * (5 * Real.sqrt (Real.log (n : ℝ) / n)) ≤ appendixGlobalGap :=
  (manuscript_global_rounding_frequency_exact n hn).trans manuscript_global_rounding_frequency_strict.le

theorem appendix_global_small_rounding_frequency_budget (n : ℕ) (hn : appendixNConf ≤ n) :
    appendixGlobalCutoff * (5 * Real.sqrt (Real.log (n : ℝ) / n)) ≤ Real.exp (-202 * appendixA) := by
  have hd := mul_le_mul_of_nonneg_left (appendix_rounding_error_decay n hn)
    (Real.exp_pos (20 * appendixA)).le
  have he : Real.exp (20 * appendixA) * (5 * Real.exp (-250 * appendixA)) = 5 * Real.exp (-230 * appendixA) := by
    rw [show Real.exp (20 * appendixA) * (5 * Real.exp (-250 * appendixA)) =
      5 * (Real.exp (20 * appendixA) * Real.exp (-250 * appendixA)) by ring, ← Real.exp_add]
    congr 2
    ring
  rw [he] at hd
  have hsmall := exponential_relative_sixteenth 5 (230 * appendixA) (202 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(230 * appendixA) = -230 * appendixA by ring,
    show -(202 * appendixA) = -202 * appendixA by ring] at hsmall
  change Real.exp (20 * appendixA) * (5 * Real.sqrt (Real.log (n : ℝ) / n)) ≤ _
  nlinarith only [hd, hsmall, Real.exp_pos (-202 * appendixA)]

theorem mixture_spectral_gap_absorption (r g A B e : ℝ) (hr : r ∈ Icc 0 (1 / 100))
    (hg : 0 ≤ g) (hA : A ≤ (1 - r) * B + r + e)
    (hB : B ≤ 1 - 50 * g) (he : e ≤ g) : A ≤ 1 - g := by
  have hB' := mul_le_mul_of_nonneg_left hB (show 0 ≤ 1 - r by linarith [hr.2])
  have hrg := mul_le_mul_of_nonneg_right hr.2 hg
  nlinarith only [hA, hB', he, hrg, hg]

end BerryEsseen
