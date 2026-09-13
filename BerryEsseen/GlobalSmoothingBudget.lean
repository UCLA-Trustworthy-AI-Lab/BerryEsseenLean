import BerryEsseen.GlobalSampleBudget
import BerryEsseen.GlobalFourierAssembly

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem appendix_global_scaled_fourier_budget (n ℓ : ℕ) (hn : appendixNConf ≤ n)
    (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    Real.sqrt (ℓ : ℝ) * globalFourierBudget ℓ appendixDerivativeError appendixGlobalCutoff appendixGlobalGap ≤
      30 * (1 + Real.log appendixGlobalCutoff) / Real.sqrt (ℓ : ℝ) +
        12 * (1 + Real.log appendixGlobalCutoff) * appendixDerivativeError := by
  let r := Real.sqrt (ℓ : ℝ)
  let T := appendixGlobalCutoff
  let H := 1 + Real.log T
  have hb := appendix_global_sample_bounds n ℓ hn hℓ
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < ℓ by omega))
  have hr2 : r ^ 2 = (ℓ : ℝ) := Real.sq_sqrt (Nat.cast_nonneg ℓ)
  have hT : 10 ≤ T := appendix_global_cutoff_ge_ten
  have hT0 : 0 < T := by linarith
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg (show 1 ≤ T by linarith)]
  have hlog2 : Real.log (2 * T) ≤ H := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    dsimp [H]
    linarith [Real.log_two_lt_d9]
  have hlog2n : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have he := appendix_global_exponential_absorption n ℓ hn hℓ
  have he1 := mul_le_mul_of_nonneg_right he.1 (show 0 ≤ 2 * Real.log (2 * T) by positivity)
  have he2 := mul_le_mul_of_nonneg_right he.2 (by norm_num : (0 : ℝ) ≤ 5)
  have hlogdiv := div_le_div_of_nonneg_right hlog2 hr.le
  have hHdiv := div_le_div_of_nonneg_right hH hr.le
  have hid : r * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap =
      11 / r + 12 * H / r + 12 * H * appendixDerivativeError +
      2 * Real.log (2 * T) * (r * Real.exp (-(ℓ : ℝ) * appendixGlobalGap)) +
      5 * (r * Real.exp (-(ℓ : ℝ) / 8)) := by
    unfold globalFourierBudget
    change r * (11 / (ℓ : ℝ) + 12 * H * (1 / (ℓ : ℝ) + appendixDerivativeError / r) +
      2 * Real.log (2 * T) * Real.exp (-(ℓ : ℝ) * appendixGlobalGap) + 5 * Real.exp (-(ℓ : ℝ) / 8)) = _
    rw [← hr2]
    field_simp
    <;> ring
  change r * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap ≤ 30 * H / r + 12 * H * appendixDerivativeError
  rw [hid]
  change (r * Real.exp (-(ℓ : ℝ) * appendixGlobalGap)) * (2 * Real.log (2 * T)) ≤ (1 / r) * (2 * Real.log (2 * T)) at he1
  change (r * Real.exp (-(ℓ : ℝ) / 8)) * 5 ≤ (1 / r) * 5 at he2
  rw [show (1 / r) * (2 * Real.log (2 * T)) = 2 * (Real.log (2 * T) / r) by ring] at he1
  rw [show 30 * H / r = 30 * (H / r) by ring, show 12 * H / r = 12 * (H / r) by ring,
    show 11 / r = 11 * (1 / r) by ring]
  nlinarith only [he1, he2, hlogdiv, hHdiv]

theorem appendix_global_smoothing_budget (n ℓ : ℕ) (hn : appendixNConf ≤ n)
    (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    Real.sqrt (ℓ : ℝ) * ((1 / 4 : ℝ) *
      globalFourierBudget ℓ appendixDerivativeError appendixGlobalCutoff appendixGlobalGap +
      24 / (Real.sqrt (ℓ : ℝ) * appendixGlobalCutoff)) ≤
      10 * (1 + Real.log appendixGlobalCutoff) / Real.sqrt (ℓ : ℝ) +
      3 * (1 + Real.log appendixGlobalCutoff) * appendixDerivativeError + 24 / appendixGlobalCutoff := by
  let r := Real.sqrt (ℓ : ℝ)
  let T := appendixGlobalCutoff
  let H := 1 + Real.log T
  have hb := appendix_global_sample_bounds n ℓ hn hℓ
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < ℓ by omega))
  have hT : 10 ≤ T := appendix_global_cutoff_ge_ten
  have hT0 : 0 < T := by linarith
  have hH : 0 ≤ H := by dsimp [H]; linarith [Real.log_nonneg (show 1 ≤ T by linarith)]
  have hδ := appendix_derivative_error_small.1
  have hbound := appendix_global_scaled_fourier_budget n ℓ hn hℓ
  have hm := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hid : r * ((1 / 4 : ℝ) * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap +
      24 / (r * T)) =
      (1 / 4) * (r * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap) + 24 / T := by
    field_simp
    <;> ring
  change r * ((1 / 4 : ℝ) * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap + 24 / (r * T)) ≤ _
  rw [hid]
  change _ ≤ 10 * H / r + 3 * H * appendixDerivativeError + 24 / T
  have hmain : (1 / 4 : ℝ) * (r * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap) ≤
      10 * H / r + 3 * H * appendixDerivativeError := by
    have hpos : 0 ≤ H / r := by positivity
    change (1 / 4 : ℝ) * (r * globalFourierBudget ℓ appendixDerivativeError T appendixGlobalGap) ≤
      (1 / 4) * (30 * H / r + 12 * H * appendixDerivativeError) at hm
    simp only [div_eq_mul_inv] at hm hpos ⊢
    nlinarith only [hm, hpos]
  exact add_le_add hmain le_rfl

theorem appendix_global_final_budget (n ℓ : ℕ) (hn : appendixNConf ≤ n)
    (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    10 * (1 + Real.log appendixGlobalCutoff) / Real.sqrt (ℓ : ℝ) +
      3 * (1 + Real.log appendixGlobalCutoff) * appendixDerivativeError + 24 / appendixGlobalCutoff ≤
      Real.exp (-19 * appendixA) := by
  have hb := appendix_global_sample_bounds n ℓ hn hℓ
  have hH : 0 ≤ 10 * (1 + 20 * appendixA) := by norm_num [appendixA]
  have hr : 0 < Real.sqrt (ℓ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < ℓ by omega))
  have hceil := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsℓ := Real.sq_sqrt (Nat.cast_nonneg ℓ)
  have he2 : Real.exp (500 * appendixA) ^ 2 = Real.exp (1000 * appendixA) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hroot : Real.exp (500 * appendixA) ≤ Real.sqrt 2 * Real.sqrt (ℓ : ℝ) := by
    nlinarith only [hceil, hℓ, hs2, hsℓ, he2, Real.exp_pos (500 * appendixA),
      mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hr.le]
  have hi : 1 / Real.sqrt (ℓ : ℝ) ≤ Real.sqrt 2 * Real.exp (-500 * appendixA) := by
    rw [show -500 * appendixA = -(500 * appendixA) by ring, Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hr (Real.exp_pos _)).mpr
    simpa only [one_mul] using hroot
  have hfirst := mul_le_mul_of_nonneg_left hi hH
  have hs2le : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith only [hs2, Real.sqrt_nonneg (2 : ℝ)]
  have hfirst' : 10 * (1 + 20 * appendixA) / Real.sqrt (ℓ : ℝ) ≤
      20 * (1 + 20 * appendixA) * Real.exp (-500 * appendixA) := by
    have hm := mul_le_mul_of_nonneg_right hs2le (mul_nonneg hH (Real.exp_pos (-500 * appendixA)).le)
    simp only [div_eq_mul_inv] at hfirst ⊢
    nlinarith only [hfirst, hm]
  have h1 := exponential_relative_sixteenth (20 * (1 + 20 * appendixA)) (500 * appendixA) (19 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth (3 * (1 + 20 * appendixA) * (10 : ℝ) ^ 10) (60 * appendixA) (19 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h3 := exponential_relative_sixteenth 24 (20 * appendixA) (19 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [appendix_derivative_error_formula, appendixGlobalCutoff, Real.log_exp]
  rw [show 24 / Real.exp (20 * appendixA) = 24 * Real.exp (-(20 * appendixA)) by
    rw [Real.exp_neg, div_eq_mul_inv]]
  rw [show -(19 * appendixA) = -19 * appendixA by ring] at h1 h2 h3
  rw [show -(60 * appendixA) = -60 * appendixA by ring] at h2
  rw [show -(500 * appendixA) = -500 * appendixA by ring] at h1
  nlinarith only [hfirst', h1, h2, h3, Real.exp_pos (-19 * appendixA)]

end BerryEsseen
