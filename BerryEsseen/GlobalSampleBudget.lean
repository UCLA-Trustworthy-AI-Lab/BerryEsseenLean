import BerryEsseen.GlobalDerivativeBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem appendix_global_gap_lower : Real.exp (-201 * appendixA) ≤ appendixGlobalGap := by
  have h := exponential_relative_sixteenth ((10 : ℝ) ^ 20) (201 * appendixA) (200 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(201 * appendixA) = -201 * appendixA by ring,
    show -(200 * appendixA) = -200 * appendixA by ring] at h
  rw [appendix_global_gap_formula]
  nlinarith only [h, Real.exp_pos (-200 * appendixA)]

theorem appendix_global_sample_bounds (n ℓ : ℕ) (hn : appendixNConf ≤ n)
    (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    1000000 ≤ ℓ ∧ Real.exp (400 * appendixA) ≤ Real.sqrt (ℓ : ℝ) ∧
      2 ≤ (ℓ : ℝ) * appendixGlobalGap ^ 2 := by
  have hnexp := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have he2 : (2 : ℝ) ≤ Real.exp (200 * appendixA) := by
    have h := Real.add_one_le_exp (200 * appendixA)
    linarith [show (1 : ℝ) ≤ 200 * appendixA by norm_num [appendixA]]
  have he := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (800 * appendixA)).le
  rw [← Real.exp_add, show 800 * appendixA + 200 * appendixA = 1000 * appendixA by ring] at he
  have hlower : Real.exp (800 * appendixA) ≤ (ℓ : ℝ) := by nlinarith only [he, hnexp, hℓ]
  have hlbig : (1000000 : ℝ) ≤ ℓ := by
    have h := Real.add_one_le_exp (800 * appendixA)
    linarith [show (1000000 : ℝ) ≤ 1 + 800 * appendixA by norm_num [appendixA]]
  refine ⟨by exact_mod_cast hlbig, ?_, ?_⟩
  · apply (Real.le_sqrt (Real.exp_pos _).le (Nat.cast_nonneg ℓ)).mpr
    rw [← Real.exp_nat_mul]
    convert hlower using 1 <;> ring
  · have hg := appendix_global_gap_lower
    have hg0 : 0 ≤ appendixGlobalGap := (Real.exp_pos _).le.trans hg
    have hsq := pow_le_pow_left₀ (Real.exp_pos (-201 * appendixA)).le hg 2
    have hm := mul_le_mul hlower hsq (by positivity : 0 ≤ Real.exp (-201 * appendixA) ^ 2) (Nat.cast_nonneg ℓ)
    have hid : Real.exp (800 * appendixA) * Real.exp (-201 * appendixA) ^ 2 =
        Real.exp (398 * appendixA) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hid] at hm
    have h := Real.add_one_le_exp (398 * appendixA)
    linarith [show (2 : ℝ) ≤ 1 + 398 * appendixA by norm_num [appendixA]]

theorem exponential_gap_sample_absorption (m g : ℝ) (hm : 0 < m) (hg : 0 ≤ g)
    (hmg : 2 ≤ m * g ^ 2) : m * Real.exp (-m * g) ≤ 1 := by
  rw [show -m * g = -(m * g) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg hm.le hg)
  have hmul := mul_le_mul_of_nonneg_left hmg hm.le
  nlinarith only [h, hmul, mul_nonneg hm.le hg]

/-- Original displayed ratio at N_conf, including its exact coefficient. -/
theorem manuscript_global_original_sample_gap (n ℓ : ℕ) (hn : appendixNConf ≤ n)
    (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) * appendixGlobalGap ∧
      1 < (1 / 2 : ℝ) * (1 / (10 : ℝ) ^ 20) * Real.exp (300 * appendixA) := by
  have hnexp := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have hroot : Real.exp (500 * appendixA) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (Real.exp_pos _).le (Nat.cast_nonneg n)).mpr
    rw [← Real.exp_nat_mul]
    convert hnexp using 1 <;> ring
  have hnum : 1 < (1 / 2 : ℝ) * (1 / (10 : ℝ) ^ 20) * Real.exp (300 * appendixA) := by
    have he := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 300 * appendixA by norm_num [appendixA])
    have hpoly : (2 : ℝ) * 10 ^ 20 < 1 + 300 * appendixA + (300 * appendixA) ^ 2 / 2 := by norm_num [appendixA]
    linarith
  have hformula : Real.exp (500 * appendixA) * appendixGlobalGap =
      (1 / (10 : ℝ) ^ 20) * Real.exp (300 * appendixA) := by
    rw [appendix_global_gap_formula, mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hrootgap := mul_le_mul_of_nonneg_right hroot
    (show 0 ≤ appendixGlobalGap by unfold appendixGlobalGap; positivity)
  rw [hformula] at hrootgap
  have hg : 2 ≤ Real.sqrt (n : ℝ) * appendixGlobalGap := by linarith
  have hmul := mul_le_mul_of_nonneg_right hg (Real.sqrt_nonneg (n : ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs' : (Real.sqrt (n : ℝ) * appendixGlobalGap) * Real.sqrt (n : ℝ) =
      (n : ℝ) * appendixGlobalGap := by
    calc
      _ = Real.sqrt (n : ℝ) ^ 2 * appendixGlobalGap := by ring
      _ = _ := by rw [hs]
  rw [hs'] at hmul
  have hℓg := mul_le_mul_of_nonneg_right hℓ
    (show 0 ≤ appendixGlobalGap by unfold appendixGlobalGap; positivity)
  exact ⟨by nlinarith only [hmul, hℓg], hnum⟩

theorem manuscript_global_original_exponential_absorption (n ℓ : ℕ)
    (hn : appendixNConf ≤ n) (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) (hℓn : ℓ ≤ n) :
    Real.sqrt (ℓ : ℝ) * Real.exp (-(ℓ : ℝ) * appendixGlobalGap) ≤ 1 / Real.sqrt (ℓ : ℝ) ∧
      Real.sqrt (ℓ : ℝ) * Real.exp (-(ℓ : ℝ) / 8) ≤ 1 / Real.sqrt (ℓ : ℝ) := by
  have hnexp := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have hnlarge : (1000000 : ℝ) ≤ n := by
    have he := Real.add_one_le_exp (1000 * appendixA)
    linarith [show (1000000 : ℝ) ≤ 1000 * appendixA + 1 by norm_num [appendixA]]
  have hnr2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have hnr0 := Real.sqrt_nonneg (n : ℝ)
  have hnr : 16 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hr := Real.sqrt_pos.mpr hℓ0
  have hr2 := Real.sq_sqrt hℓ0.le
  have hgap := (manuscript_global_original_sample_gap n ℓ hn hℓ).1
  have hgauss : Real.sqrt (n : ℝ) ≤ (ℓ : ℝ) / 8 := by
    have hh := mul_le_mul_of_nonneg_right hnr hnr0
    nlinarith only [hh, hnr2, hℓ]
  have hnexpRoot : (n : ℝ) ≤ Real.exp (Real.sqrt (n : ℝ)) := by
    have hc := Real.pow_div_factorial_le_exp (Real.sqrt (n : ℝ)) hnr0 3
    norm_num at hc
    have hh := mul_le_mul_of_nonneg_right (show 6 ≤ Real.sqrt (n : ℝ) by linarith) (sq_nonneg (Real.sqrt (n : ℝ)))
    nlinarith only [hc, hh, hnr2]
  have habsorb : (n : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).mpr hnexpRoot
  have hℓnR : (ℓ : ℝ) ≤ n := by exact_mod_cast hℓn
  have hbase : (ℓ : ℝ) * Real.exp (-Real.sqrt (n : ℝ)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hℓnR (Real.exp_pos _).le).trans habsorb
  have hone : (ℓ : ℝ) * Real.exp (-(ℓ : ℝ) * appendixGlobalGap) ≤ 1 := by
    have hh := Real.exp_le_exp.mpr (show -(ℓ : ℝ) * appendixGlobalGap ≤ -Real.sqrt (n : ℝ) by linarith)
    exact (mul_le_mul_of_nonneg_left hh hℓ0.le).trans hbase
  have htwo : (ℓ : ℝ) * Real.exp (-(ℓ : ℝ) / 8) ≤ 1 := by
    have hh := Real.exp_le_exp.mpr (show -(ℓ : ℝ) / 8 ≤ -Real.sqrt (n : ℝ) by linarith)
    exact (mul_le_mul_of_nonneg_left hh hℓ0.le).trans hbase
  constructor
  · apply (le_div_iff₀ hr).mpr
    calc
      _ = Real.sqrt (ℓ : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) * appendixGlobalGap) := by ring
      _ ≤ 1 := by rwa [hr2]
  · apply (le_div_iff₀ hr).mpr
    calc
      _ = Real.sqrt (ℓ : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / 8) := by ring
      _ ≤ 1 := by rwa [hr2]

/-- Preserve the stronger existing interface by applying the manuscript range
with n replaced by ℓ when ℓ exceeds n. -/
theorem appendix_global_exponential_absorption (n ℓ : ℕ) (hn : appendixNConf ≤ n)
    (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    Real.sqrt (ℓ : ℝ) * Real.exp (-(ℓ : ℝ) * appendixGlobalGap) ≤ 1 / Real.sqrt (ℓ : ℝ) ∧
      Real.sqrt (ℓ : ℝ) * Real.exp (-(ℓ : ℝ) / 8) ≤ 1 / Real.sqrt (ℓ : ℝ) := by
  by_cases hℓn : ℓ ≤ n
  · exact manuscript_global_original_exponential_absorption n ℓ hn hℓ hℓn
  · have hnℓ : n ≤ ℓ := by omega
    exact manuscript_global_original_exponential_absorption ℓ ℓ (hn.trans hnℓ)
      (by linarith [show (0 : ℝ) ≤ ℓ from Nat.cast_nonneg ℓ]) le_rfl

end BerryEsseen
