import BerryEsseen.EffectiveJitterLowFrequency
import BerryEsseen.EffectiveGaussianBounds

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem effective_cluster_exponential_budget (n : ℕ) (hn : 1000000 ≤ n) :
    Real.sqrt (n : ℝ) * Real.exp (-(n : ℝ) / 200) ≤ 1 / (2 * Real.sqrt (n : ℝ)) ∧
      Real.sqrt (n : ℝ) * Real.exp (-3 * (n : ℝ) / 100) ≤ 1 / (20 * Real.sqrt (n : ℝ)) := by
  have hnR : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hr2 := Real.sq_sqrt hn0.le
  have hpoly := mul_nonneg (sub_nonneg.mpr hnR) hn0.le
  have he1 : (n : ℝ) * Real.exp (-(n : ℝ) / 200) ≤ 1 / 2 := by
    rw [show -(n : ℝ) / 200 = -((n : ℝ) / 200) by ring, Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ (n : ℝ) / 200)
    nlinarith only [h, hpoly, hnR]
  have he2 : (n : ℝ) * Real.exp (-3 * (n : ℝ) / 100) ≤ 1 / 20 := by
    rw [show -3 * (n : ℝ) / 100 = -(3 * (n : ℝ) / 100) by ring, Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 3 * (n : ℝ) / 100)
    nlinarith only [h, hpoly, hnR]
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (n : ℝ))).mpr
    nth_rw 1 [← hr2] at he1
    nlinarith only [he1]
  · apply (le_div_iff₀ (by positivity : 0 < 20 * Real.sqrt (n : ℝ))).mpr
    nth_rw 1 [← hr2] at he2
    nlinarith only [he2]

def effectiveClusterFourierBudget (n : ℕ) (s T : ℝ) : ℝ :=
  7 / (n : ℝ) + (1 / (n : ℝ) + 5 * s * T ^ 2 / Real.sqrt (n : ℝ)) * (1 + Real.log T) +
    2 * Real.log (2 * T) * Real.exp (-(n : ℝ) / 200) + 20 * Real.exp (-3 * (n : ℝ) / 100)

def effectiveClusterError (n : ℕ) (ε T : ℝ) : ℝ :=
  4 * (1 + Real.log T) / Real.sqrt (n : ℝ) + 2 * ε ^ 2 * T ^ 2 * (1 + Real.log T) + 50 / T

theorem effective_cluster_scaled_fourier_budget (n : ℕ) (hn : 1000000 ≤ n)
    (s ε T : ℝ) (hs : 0 ≤ s) (hsε : s ≤ ε ^ 2) (hT : 10 ≤ T) :
    Real.sqrt (n : ℝ) * effectiveClusterFourierBudget n s T ≤
      10 * (1 + Real.log T) / Real.sqrt (n : ℝ) + 5 * ε ^ 2 * T ^ 2 * (1 + Real.log T) := by
  let r := Real.sqrt (n : ℝ)
  let H := 1 + Real.log T
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hT0 : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hlog2 : Real.log (2 * T) ≤ H := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    have h := Real.log_two_lt_d9
    dsimp [H]
    linarith
  have hlog2n : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have he := effective_cluster_exponential_budget n hn
  have hE1 : 2 * r * Real.log (2 * T) * Real.exp (-(n : ℝ) / 200) ≤ H / r := by
    have h := mul_le_mul_of_nonneg_right he.1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog2n)
    have h' := div_le_div_of_nonneg_right hlog2 hr.le
    have heq : (1 / (2 * r)) * (2 * Real.log (2 * T)) = Real.log (2 * T) / r := by ring
    change (r * Real.exp (-(n : ℝ) / 200)) * (2 * Real.log (2 * T)) ≤ _ at h
    rw [heq] at h
    nlinarith only [h, h']
  have hE2 : 20 * r * Real.exp (-3 * (n : ℝ) / 100) ≤ H / r := by
    have h := mul_le_mul_of_nonneg_left he.2 (by norm_num : (0 : ℝ) ≤ 20)
    have h' := div_le_div_of_nonneg_right hH hr.le
    have heq : 20 * (1 / (20 * r)) = 1 / r := by ring
    change 20 * (r * Real.exp (-3 * (n : ℝ) / 100)) ≤ _ at h
    rw [heq] at h
    nlinarith only [h, h']
  have hsbudget := mul_le_mul_of_nonneg_right hsε (mul_nonneg (sq_nonneg T) (by linarith : 0 ≤ H))
  have h7 : 7 / r ≤ 7 * (H / r) := by
    convert div_le_div_of_nonneg_right (show (7 : ℝ) ≤ 7 * H by linarith) hr.le using 1 <;> ring
  have hid : r * effectiveClusterFourierBudget n s T =
      7 / r + H / r + 5 * s * T ^ 2 * H +
        2 * r * Real.log (2 * T) * Real.exp (-(n : ℝ) / 200) + 20 * r * Real.exp (-3 * (n : ℝ) / 100) := by
    unfold effectiveClusterFourierBudget
    change r * (7 / (n : ℝ) + (1 / (n : ℝ) + 5 * s * T ^ 2 / r) * H +
      2 * Real.log (2 * T) * Real.exp (-↑n / 200) + 20 * Real.exp (-3 * ↑n / 100)) = _
    rw [show 7 / (n : ℝ) = 7 / r ^ 2 by rw [hr2], show 1 / (n : ℝ) = 1 / r ^ 2 by rw [hr2]]
    field_simp
    <;> ring
  change r * effectiveClusterFourierBudget n s T ≤ 10 * H / r + 5 * ε ^ 2 * T ^ 2 * H
  rw [hid, show 10 * H / r = 10 * (H / r) by ring]
  nlinarith only [hE1, hE2, hsbudget, h7]

theorem effective_cluster_smoothing_budget (n : ℕ) (hn : 1000000 ≤ n)
    (s ε T σ : ℝ) (hs : 0 ≤ s) (hsε : s ≤ ε ^ 2) (hT : 10 ≤ T) (hσ : 0.48 ≤ σ) :
    Real.sqrt (n : ℝ) * ((1 / 4 : ℝ) * effectiveClusterFourierBudget n s T +
      24 / (σ * Real.sqrt (n : ℝ) * T)) ≤ effectiveClusterError n ε T := by
  let r := Real.sqrt (n : ℝ)
  let H := 1 + Real.log T
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hT0 : 0 < T := by linarith
  have hσ0 : 0 < σ := by linarith
  have hH : 0 ≤ H := by dsimp [H]; linarith [Real.log_nonneg (show 1 ≤ T by linarith)]
  have hbound := effective_cluster_scaled_fourier_budget n hn s ε T hs hsε hT
  have hscaled : (1 / 4 : ℝ) * (r * effectiveClusterFourierBudget n s T) ≤
      (1 / 4) * (10 * H / r + 5 * ε ^ 2 * T ^ 2 * H) :=
    mul_le_mul_of_nonneg_left hbound (by norm_num)
  have hmain : (1 / 4 : ℝ) * (10 * H / r + 5 * ε ^ 2 * T ^ 2 * H) ≤
      4 * H / r + 2 * ε ^ 2 * T ^ 2 * H := by
    have h1 : 0 ≤ H / r := by positivity
    have h2 : 0 ≤ ε ^ 2 * T ^ 2 * H := by positivity
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    nlinarith only [h1, h2]
  have htail : 24 / (σ * T) ≤ 50 / T := by
    apply (div_le_div_iff₀ (by positivity : 0 < σ * T) hT0).mpr
    have h := mul_le_mul_of_nonneg_right hσ hT0.le
    nlinarith only [h]
  have he : r * ((1 / 4 : ℝ) * effectiveClusterFourierBudget n s T + 24 / (σ * r * T)) =
      (1 / 4) * (r * effectiveClusterFourierBudget n s T) + 24 / (σ * T) := by
    field_simp
    <;> ring
  change r * ((1 / 4 : ℝ) * effectiveClusterFourierBudget n s T + 24 / (σ * r * T)) ≤
    4 * H / r + 2 * ε ^ 2 * T ^ 2 * H + 50 / T
  rw [he]
  linarith only [hscaled, hmain, htail]

end BerryEsseen
