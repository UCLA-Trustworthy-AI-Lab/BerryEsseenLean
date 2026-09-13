import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Exact algebra for the constants in He--Cheng, September 2026.
No probability theorem is assumed in this module. -/
noncomputable section
namespace BerryEsseen

def cStar : ℝ := 3 + Real.sqrt 10
def pE : ℝ := (4 - Real.sqrt 10) / 2
def qE : ℝ := 1 - pE
def sigmaE : ℝ := Real.sqrt (pE * qE)
def aE : ℝ := pE / sigmaE
def bE : ℝ := qE / sigmaE
def hE : ℝ := 1 / sigmaE
def betaE : ℝ := (pE ^ 2 + qE ^ 2) / sigmaE
def kappaE : ℝ := (qE - pE) / sigmaE
def phi0 : ℝ := 1 / Real.sqrt (2 * Real.pi)
def cE : ℝ := (3 + Real.sqrt 10) / (6 * Real.sqrt (2 * Real.pi))

theorem sqrt10_sq : (Real.sqrt (10 : ℝ)) ^ 2 = 10 := Real.sq_sqrt (by norm_num)

theorem sqrt10_bounds : 3 < Real.sqrt (10 : ℝ) ∧ Real.sqrt (10 : ℝ) < 4 := by
  have := Real.sqrt_nonneg (10 : ℝ)
  constructor <;> nlinarith [sqrt10_sq]

theorem pE_bounds : 2 / 5 < pE ∧ pE < 9 / 20 := by
  have hs := sqrt10_bounds
  unfold pE
  constructor <;> nlinarith [sqrt10_sq]

theorem pE_pos : 0 < pE := lt_trans (by norm_num) pE_bounds.1
theorem pE_lt_half : pE < 1 / 2 := lt_trans pE_bounds.2 (by norm_num)
theorem qE_pos : 0 < qE := by unfold qE; linarith [pE_lt_half]
theorem pE_add_qE : pE + qE = 1 := by unfold qE; ring
theorem sigmaE_pos : 0 < sigmaE := Real.sqrt_pos.2 (mul_pos pE_pos qE_pos)
theorem sigmaE_sq : sigmaE ^ 2 = pE * qE := Real.sq_sqrt (le_of_lt (mul_pos pE_pos qE_pos))
theorem cStar_gt_one : 1 < cStar := by unfold cStar; linarith [sqrt10_bounds.1]
theorem phi0_pos : 0 < phi0 := by unfold phi0; positivity
theorem cE_eq : cE = phi0 * cStar / 6 := by unfold cE phi0 cStar; ring
theorem cE_pos : 0 < cE := by
  rw [cE_eq]
  exact div_pos (mul_pos phi0_pos (lt_trans zero_lt_one cStar_gt_one)) (by norm_num)

theorem signed_moment_identity : cStar * (qE - pE) = 1 := by
  unfold cStar qE pE
  nlinarith [sqrt10_sq]

theorem beta_identity : cStar * betaE = Real.sqrt 10 / sigmaE := by
  have h : cStar * (pE ^ 2 + qE ^ 2) = Real.sqrt 10 := by
    simp only [cStar, qE, pE]
    nlinarith [sqrt10_sq, mul_self_nonneg (Real.sqrt (10 : ℝ) - 3)]
  unfold betaE
  rw [← mul_div_assoc, h]

theorem span_identity : aE + bE = hE := by
  unfold aE bE hE
  rw [← add_div, pE_add_qE]

/-- The exact quadratic deficit used in the effective local theorem. -/
theorem bernoulli_deficit_identity (p : ℝ) :
    cStar * (p ^ 2 + (1 - p) ^ 2) - 2 * (2 - p) =
      2 * cStar * (p - pE) ^ 2 := by
  have hs := sqrt10_sq
  unfold cStar pE
  nlinarith [hs, mul_self_nonneg (Real.sqrt (10 : ℝ) - 3)]

theorem bernoulli_deficit_nonneg (p : ℝ) :
    2 * (2 - p) ≤ cStar * (p ^ 2 + (1 - p) ^ 2) := by
  have h := bernoulli_deficit_identity p
  have hp : 0 ≤ 2 * cStar * (p - pE) ^ 2 :=
    mul_nonneg (by linarith [cStar_gt_one]) (sq_nonneg _)
  linarith

theorem bernoulli_deficit_eq_zero_iff (p : ℝ) :
    cStar * (p ^ 2 + (1 - p) ^ 2) - 2 * (2 - p) = 0 ↔ p = pE := by
  rw [bernoulli_deficit_identity]
  have hc : (2 * cStar : ℝ) ≠ 0 := by linarith [cStar_gt_one]
  simp [mul_eq_zero, hc, sub_eq_zero]

theorem affine_left_endpoint :
    pE - Real.sqrt 10 / 2 * pE = -(pE * qE) := by
  simp only [qE, pE]
  nlinarith [sqrt10_sq]

theorem affine_right_endpoint :
    pE + Real.sqrt 10 / 2 * qE = 9 / 2 - Real.sqrt 10 := by
  simp only [qE, pE]
  nlinarith [sqrt10_sq]

theorem affine_endpoints_inside :
    -1 < pE - Real.sqrt 10 / 2 * pE ∧
      pE + Real.sqrt 10 / 2 * qE < 2 := by
  rw [affine_left_endpoint, affine_right_endpoint]
  have hp := pE_bounds
  have hq := qE_pos
  have hpq := pE_add_qE
  constructor
  · nlinarith [sq_nonneg (pE - qE)]
  · linarith [sqrt10_bounds.1]

end BerryEsseen
