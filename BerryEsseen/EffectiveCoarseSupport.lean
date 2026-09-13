import BerryEsseen.EffectiveContactBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The numerical parameter interval printed in the coarse-support argument. -/
theorem manuscript_esseen_coarse_parameters :
    pE ∈ Icc 0.418 0.420 ∧ sigmaE ∈ Icc 0.49 0.5 := by
  have hp : pE ∈ Icc 0.418 0.420 := by
    unfold pE
    constructor <;> nlinarith [sqrt10_sq, Real.sqrt_nonneg (10 : ℝ)]
  refine ⟨hp, ?_, ?_⟩
  · have hprod := mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)
    have he := sigmaE_sq
    rw [show qE = 1 - pE from rfl] at he
    nlinarith [he, sigmaE_pos, hp.1, hp.2]
  · nlinarith [sigmaE_sq, sigmaE_pos, pE_add_qE, sq_nonneg (pE - qE)]

/-- The manuscript's two strict root estimates, not the former 1.5 and 2. -/
theorem manuscript_esseen_contact_roots :
    Real.sqrt 10 / 2 * aE < 1.363 ∧ Real.sqrt 10 / 2 * bE < 1.89 := by
  have hp := manuscript_esseen_coarse_parameters.1
  have hσ := manuscript_esseen_coarse_parameters.2.1
  have hs : Real.sqrt 10 ≤ 3.164 := by
    nlinarith [sqrt10_sq, Real.sqrt_nonneg (10 : ℝ)]
  have ha : aE ≤ 0.420 / 0.49 := by
    unfold aE
    apply (div_le_iff₀ sigmaE_pos).mpr
    nlinarith [hp.2]
  have hb : bE ≤ 0.582 / 0.49 := by
    unfold bE
    apply (div_le_iff₀ sigmaE_pos).mpr
    nlinarith [hp.1, pE_add_qE]
  have h1 := mul_le_mul hs ha aE_pos.le (by norm_num : (0 : ℝ) ≤ 3.164)
  have h2 := mul_le_mul hs hb bE_pos.le (by norm_num : (0 : ℝ) ≤ 3.164)
  constructor <;> norm_num at h1 h2 ⊢ <;> nlinarith only [h1, h2]

theorem esseen_contact_roots_effective :
    Real.sqrt 10 / 2 * aE ≤ 1.5 ∧ Real.sqrt 10 / 2 * bE ≤ 2 := by
  have h := manuscript_esseen_contact_roots
  constructor <;> linarith [h.1, h.2]

theorem effectiveContactLimit_negative_outside (y : ℝ)
    (hy : pE + sigmaE * y ∉ Icc (-1 / 2) (3 / 2)) :
    effectiveContactLimit y < -1 / 10 := by
  have hpE := manuscript_esseen_coarse_parameters.1
  have hσ : sigmaE ≤ 1 / 2 := by
    linarith [manuscript_esseen_coarse_parameters.2.2]
  have hc : 6 ≤ cStar := by unfold cStar; nlinarith [sqrt10_sq, Real.sqrt_nonneg (10 : ℝ)]
  have hl := manuscript_esseen_contact_roots.1
  have hr := manuscript_esseen_contact_roots.2
  have hleq : 3 * cStar * betaE / 2 = (cStar + 1) * (Real.sqrt 10 / 2 * aE) := by
    have h := esseen_contact_left_root
    apply_fun (fun x : ℝ => x * (2 * (cStar + 1))) at h
    have hz : 2 * (cStar + 1) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hz] at h
    linarith only [h]
  have hreq : 3 * cStar * betaE / 2 = (cStar - 1) * (Real.sqrt 10 / 2 * bE) := by
    have h := esseen_contact_right_root
    apply_fun (fun x : ℝ => x * (2 * (cStar - 1))) at h
    have hz : 2 * (cStar - 1) ≠ 0 := by linarith
    rw [div_mul_cancel₀ _ hz] at h
    linarith only [h]
  have hp : (2 : ℝ) ≤ contactPolynomial cStar betaE y := by
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · have hyn : y < 0 := by nlinarith [sigmaE_pos, pE_pos]
      have hm := mul_le_mul_of_nonpos_right hσ hyn.le
      have hyb : y < -1.836 := by linarith [hpE.1]
      have hlm := mul_le_mul_of_nonneg_left hl.le (show 0 ≤ cStar + 1 by linarith)
      have hcoef : 2 ≤ -(cStar + 1) * y - 3 * cStar * betaE / 2 := by
        have hprod := mul_le_mul_of_nonneg_left (show 1.836 ≤ -y by linarith) (show 0 ≤ cStar + 1 by linarith)
        nlinarith only [hprod, hlm, hleq, hc]
      have hy2 : 1 ≤ y ^ 2 := by nlinarith only [hyb]
      have hmul := mul_le_mul hy2 hcoef (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg y)
      rw [contactPolynomial, abs_of_nonpos hyn.le]
      nlinarith only [hmul]
    · have hyp : 0 < y := by
        by_contra h
        have hmul := mul_nonpos_of_nonneg_of_nonpos sigmaE_pos.le (le_of_not_gt h)
        linarith [hpE.2]
      have hm := mul_le_mul_of_nonneg_right hσ hyp.le
      have hyb : 2.16 < y := by linarith [hpE.2]
      have hrm := mul_le_mul_of_nonneg_left hr.le (show 0 ≤ cStar - 1 by linarith)
      have hcoef : 1 / 2 ≤ (cStar - 1) * y - 3 * cStar * betaE / 2 := by
        have hprod := mul_le_mul_of_nonneg_left hyb.le (show 0 ≤ cStar - 1 by linarith)
        nlinarith only [hprod, hrm, hreq, hc]
      have hy2 : 4 ≤ y ^ 2 := by nlinarith only [hyb]
      have hmul := mul_le_mul hy2 hcoef (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg y)
      rw [contactPolynomial, abs_of_nonneg hyp.le]
      nlinarith only [hmul]
  rw [effectiveContactLimit_eq_polynomial]
  have hm := mul_le_mul phi0_effective_lower.le hp (by norm_num : (0 : ℝ) ≤ 2) phi0_pos.le
  nlinarith only [hm]

theorem effective_coarse_support_of_contact (y : ℝ)
    (h : 0 ≤ effectiveContactLimit y + Real.exp (-4 * appendixA)) :
    pE + sigmaE * y ∈ Icc (-1 / 2) (3 / 2) := by
  by_contra hy
  have hneg := effectiveContactLimit_negative_outside y hy
  have he : Real.exp (-4 * appendixA) < 1 / 10 := by
    have h := Real.add_one_le_exp (4 * appendixA)
    have hh : (10 : ℝ) < Real.exp (4 * appendixA) := by linarith [show (10 : ℝ) < 1 + 4 * appendixA by norm_num [appendixA]]
    rw [show -4 * appendixA = -(4 * appendixA) by ring, Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hh
  linarith only [h, hneg, he]

end BerryEsseen
