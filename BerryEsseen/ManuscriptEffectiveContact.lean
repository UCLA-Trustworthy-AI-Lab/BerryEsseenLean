import BerryEsseen.ManuscriptGaussianCancellation
import BerryEsseen.EffectiveContactBudget

/-! The manuscript's four-row contact budget, with the original
100, 3*d+2/n, 1625, 36 and 2000 constants. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_sqrt_step_bounds (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ sqrtStepCorrection x - 1 / 2 ∧
      sqrtStepCorrection x - 1 / 2 ≤ 2 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hi : 0 ≤ 1 / x := by positivity
  have hs : 1 ≤ Real.sqrt (1 + 1 / x) := Real.one_le_sqrt.mpr (by linarith)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 + 1 / x by positivity)
  have hden : 0 < Real.sqrt (1 + 1 / x) + 1 := by positivity
  have hlo : (1 / 2 : ℝ) ≤ sqrtStepCorrection x := by
    unfold sqrtStepCorrection
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hs, hs2, sq_nonneg (Real.sqrt (1 + 1 / x) - 1)]
  have hu := (sqrtStepCorrection_effective_bound x hx).1
  have hb : 1 / (2 * x) ≤ 2 / (x + 1) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * x) (by positivity : 0 < x + 1)).mpr
    linarith
  exact ⟨by linarith, by linarith⟩

theorem manuscript_sqrt_predecessor_correction (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (n + 1 : ℝ) * (Real.sqrt ((n + 1 : ℝ) / (n : ℝ)) - 1) - 1 / 2 ∧
    (n + 1 : ℝ) * (Real.sqrt ((n + 1 : ℝ) / (n : ℝ)) - 1) - 1 / 2 ≤
      2 / (n + 1 : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hi := sqrt_step_correction_identity (n : ℝ) hn0
  have he : (n + 1 : ℝ) * (Real.sqrt ((n + 1 : ℝ) / (n : ℝ)) - 1) =
      sqrtStepCorrection (n : ℝ) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ (n + 1 : ℝ))]
    have hr : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    apply (mul_right_cancel₀ hr)
    have hh := congrArg (fun a : ℝ => a * Real.sqrt (n : ℝ)) hi
    field_simp [hr] at hh ⊢
    linear_combination hh - Real.sqrt (n + 1 : ℝ) * hs
  rw [he]
  exact manuscript_sqrt_step_bounds n (by exact_mod_cast hn)

theorem manuscript_contact_recursive_budget (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (hβ : thirdMoment P ≤ 2) (hR : 0 ≤ extremalConstant (n + 1)) :
    thirdMoment P * (Real.sqrt (n + 1 : ℝ) ^ 3 / Real.sqrt (n : ℝ) * extremalConstant n -
      (n + 1 : ℝ) * extremalConstant (n + 1) - extremalConstant (n + 1) / 2) ≤
      3 * scaledDrop extremalConstant (n + 1) + 2 / (n + 1 : ℝ) := by
  let R := extremalConstant (n + 1)
  let d := scaledDrop extremalConstant (n + 1)
  let a := (n + 1 : ℝ) + sqrtStepCorrection (n : ℝ)
  let m := max (extremalConstant n - R) 0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN : (0 : ℝ) < n + 1 := by positivity
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    linarith [sqrtStepCorrection_nonneg (n : ℝ) hn0]
  have ha : a ≤ (3 / 2 : ℝ) * (n + 1 : ℝ) := by
    have h := (sqrtStepCorrection_effective_bound (n : ℝ) hnR).2
    dsimp only [a]
    linarith
  have hm : 0 ≤ m := le_max_right _ _
  have hd : 0 ≤ d := scaledDrop_nonneg _ _
  have hdeq : (n + 1 : ℝ) * m = d := by
    simp only [m, d, R, scaledDrop, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hdiff : a * (extremalConstant n - R) ≤ (3 / 2 : ℝ) * d := by
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (extremalConstant n - R) 0) ha0
    have h2 := mul_le_mul_of_nonneg_right ha hm
    change a * (extremalConstant n - R) ≤ a * m at h1
    rw [show (3 / 2 : ℝ) * (n + 1 : ℝ) * m = (3 / 2 : ℝ) * d by rw [mul_assoc, hdeq]] at h2
    exact h1.trans h2
  have hβpos := (thirdMoment_pos P).le
  have hprod : thirdMoment P * R ≤ 1 := by
    have hRb : R ≤ 0.4690 := (extremalConstant_bounds H (n + 1) (by omega)).1
    have h := mul_le_mul hβ hRb hR (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h]
  have hs := manuscript_sqrt_step_bounds (n : ℝ) hnR
  have hsmall : thirdMoment P * R * (sqrtStepCorrection (n : ℝ) - 1 / 2) ≤
      2 / (n + 1 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hprod hs.1
    nlinarith only [h1, hs.2]
  have hlarge := mul_le_mul_of_nonneg_left hdiff hβpos
  have hβd := mul_le_mul_of_nonneg_right hβ hd
  rw [sqrt_step_correction_identity (n : ℝ) hn0]
  change thirdMoment P * (a * extremalConstant n - (n + 1 : ℝ) * R - R / 2) ≤ 3 * d + _
  dsimp only [a] at hlarge ⊢
  nlinarith only [hsmall, hlarge, hβd]

theorem manuscript_extremizer_contact_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (y : ℝ) (hy : y ∈ P.measure.support) :
    0 ≤ gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y +
      3 * scaledDrop extremalConstant (n + 1) + 2 / (n + 1 : ℝ) +
      3 / 2 * extremalConstant (n + 1) * thirdMoment P * y ^ 2 -
      extremalConstant (n + 1) * |y| ^ 3 +
      3 * extremalConstant (n + 1) * signedSecondMoment P * y := by
  have hp : 0 ≤ signedRatio P n t := by rw [hattain]; exact cE_pos.le.trans hv.le
  have hc := influence_contact_at_extremizer H P n t hattain hp y hy
  have hb := influenceNumerator_gaussian_bound H P n hn t y
  rw [hc, hattain] at hb
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hr := manuscript_contact_recursive_budget H P n hn hβ (cE_pos.le.trans hv.le)
  nlinarith only [hb, hr]

theorem manuscript_extremizer_effective_contact_polynomial (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hd : scaledDrop extremalConstant (n + 1) ≤ 20 / Real.sqrt (n + 1 : ℝ))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hβE : |thirdMoment P - betaE| ≤ δ)
    (hME : |signedSecondMoment P - signedSecondMoment esseenLaw| ≤ δ)
    (y : ℝ) (hy : y ∈ P.measure.support) (hyb : |y| ≤ 6) :
    0 ≤ effectiveContactLimit y + 2000 / Real.sqrt (n + 1 : ℝ) +
      1000 * (δ + (t / Real.sqrt (n + 1 : ℝ)) ^ 2) := by
  have hr : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hR : |extremalConstant (n + 1) - cE| ≤ 4.75 / Real.sqrt (n + 1 : ℝ) := by
    rw [abs_of_pos (sub_pos.mpr hv)]
    have h := (extremalConstant_bounds H (n + 1) (by omega)).2
    simp only [Nat.cast_add, Nat.cast_one] at h
    linarith only [h]
  have herr := contact_polynomial_parameter_error (extremalConstant (n + 1))
    (thirdMoment P) (signedSecondMoment P) y δ hδ (by rwa [abs_of_pos (thirdMoment_pos P)])
    (signedSecondMoment_abs_le_one P) hyb hβE hME
  have herr' := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 342)
  have hG := manuscript_gaussianHn_effective_local_remainder (n + 1) (by omega)
    (t / Real.sqrt (n + 1 : ℝ)) y hyb
  simp only [gaussianHn, Nat.cast_add, Nat.cast_one] at hG
  have hGa := (le_abs_self _).trans hG
  have hpa := (le_abs_self _).trans herr
  have hc := manuscript_extremizer_contact_bound H P n hn t hattain hv y hy
  have hroot : Real.sqrt (n + 1 : ℝ) ≤ (n + 1 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
    have hr1 : 1 ≤ Real.sqrt (n + 1 : ℝ) := Real.one_le_sqrt.mpr (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
    nlinarith only [hs, hr1]
  have hi : 2 / (n + 1 : ℝ) ≤ 2 / Real.sqrt (n + 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hr hroot
  unfold effectiveContactLimit
  simp only [div_eq_mul_inv] at hd herr' hGa hc hpa hi ⊢
  nlinarith only [hc, hpa, herr', hGa, hd, hi, hδ,
    sq_nonneg (t * (Real.sqrt (n + 1 : ℝ))⁻¹), inv_nonneg.mpr hr.le]

theorem manuscript_appendix_contact_polynomial_budget (n : ℕ) (hn : appendixNConf ≤ n)
    (z : ℝ) (hz : z ^ 2 ≤ Real.exp (-5 * appendixA)) :
    2000 / Real.sqrt (n : ℝ) + 1000 * (Real.exp (-6 * appendixA) + z ^ 2) ≤
      Real.exp (-4 * appendixA) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hceil := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have hr : Real.exp (500 * appendixA) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (Real.exp_pos _).le hn0).mpr
    rw [← Real.exp_nat_mul]
    convert hceil using 1 <;> ring
  have hi : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-500 * appendixA) := by
    rw [show -500 * appendixA = -(500 * appendixA) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hr
  have h1 := exponential_relative_sixteenth 2000 (500 * appendixA) (4 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth 1000 (6 * appendixA) (4 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h3 := exponential_relative_sixteenth 1000 (5 * appendixA) (4 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  simp only [← neg_mul] at h1 h2 h3
  have him := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2000)
  simp only [div_eq_mul_inv] at him ⊢
  nlinarith only [h1, h2, h3, him, hz, (Real.exp_pos (-4 * appendixA)).le]

end BerryEsseen
