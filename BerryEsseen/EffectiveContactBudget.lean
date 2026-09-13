import BerryEsseen.EffectiveIdentification
import BerryEsseen.EffectiveContactGaussian
import BerryEsseen.EffectiveSupport

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem sqrtStepCorrection_effective_bound (x : ℝ) (hx : 1 ≤ x) :
    sqrtStepCorrection x ≤ 1 / 2 + 1 / (2 * x) ∧ sqrtStepCorrection x ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hi : 1 / x ≤ 1 := (div_le_one hx0).mpr hx
  have hs : 1 ≤ Real.sqrt (1 + 1 / x) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [one_div_nonneg.mpr hx0.le]
  have hb : sqrtStepCorrection x ≤ (1 + 1 / x) / 2 := by
    unfold sqrtStepCorrection
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have he : (1 + 1 / x) / 2 = 1 / 2 + 1 / (2 * x) := by field_simp
  exact ⟨by linarith only [hb, he], by linarith only [hb, hi]⟩

theorem contactRecursiveError_effective_bound (n : ℕ) (hn : 1 ≤ n)
    (hd : scaledDrop extremalConstant (n + 1) ≤ 20 / Real.sqrt (n + 1 : ℝ)) :
    contactRecursiveError n ≤ 40 / Real.sqrt (n + 1 : ℝ) := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hx0
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hr2 := Real.sq_sqrt hx0.le
  have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hr1 : 1 ≤ Real.sqrt (n : ℝ) := (Real.le_sqrt (by norm_num) hx0.le).mpr (by simpa using hx)
  have hrn : Real.sqrt (n : ℝ) ≤ n := by nlinarith only [hr2, hr1]
  have hsr : Real.sqrt (n + 1 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by nlinarith only [hr2, hs2, hx, hr.le, hs.le]
  have hc := sqrtStepCorrection_effective_bound (n : ℝ) hx
  have hmul := mul_le_mul_of_nonneg_left hc.1 cE_pos.le
  have hmul' := mul_le_mul_of_nonneg_right hc.2 (show 0 ≤ 4.75 / Real.sqrt (n : ℝ) by positivity)
  have hi : cE / (2 * (n : ℝ)) ≤ 1 / Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ)) hr).mpr
    have h := mul_le_mul_of_nonneg_right cE_numeric_bounds.2.le hr.le
    nlinarith only [h, hrn, hr.le]
  have he : contactRecursiveError n ≤ 6 / Real.sqrt (n : ℝ) + scaledDrop extremalConstant (n + 1) := by
    unfold contactRecursiveError
    simp only [div_eq_mul_inv] at hmul hmul' hi ⊢
    nlinarith only [hmul, hmul', hi, inv_nonneg.mpr hr.le]
  have hdiv : 6 / Real.sqrt (n : ℝ) ≤ 12 / Real.sqrt (n + 1 : ℝ) :=
    (div_le_div_iff₀ hr hs).mpr (by nlinarith only [hsr])
  simp only [div_eq_mul_inv] at he hdiv hd ⊢
  nlinarith only [he, hdiv, hd, inv_nonneg.mpr hs.le]

def effectiveContactLimit (y : ℝ) : ℝ :=
    phi0 / 6 * (y ^ 3 - 3 * y) - cE * |y| ^ 3 +
      3 / 2 * cE * betaE * y ^ 2 + 3 * cE * signedSecondMoment esseenLaw * y

theorem effectiveContactLimit_eq_polynomial (y : ℝ) :
    effectiveContactLimit y = -(phi0 / 6) * contactPolynomial cStar betaE y := by
  unfold effectiveContactLimit
  rw [signedSecondMoment_esseen]
  exact contact_linear_cancellation betaE y

theorem contact_polynomial_coefficient_bound (β M y : ℝ)
    (hβ : |β| ≤ 2) (hM : |M| ≤ 1) (hy : |y| ≤ 6) :
    |3 / 2 * β * y ^ 2 - |y| ^ 3 + 3 * M * y| ≤ 342 := by
  have hy2 : y ^ 2 ≤ 36 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at h
    exact h
  have hy3 : |y| ^ 3 ≤ 216 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 3
    norm_num at h
    exact h
  have hq : |3 / 2 * β * y ^ 2| ≤ 108 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y)]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have h := mul_le_mul hβ hy2 (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [h]
  have hl : |3 * M * y| ≤ 18 := by
    rw [abs_mul, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h := mul_le_mul hM hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h]
  have ht := (abs_add_le (3 / 2 * β * y ^ 2 - |y| ^ 3) (3 * M * y)).trans
    (add_le_add (abs_sub (3 / 2 * β * y ^ 2) (|y| ^ 3)) le_rfl)
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg y) 3)] at ht
  linarith only [ht, hq, hl, hy3]

theorem contact_polynomial_parameter_error (R β M y δ : ℝ) (hδ : 0 ≤ δ)
    (hβ : |β| ≤ 2) (hM : |M| ≤ 1) (hy : |y| ≤ 6)
    (hβE : |β - betaE| ≤ δ) (hME : |M - signedSecondMoment esseenLaw| ≤ δ) :
    |(3 / 2 * R * β * y ^ 2 - R * |y| ^ 3 + 3 * R * M * y) -
      (3 / 2 * cE * betaE * y ^ 2 - cE * |y| ^ 3 + 3 * cE * signedSecondMoment esseenLaw * y)| ≤
      342 * |R - cE| + 36 * δ := by
  have hy2 : y ^ 2 ≤ 36 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at h
    exact h
  have he : (3 / 2 * R * β * y ^ 2 - R * |y| ^ 3 + 3 * R * M * y) -
      (3 / 2 * cE * betaE * y ^ 2 - cE * |y| ^ 3 + 3 * cE * signedSecondMoment esseenLaw * y) =
      (R - cE) * (3 / 2 * β * y ^ 2 - |y| ^ 3 + 3 * M * y) +
      cE * (3 / 2 * (β - betaE) * y ^ 2 + 3 * (M - signedSecondMoment esseenLaw) * y) := by ring
  have hfirst : |(R - cE) * (3 / 2 * β * y ^ 2 - |y| ^ 3 + 3 * M * y)| ≤ 342 * |R - cE| := by
    rw [abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left (contact_polynomial_coefficient_bound β M y hβ hM hy) (abs_nonneg (R - cE))]
  have hq : |3 / 2 * (β - betaE) * y ^ 2| ≤ 54 * δ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y)]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have h := mul_le_mul hβE hy2 (sq_nonneg y) hδ
    nlinarith only [h]
  have hl : |3 * (M - signedSecondMoment esseenLaw) * y| ≤ 18 * δ := by
    rw [abs_mul, abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h := mul_le_mul hME hy (abs_nonneg y) hδ
    nlinarith only [h]
  have hinner := (abs_add_le (3 / 2 * (β - betaE) * y ^ 2) (3 * (M - signedSecondMoment esseenLaw) * y)).trans (add_le_add hq hl)
  have hsecond : |cE * (3 / 2 * (β - betaE) * y ^ 2 + 3 * (M - signedSecondMoment esseenLaw) * y)| ≤ 36 * δ := by
    rw [abs_mul, abs_of_pos cE_pos]
    have hc : cE ≤ 1 / 2 := by linarith [cE_numeric_bounds.2]
    have h := mul_le_mul hc hinner (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [h]
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

theorem extremizer_effective_contact_polynomial (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hd : scaledDrop extremalConstant (n + 1) ≤ 20 / Real.sqrt (n + 1 : ℝ))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hβE : |thirdMoment P - betaE| ≤ δ)
    (hME : |signedSecondMoment P - signedSecondMoment esseenLaw| ≤ δ)
    (y : ℝ) (hy : y ∈ P.measure.support) (hyb : |y| ≤ 6) :
    0 ≤ effectiveContactLimit y + 4000 / Real.sqrt (n + 1 : ℝ) +
      1000 * (δ + (t / Real.sqrt (n + 1 : ℝ)) ^ 2) := by
  have hr : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hβ : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hrec := mul_le_mul_of_nonneg_left (contactRecursiveError_effective_bound n hn hd) (thirdMoment_pos P).le
  have hrec' := mul_le_mul_of_nonneg_right hβ (show 0 ≤ 40 / Real.sqrt (n + 1 : ℝ) by positivity)
  have hR : |extremalConstant (n + 1) - cE| ≤ 4.75 / Real.sqrt (n + 1 : ℝ) := by
    rw [abs_of_pos (sub_pos.mpr hv)]
    have h := (extremalConstant_bounds H (n + 1) (by omega)).2
    simp only [Nat.cast_add, Nat.cast_one] at h
    linarith only [h]
  have herr := contact_polynomial_parameter_error (extremalConstant (n + 1))
    (thirdMoment P) (signedSecondMoment P) y δ hδ (by rwa [abs_of_pos (thirdMoment_pos P)])
    (signedSecondMoment_abs_le_one P) hyb hβE hME
  have herr' := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 342)
  have hG := gaussianHn_effective_local_remainder (n + 1) (by omega)
    (t / Real.sqrt (n + 1 : ℝ)) y hyb
  simp only [gaussianHn, Nat.cast_add, Nat.cast_one] at hG
  have hGa := (le_abs_self _).trans hG
  have hpa := (le_abs_self _).trans herr
  have hc := extremizer_sharp_contact_bound H P n hn t hattain hv y hy
  unfold effectiveContactLimit
  simp only [div_eq_mul_inv] at hrec hrec' herr' hGa hc hpa ⊢
  nlinarith only [hc, hpa, herr', hGa, hrec, hrec', hδ,
    sq_nonneg (t * (Real.sqrt (n + 1 : ℝ))⁻¹), inv_nonneg.mpr hr.le]

theorem appendix_contact_polynomial_budget (n : ℕ) (hn : appendixNConf ≤ n)
    (z : ℝ) (hz : z ^ 2 ≤ Real.exp (-5 * appendixA)) :
    4000 / Real.sqrt (n : ℝ) + 1000 * (Real.exp (-6 * appendixA) + z ^ 2) ≤
      Real.exp (-4 * appendixA) := by
  have hr := (appendix_global_sample_bounds n n hn (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)).2.1
  have hr0 := (Real.exp_pos (400 * appendixA)).trans_le hr
  have hi : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-400 * appendixA) := by
    rw [show -400 * appendixA = -(400 * appendixA) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hr
  have h1 := exponential_relative_sixteenth 4000 (400 * appendixA) (4 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth 1000 (6 * appendixA) (4 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h3 := exponential_relative_sixteenth 1000 (5 * appendixA) (4 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  simp only [← neg_mul] at h1 h2 h3
  have him := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 4000)
  simp only [div_eq_mul_inv] at him ⊢
  nlinarith only [h1, h2, h3, him, hz, (Real.exp_pos (-4 * appendixA)).le]

end BerryEsseen
