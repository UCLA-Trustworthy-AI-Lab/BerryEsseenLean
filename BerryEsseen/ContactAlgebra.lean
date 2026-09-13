import BerryEsseen.Constants

/-! Algebraic consequences of the contamination identity.
The differentiation and probabilistic support-contact theorem itself are
not asserted here. Each input inequality is explicit in the theorem type. -/
noncomputable section
namespace BerryEsseen

def contactPolynomial (c β y : ℝ) : ℝ :=
  c * |y| ^ 3 - y ^ 3 - (3 / 2) * c * β * y ^ 2

theorem contact_linear_cancellation (β y : ℝ) :
    phi0 / 6 * (y ^ 3 - 3 * y) - cE * |y| ^ 3 +
      (3 / 2) * cE * β * y ^ 2 + 3 * cE * (qE - pE) * y =
    -(phi0 / 6) * contactPolynomial cStar β y := by
  rw [cE_eq]
  have hm := signed_moment_identity
  unfold contactPolynomial
  linear_combination phi0 * y / 2 * hm

theorem contact_polynomial_of_limit (β y : ℝ)
    (h : 0 ≤ phi0 / 6 * (y ^ 3 - 3 * y) - cE * |y| ^ 3 +
      (3 / 2) * cE * β * y ^ 2 + 3 * cE * (qE - pE) * y) :
    contactPolynomial cStar β y ≤ 0 := by
  rw [contact_linear_cancellation] at h
  have hp := phi0_pos
  nlinarith

theorem contact_polynomial_interval (c β y : ℝ) (hc : 1 < c) (hβ : 0 ≤ β)
    (h : contactPolynomial c β y ≤ 0) :
    -(3 * c * β / (2 * (c + 1))) ≤ y ∧ y ≤ 3 * c * β / (2 * (c - 1)) := by
  have hcp : 0 < c := by linarith
  have hleft : 0 ≤ 3 * c * β / (2 * (c + 1)) := by positivity
  have hcm : 0 < c - 1 := by linarith
  have hright : 0 ≤ 3 * c * β / (2 * (c - 1)) := by positivity
  by_cases hy : y = 0
  · subst y; constructor <;> linarith
  have hysq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  rcases le_total 0 y with hypos | hyneg
  · have hf : contactPolynomial c β y = y ^ 2 * ((c - 1) * y - 3 * c * β / 2) := by
      simp only [contactPolynomial, abs_of_nonneg hypos]
      ring
    rw [hf] at h
    have hlin : (c - 1) * y - 3 * c * β / 2 ≤ 0 :=
      le_of_not_gt (fun hp => not_lt_of_ge h (mul_pos hysq hp))
    refine ⟨by linarith, (le_div_iff₀ (by linarith : 0 < 2 * (c - 1))).2 ?_⟩
    nlinarith
  · have hf : contactPolynomial c β y = y ^ 2 * (-(c + 1) * y - 3 * c * β / 2) := by
      simp only [contactPolynomial, abs_of_nonpos hyneg]
      ring
    rw [hf] at h
    have hlin : -(c + 1) * y - 3 * c * β / 2 ≤ 0 :=
      le_of_not_gt (fun hp => not_lt_of_ge h (mul_pos hysq hp))
    refine ⟨?_, by linarith⟩
    have hb : -y ≤ 3 * c * β / (2 * (c + 1)) :=
      (le_div_iff₀ (by linarith : 0 < 2 * (c + 1))).2 (by nlinarith)
    linarith

/-- The explicit cubic support certificate in Appendix A.1. -/
theorem effective_support_cubic_negative (r d : ℝ) (hr : 6 ≤ r) (hd : d ≤ 1) :
    -(r ^ 3) / 3 + 3 * r ^ 2 / 2 + 17 * r / 10 + 3 / 2 + 2 * d < 0 := by
  have h1 : 0 ≤ r - 6 := by linarith
  have h2 : 0 ≤ (r - 6) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (r - 6) ^ 3 := pow_nonneg h1 _
  nlinarith

theorem support_bound_of_contact (S : Set ℝ) (I : ℝ → ℝ) (β d : ℝ)
    (hd : d ≤ 1)
    (hcontact : ∀ y ∈ S, I y = 0)
    (hbound : ∀ y, β * I y ≤ -(|y| ^ 3) / 3 + 3 * |y| ^ 2 / 2 +
      17 * |y| / 10 + 3 / 2 + 2 * d) :
    S ⊆ Set.Ioo (-6) 6 := by
  intro y hy
  have hb := hbound y
  rw [hcontact y hy, mul_zero] at hb
  have habs : |y| < 6 := by
    by_contra hn
    have hneg := effective_support_cubic_negative |y| d (le_of_not_gt hn) hd
    linarith
  exact abs_lt.1 habs

end BerryEsseen
