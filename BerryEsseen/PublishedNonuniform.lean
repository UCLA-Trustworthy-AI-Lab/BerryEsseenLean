import BerryEsseen.ClassicalBounds

/-! Published iid nonuniform Berry--Esseen bound, accepted as an explicit premise.

I. G. Shevtsova, J. Math. Sci. 248 (2020), 92--98,
DOI 10.1007/s10958-020-04858-2; author's version arXiv:2001.01123v1,
equation (1), page 1, and Table 1, page 2, iid column, delta = 1.
The table records an upper bound 17.36, attributed to the author's
2017 chapter, pp. 47--102, and the 2013 announcement, pp. 124--125.

For iid standardized summands the Lyapunov fraction is beta / sqrt n.
The right-continuous CDF form below is equivalent to the source's strict
CDF form by taking thresholds decreasing to x and using continuity of
the normal CDF and of the denominator. No manuscript-specific result
is a field, and no instance of this premise is asserted.
-/
noncomputable section
namespace BerryEsseen

structure PublishedNonuniformBound : Prop where
  bound : ∀ (P : StandardizedLaw) (n : ℕ), 1 ≤ n → ∀ x : ℝ,
    normalizedDiscrepancy P n x ≤ (17.36 : ℝ) / (1 + |x| ^ 3)

theorem normalizedDiscrepancy_far_bound (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x R : ℝ) (hR : 0 ≤ R) (hx : R ≤ |x|) :
    normalizedDiscrepancy P n x ≤ (17.36 : ℝ) / (1 + R ^ 3) := by
  exact (U.bound P n hn x).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (add_le_add_right (pow_le_pow_left₀ hR hx 3) 1))

theorem normalizedDiscrepancy_far_five (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 5 ≤ |x|) :
    normalizedDiscrepancy P n x < 0.14 := by
  have h := normalizedDiscrepancy_far_bound U P n hn x 5 (by norm_num) hx
  norm_num at h
  linarith

theorem normalizedDiscrepancy_far_four_point_nine (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 4.9 ≤ |x|) :
    normalizedDiscrepancy P n x < 0.15 := by
  have h := normalizedDiscrepancy_far_bound U P n hn x 4.9 (by norm_num) hx
  norm_num at h
  linarith

end BerryEsseen
