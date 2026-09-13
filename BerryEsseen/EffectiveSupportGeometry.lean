import BerryEsseen.EffectiveContactFlatness

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- A point outside the two small clusters has an intermediate separation from
one of two actual support anchors. -/
theorem two_cluster_anchor_separation (S : Set ℝ) (ζ a b r : ℝ)
    (hζ : ζ ∈ Ioc 0 (1 / 1000)) (hS : S ⊆ Icc (-(1 / 2)) (3 / 2))
    (ha : a ∈ S) (hb : b ∈ S) (hr : r ∈ S)
    (ha0 : |a| < ζ / 10) (hb1 : |b - 1| < ζ / 10)
    (hout : r ∉ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    ∃ x ∈ S, ∃ y ∈ S, x < y ∧ 9 * ζ / 10 ≤ y - x ∧ y - x ≤ 3 / 5 := by
  have hra := hS hr
  have ha' := abs_lt.mp ha0
  have hb' := abs_lt.mp hb1
  by_cases hrhalf : r ≤ 1 / 2
  · have hout0 : r ∉ Icc (-ζ) ζ := fun h => hout (Or.inl h)
    have hs : r < -ζ ∨ ζ < r := by
      simpa only [mem_Icc, not_and_or, not_le] using hout0
    rcases hs with hleft | hright
    · refine ⟨r, hr, a, ha, ?_, ?_, ?_⟩ <;> linarith only [hleft, ha'.1, ha'.2, hζ.1, hζ.2, hra.1]
    · refine ⟨a, ha, r, hr, ?_, ?_, ?_⟩ <;> linarith only [hright, ha'.1, ha'.2, hζ.1, hζ.2, hrhalf]
  · have hout1 : r ∉ Icc (1 - ζ) (1 + ζ) := fun h => hout (Or.inr h)
    have hs : r < 1 - ζ ∨ 1 + ζ < r := by
      simpa only [mem_Icc, not_and_or, not_le] using hout1
    rcases hs with hleft | hright
    · refine ⟨r, hr, b, hb, ?_, ?_, ?_⟩ <;> linarith only [hleft, hb'.1, hb'.2, hζ.1, hζ.2, hrhalf]
    · refine ⟨b, hb, r, hr, ?_, ?_, ?_⟩ <;> linarith only [hright, hb'.1, hb'.2, hζ.1, hζ.2, hra.2]

theorem two_cluster_confinement_of_no_intermediate_pair (S : Set ℝ) (ζ a b : ℝ)
    (hζ : ζ ∈ Ioc 0 (1 / 1000)) (hS : S ⊆ Icc (-(1 / 2)) (3 / 2))
    (ha : a ∈ S) (hb : b ∈ S)
    (ha0 : |a| < ζ / 10) (hb1 : |b - 1| < ζ / 10)
    (hno : ∀ x ∈ S, ∀ y ∈ S, x < y → 9 * ζ / 10 ≤ y - x → y - x ≤ 3 / 5 → False) :
    S ⊆ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ) := by
  intro r hr
  by_contra hout
  obtain ⟨x, hx, y, hy, hxy, hl, hu⟩ := two_cluster_anchor_separation S ζ a b r hζ hS ha hb hr ha0 hb1 hout
  exact hno x hx y hy hxy hl hu

theorem two_le_hE : 2 ≤ hE := by
  have hσ : sigmaE ≤ 1 / 2 := by
    nlinarith [sigmaE_sq, sigmaE_pos, pE_add_qE, sq_nonneg (pE - qE)]
  unfold hE
  exact (le_div_iff₀ sigmaE_pos).mpr (by linarith only [hσ])

theorem identified_span_three_quarters (h : ℝ)
    (hh : |h - hE| ≤ Real.exp (-7 * appendixA)) :
    3 * hE / 5 ≤ 3 * h / 4 := by
  have he : Real.exp (-7 * appendixA) ≤ Real.exp (-6 * appendixA) :=
    Real.exp_le_exp.mpr (by norm_num [appendixA])
  have hsmall := appendix_identification_moment_small
  have hl := (abs_le.mp hh).1
  linarith only [hl, he, hsmall, two_le_hE]

theorem appendix_confinement_separation_budget (r : ℝ)
    (hr : Real.exp (400 * appendixA) ≤ r) :
    4 * Real.exp (-5 * appendixA) <
      (9 * (Real.exp (-2 * appendixA) / 2) / 10 * hE) / 3 - 10 / r := by
  have hr0 : 0 < r := (Real.exp_pos _).trans_le hr
  have hi : 1 / r ≤ Real.exp (-400 * appendixA) := by
    rw [show -400 * appendixA = -(400 * appendixA) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hr
  have h10 := exponential_relative_sixteenth 10 (400 * appendixA) (2 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h4 := exponential_relative_sixteenth 4 (5 * appendixA) (2 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  simp only [← neg_mul] at h10 h4
  have hsmall : 10 / r ≤ Real.exp (-2 * appendixA) / 16 := by
    calc
      10 / r = 10 * (1 / r) := by ring
      _ ≤ 10 * Real.exp (-400 * appendixA) := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ ≤ _ := h10
  have hh := mul_le_mul_of_nonneg_left two_le_hE (Real.exp_pos (-2 * appendixA)).le
  nlinarith only [h4, hsmall, hh, Real.exp_pos (-2 * appendixA)]

end BerryEsseen
