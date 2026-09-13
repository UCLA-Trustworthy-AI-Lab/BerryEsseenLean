import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact scalar error budgets. The probabilistic estimates supplying their
inputs are deliberately not hidden in global assumptions. -/
namespace BerryEsseen

/-- The third-moment cutoff from the structural bound. -/
theorem moment_cutoff (R β c a b : ℝ) (hβ : 0 < β) (hca : a < c)
    (hR : c < R) (hstruct : R ≤ a * (β + b) / β) :
    β < a * b / (c - a) := by
  have hmul := (le_div_iff₀ hβ).1 hstruct
  apply (lt_div_iff₀ (sub_pos.2 hca)).2
  nlinarith

/-- No moment bound is assumed globally: it is applied only to violations. -/
theorem cutoff_global_bound (R β c a b K t : ℝ)
    (hβ : 0 < β) (hca : a < c) (hK : 0 ≤ K) (ht : 0 < t)
    (hstruct : R ≤ a * (β + b) / β)
    (hasym : R ≤ c + K * β / t) (hB : 0 ≤ a * b / (c - a)) :
    R ≤ c + K * (a * b / (c - a)) / t := by
  by_cases hR : R ≤ c
  · exact hR.trans (le_add_of_nonneg_right (by positivity))
  · have hcut := moment_cutoff R β c a b hβ hca (lt_of_not_ge hR) hstruct
    have hmul := mul_le_mul_of_nonneg_left hcut.le hK
    exact hasym.trans (add_le_add_right (div_le_div_of_nonneg_right hmul ht.le) c)

/-- Absorption retains a loss proportional to every positive lam, however small. -/
theorem absorb_cluster_errors (R Rb lam c q e : ℝ)
    (hlam : 0 ≤ lam) (_hq : 0 < q) (_hc : 0 < c)
    (hbudget : e ≤ c / (2 * q))
    (hcompare : R ≤ Rb - c * lam / q + lam * e) :
    R ≤ Rb - c * lam / (2 * q) := by
  have hm := mul_le_mul_of_nonneg_left hbudget hlam
  have hid : c * lam / q = 2 * (c * lam / (2 * q)) := by ring
  have hid' : lam * (c / (2 * q)) = c * lam / (2 * q) := by ring
  rw [hid'] at hm
  linarith

theorem absorb_cluster_errors_strict (R Rb lam c q e : ℝ)
    (hlam : 0 < lam) (hq : 0 < q) (hc : 0 < c)
    (hbudget : e ≤ c / (2 * q))
    (hcompare : R ≤ Rb - c * lam / q + lam * e) : R < Rb := by
  have h := absorb_cluster_errors R Rb lam c q e hlam.le hq hc hbudget hcompare
  have hgap : 0 < c * lam / (2 * q) := by positivity
  linarith

theorem central_far_uniform_gap (D : ℝ → ℝ) (central : Set ℝ)
    (Rb loss γ : ℝ)
    (hcentral : ∀ x ∈ central, D x ≤ Rb - loss)
    (hfar : ∀ x ∉ central, D x ≤ Rb - γ) :
    ∀ x, D x ≤ Rb - min loss γ := by
  intro x
  by_cases hx : x ∈ central
  · exact (hcentral x hx).trans (by linarith [min_le_left loss γ])
  · exact (hfar x hx).trans (by linarith [min_le_right loss γ])

/-- The actual small-variance numerical absorption budget in Appendix A.4.
This is exact rational arithmetic with a certified square-root bound. -/
theorem effective_small_variance_budget :
    (2 * 10 ^ 7 : ℝ) * ((10 : ℝ)⁻¹ ^ 12 + (10 : ℝ)⁻¹ ^ 24) +
      100 * (10 : ℝ)⁻¹ ^ 50 <
      (5 * (10 : ℝ)⁻¹ ^ 9) / Real.sqrt (5 * (10 : ℝ)⁻¹ ^ 12 + (10 : ℝ)⁻¹ ^ 24) := by
  let v : ℝ := 5 * (10 : ℝ)⁻¹ ^ 12 + (10 : ℝ)⁻¹ ^ 24
  have hv : 0 < v := by norm_num [v]
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hsq : Real.sqrt v < 1 / 400000 := by
    apply (Real.sqrt_lt hv.le (by norm_num : (0 : ℝ) ≤ 1 / 400000)).2
    norm_num [v]
  change _ < (5 * (10 : ℝ)⁻¹ ^ 9) / Real.sqrt v
  apply (lt_div_iff₀ hs).2
  have hleft : (2 * 10 ^ 7 : ℝ) * ((10 : ℝ)⁻¹ ^ 12 + (10 : ℝ)⁻¹ ^ 24) +
      100 * (10 : ℝ)⁻¹ ^ 50 < 1 / 40000 := by norm_num
  have hnonneg : 0 ≤ (2 * 10 ^ 7 : ℝ) * ((10 : ℝ)⁻¹ ^ 12 + (10 : ℝ)⁻¹ ^ 24) +
      100 * (10 : ℝ)⁻¹ ^ 50 := by positivity
  have hmul := mul_le_mul hleft.le hsq.le (Real.sqrt_nonneg v) (by norm_num : (0 : ℝ) ≤ 1 / 40000)
  norm_num at hmul ⊢
  linarith

end BerryEsseen
