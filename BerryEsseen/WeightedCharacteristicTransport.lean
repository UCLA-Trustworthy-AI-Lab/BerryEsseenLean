import BerryEsseen.ComplexWasserstein
import BerryEsseen.CharacteristicConditioning

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem complex_product_difference (a b c d : ℂ) :
    ‖a * c - b * d‖ ≤ ‖a - b‖ * ‖c‖ + ‖b‖ * ‖c - d‖ := by
  have he : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [he]
  simpa only [norm_mul] using norm_add_le ((a - b) * c) (b * (c - d))

theorem weighted_phase_difference (k : ℕ) (u x y : ℝ) :
    ‖(x : ℂ) ^ k * realPhase u x - (y : ℂ) ^ k * realPhase u y‖ ≤
      |x ^ k - y ^ k| + |y| ^ k * |u| * |x - y| := by
  have h := complex_product_difference ((x : ℂ) ^ k) ((y : ℂ) ^ k) (realPhase u x) (realPhase u y)
  have he : ‖(x : ℂ) ^ k - (y : ℂ) ^ k‖ = |x ^ k - y ^ k| := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [he, realPhase_norm, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs] at h
  have hm := mul_le_mul_of_nonneg_left (realPhase_spatial_difference u x y) (pow_nonneg (abs_nonneg y) k)
  nlinarith only [h, hm]

theorem bounded_weightedCharFun_transport (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 < L) (k : ℕ)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ x ∂ν, |x| ≤ R)
    (hpoly : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |x ^ k - y ^ k| ≤ L * |x - y|)
    (u : ℝ) :
    ‖weightedCharFun μ k u - weightedCharFun ν k u‖ ≤
      (L + R ^ k * |u|) * wassersteinOne μ ν := by
  have hC : 0 < L + R ^ k * |u| := lt_of_lt_of_le hL (le_add_of_nonneg_right (by positivity))
  apply (bounded_complex_lipschitz_integral_transport K μ ν R (L + R ^ k * |u|) hR hC hμ hν
    (fun x => (x : ℂ) ^ k * realPhase u x) (by unfold realPhase; fun_prop) ?_).2.2
  intro x y hx hy
  have hp := hpoly x y hx hy
  have hphase := weighted_phase_difference k u x y
  have hyk := pow_le_pow_left₀ (abs_nonneg y) hy k
  have hmul := mul_le_mul_of_nonneg_right hyk (mul_nonneg (abs_nonneg u) (abs_nonneg (x - y)))
  nlinarith only [hp, hphase, hmul]

theorem weighted_characteristic_transport_thirteen (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (hν : ∀ᵐ x ∂ν, |x| ≤ 13) (u : ℝ) :
    ‖charFun μ u - charFun ν u‖ ≤ (1 + |u|) * wassersteinOne μ ν ∧
      ‖weightedCharFun μ 1 u - weightedCharFun ν 1 u‖ ≤ (1 + 13 * |u|) * wassersteinOne μ ν ∧
      ‖weightedCharFun μ 2 u - weightedCharFun ν 2 u‖ ≤ (26 + 169 * |u|) * wassersteinOne μ ν := by
  constructor
  · have h := bounded_weightedCharFun_transport K μ ν 13 1 (by norm_num) (by norm_num) 0 hμ hν (by
      intro x y hx hy
      simp) u
    simpa only [weightedCharFun_zero, pow_zero, one_mul] using h
  constructor
  · have h := bounded_weightedCharFun_transport K μ ν 13 1 (by norm_num) (by norm_num) 1 hμ hν (by
      intro x y hx hy
      simp) u
    simpa only [pow_one] using h
  · have h := bounded_weightedCharFun_transport K μ ν 13 26 (by norm_num) (by norm_num) 2 hμ hν (by
      intro x y hx hy
      convert square_difference_bounded 13 x y (by norm_num) hx hy using 1 <;> norm_num) u
    norm_num only [show (13 : ℝ) ^ 2 = 169 by norm_num] at h
    exact h

end BerryEsseen
