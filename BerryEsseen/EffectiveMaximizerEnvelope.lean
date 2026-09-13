import BerryEsseen.EffectiveGlobalJitter
import BerryEsseen.BoundedJitterEnvelopes

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem jitter_upper_envelope_of_uniform_error (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h ε : ℝ) (hh : 0 < h) (hβ : thirdMoment P ≤ 2)
    (hJ : ∀ y : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter h) y -
      edgeworthCDF n (signedThirdMoment P) (y / Real.sqrt (n : ℝ))| ≤ ε) (x : ℝ) :
    Real.sqrt (n : ℝ) * (normalizedSumCDF P n x - normalCDF x) ≤
      edgeworthEnvelope h (signedThirdMoment P) x + ε + edgeworthShiftConstant h / Real.sqrt (n : ℝ) := by
  let r := Real.sqrt (n : ℝ)
  letI := normalizedJitteredSumLaw_probability P n h
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hshift := edgeworthCDF_shift_remainder n hn (signedThirdMoment P) h x
    ((signedThirdMoment_abs_le P).trans hβ)
  have hsand := (actual_normalized_jitter_sandwich P n hn h hh.le x).2
  have hj := hJ (r * (x + h / (2 * r)))
  rw [mul_div_cancel_left₀ _ hr.ne'] at hj
  have hc := normalizedJitteredSumLaw_cdf P n hn h (x + h / (2 * r))
  rw [spanJitter, if_pos hh] at hc
  change cdf (normalizedJitteredSumLaw P n h) (x + h / (2 * r)) = _ at hc
  rw [← hc] at hj
  have hj' : r * (cdf (normalizedJitteredSumLaw P n h) (x + h / (2 * r)) -
      edgeworthCDF n (signedThirdMoment P) (x + h / (2 * r))) ≤ ε :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hr.le).trans hj
  rw [cdf_eq_real] at hj'
  have hscaled := mul_le_mul_of_nonneg_left hsand hr.le
  have hshift' := (abs_le.mp hshift).2
  change r * (edgeworthCDF n (signedThirdMoment P) (x + h / (2 * r)) - normalCDF x) -
    edgeworthEnvelope h (signedThirdMoment P) x ≤ edgeworthShiftConstant h / r at hshift'
  change r * (normalizedSumCDF P n x - normalCDF x) ≤ _
  dsimp only [Measure.real, r] at hj' hscaled hshift' ⊢
  nlinarith only [hj', hscaled, hshift']

theorem effective_edgeworthShiftConstant_bound (h : ℝ) (hh : h ∈ Icc 0 5) :
    edgeworthShiftConstant h ≤ 10 := by
  have hphi := phi0_lt_two_fifths
  have hh0 := hh.1
  have hh2 : h ^ 2 ≤ 25 := by nlinarith [hh.1, hh.2]
  unfold edgeworthShiftConstant
  rw [abs_of_nonneg hh.1]
  have hm := mul_le_mul_of_nonneg_right hphi.le (show 0 ≤ 3 * h ^ 2 / 8 + 3 * h by positivity)
  nlinarith only [hm, hh2, hh.2]

theorem appendix_global_envelope_budget (n : ℕ) (hn : appendixNConf ≤ n) (h : ℝ) (hh : h ∈ Icc 0 5) :
    Real.exp (-19 * appendixA) + edgeworthShiftConstant h / Real.sqrt (n : ℝ) ≤ Real.exp (-18 * appendixA) := by
  have hs := (appendix_global_sample_bounds n n hn (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)).2.1
  have hdiv := div_le_div_of_nonneg_right (effective_edgeworthShiftConstant_bound h hh) (Real.sqrt_nonneg (n : ℝ))
  have hinv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 10) (Real.exp_pos (400 * appendixA)) hs
  have h1 := exponential_relative_sixteenth 10 (400 * appendixA) (18 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth 1 (19 * appendixA) (18 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show 10 / Real.exp (400 * appendixA) = 10 * Real.exp (-(400 * appendixA)) by
    rw [Real.exp_neg, div_eq_mul_inv]] at hinv
  rw [show -(18 * appendixA) = -18 * appendixA by ring] at h1 h2
  rw [show -(19 * appendixA) = -19 * appendixA by ring] at h2
  nlinarith only [hdiv, hinv, h1, h2, Real.exp_pos (-18 * appendixA)]

theorem effective_maximizer_envelope (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (h : ℝ) (hh : h ∈ Ioc 0 5) (hβ : thirdMoment P ≤ 2)
    (hJ : ∀ y : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter h) y -
      edgeworthCDF n (signedThirdMoment P) (y / Real.sqrt (n : ℝ))| ≤ Real.exp (-19 * appendixA))
    (z : ℝ) (hpos : cE * thirdMoment P < Real.sqrt (n : ℝ) * (normalizedSumCDF P n z - normalCDF z)) :
    cE * thirdMoment P < edgeworthEnvelope h (signedThirdMoment P) z + Real.exp (-18 * appendixA) := by
  have hb := (appendix_sample_size_bounds n (appendix_conf_sample_size n hn).1).1
  have he := jitter_upper_envelope_of_uniform_error P n (by omega) h _ hh.1 hβ hJ z
  have hbudget := appendix_global_envelope_budget n hn h ⟨hh.1.le, hh.2⟩
  linarith only [hpos, he, hbudget]

end BerryEsseen
