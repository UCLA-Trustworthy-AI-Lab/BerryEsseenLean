import BerryEsseen.EffectiveContactSaturation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem effective_identified_envelope_ceiling (P : StandardizedLaw) (h w : ℝ)
    (hh : |h - hE| ≤ Real.exp (-7 * appendixA))
    (hβ : |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA))
    (hκ : |signedThirdMoment P - kappaE| ≤ Real.exp (-6 * appendixA)) :
    edgeworthEnvelope h (signedThirdMoment P) w ≤ cE * thirdMoment P + Real.exp (-6 * appendixA) := by
  have he : Real.exp (-7 * appendixA) ≤ Real.exp (-6 * appendixA) := Real.exp_le_exp.mpr (by norm_num [appendixA])
  have hdiff := edgeworthEnvelope_parameter_difference h (signedThirdMoment P) hE kappaE w
  have hcoeff : |h - hE| / 2 + |signedThirdMoment P - kappaE| / 6 ≤
      (2 / 3) * Real.exp (-6 * appendixA) := by linarith only [hh, he, hκ]
  have hmul := mul_le_mul hcoeff phi0_lt_two_fifths.le phi0_pos.le
    (by positivity : 0 ≤ (2 / 3 : ℝ) * Real.exp (-6 * appendixA))
  have hdiff' := (le_abs_self _).trans (hdiff.trans hmul)
  have henv := positive_esseen_envelope_away 0 w (by norm_num) (abs_nonneg w)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one] at henv
  have hβ' := mul_le_mul_of_nonneg_left (abs_le.mp hβ).1 cE_pos.le
  have hc := mul_le_mul_of_nonneg_right cE_numeric_bounds.2.le (Real.exp_pos (-6 * appendixA)).le
  nlinarith only [hdiff', henv, hβ', hc, (Real.exp_pos (-6 * appendixA)).le]

theorem jitter_shifted_upper_from_error (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h ε u : ℝ) (hh : h ∈ Icc 0 5) (hβ : thirdMoment P ≤ 2)
    (hJ : ∀ y : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter h) y -
      edgeworthCDF n (signedThirdMoment P) (y / Real.sqrt (n : ℝ))| ≤ ε) :
    Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n ∗ uniformJitter h) (u + h / 2) -
      normalCDF (u / Real.sqrt (n : ℝ))) ≤
      edgeworthEnvelope h (signedThirdMoment P) (u / Real.sqrt (n : ℝ)) + ε + 10 / Real.sqrt (n : ℝ) := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hj := hJ (u + h / 2)
  have he : (u + h / 2) / Real.sqrt (n : ℝ) = u / Real.sqrt (n : ℝ) + h / (2 * Real.sqrt (n : ℝ)) := by ring
  rw [he] at hj
  have hj' := (mul_le_mul_of_nonneg_left (le_abs_self _) hr.le).trans hj
  have hs := (abs_le.mp (edgeworthCDF_shift_remainder n hn (signedThirdMoment P) h
    (u / Real.sqrt (n : ℝ)) ((signedThirdMoment_abs_le P).trans hβ))).2
  have hb := div_le_div_of_nonneg_right (effective_edgeworthShiftConstant_bound h hh) hr.le
  nlinarith only [hj', hs, hb]

theorem appendix_contact_flatness_budget (n : ℕ) (hn : 1 ≤ n) (hN : appendixNConf ≤ n + 1) :
    Real.exp (-6 * appendixA) + Real.exp (-19 * appendixA) +
      10 / Real.sqrt (n : ℝ) + 201 / (n + 1 : ℝ) ≤ Real.exp (-5 * appendixA) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := (appendix_global_sample_bounds (n + 1) n hN (by simp only [Nat.cast_add, Nat.cast_one]; linarith)).2.1
  have hr : 0 < Real.sqrt (n : ℝ) := (Real.exp_pos _).trans_le hs
  have hrN : Real.sqrt (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hi : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-400 * appendixA) := by
    rw [show -400 * appendixA = -(400 * appendixA) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hs
  have hiN := one_div_le_one_div_of_le hr hrN
  have h1 := exponential_relative_sixteenth 211 (400 * appendixA) (5 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth 1 (6 * appendixA) (5 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h3 := exponential_relative_sixteenth 1 (19 * appendixA) (5 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  simp only [← neg_mul, one_mul] at h1 h2 h3
  simp only [div_eq_mul_inv] at hi hiN ⊢
  nlinarith only [hi, hiN, h1, h2, h3, (Real.exp_pos (-5 * appendixA)).le]

theorem extremizer_effective_contact_flatness (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (hN : appendixNConf ≤ n + 1) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (h : ℝ) (hh : h ∈ Ioc 0 5) (hspan : |h - hE| ≤ Real.exp (-7 * appendixA))
    (hβ : |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA))
    (hκ : |signedThirdMoment P - kappaE| ≤ Real.exp (-6 * appendixA))
    (hJ : ∀ u : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter h) u -
      edgeworthCDF n (signedThirdMoment P) (u / Real.sqrt (n : ℝ))| ≤ Real.exp (-19 * appendixA))
    (y : ℝ) (hy : y ∈ P.measure.support) (hyb : |y| ≤ 6) :
    Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n ∗ uniformJitter h) (t - y + h / 2) -
      cdf (iidSumLaw P.measure n) (t - y)) ∈ Icc 0 (Real.exp (-5 * appendixA)) := by
  have hβ2 : thirdMoment P ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    linarith [momentCutoff_bounds.2]
  have hprev := contact_previous_discrepancy_effective H P n hn t hattain hv y hy hyb
  have hupper := jitter_shifted_upper_from_error P n hn h _ (t - y) ⟨hh.1.le, hh.2⟩ hβ2 hJ
  have henv := effective_identified_envelope_ceiling P h ((t - y) / Real.sqrt (n : ℝ)) hspan hβ hκ
  have hbudget := appendix_contact_flatness_budget n hn hN
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (uniformJitter_cdf_between (iidSumLaw P.measure n) h hh.1 (t - y)).1), ?_⟩
  nlinarith only [hprev, hupper, henv, hbudget]

theorem effective_contact_increment_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r h u d ε : ℝ) (hr : 0 ≤ r) (hh : 0 < h) (hε : 0 ≤ ε)
    (hd : 0 ≤ d) (hdh : d ≤ 3 * h / 4)
    (hflat : r * (cdf (μ ∗ uniformJitter h) (u + h / 2) - cdf μ u) ≤ ε) :
    r * (cdf μ (u + d) - cdf μ u) ≤ 4 * ε := by
  have hinc := uniformJitter_controls_cdf_increment μ hh u d hd (by linarith)
  have hm := mul_le_mul_of_nonneg_left hinc hr
  have hcoef : 1 / 4 ≤ (h - d) / h := (le_div_iff₀ hh).mpr (by linarith)
  have hc0 : 0 ≤ r * (cdf μ (u + d) - cdf μ u) :=
    mul_nonneg hr (sub_nonneg.mpr (monotone_cdf μ (by linarith)))
  have hb := mul_le_mul_of_nonneg_right hcoef hc0
  nlinarith only [hm, hflat, hb]

end BerryEsseen
