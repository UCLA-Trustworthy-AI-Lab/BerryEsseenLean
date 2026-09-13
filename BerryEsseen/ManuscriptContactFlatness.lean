import BerryEsseen.ManuscriptContactSaturation
import BerryEsseen.ManuscriptBinomialEffective
import BerryEsseen.GeneralJitterWidth
import BerryEsseen.EffectiveSupportGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_edgeworthCDF_unit_lipschitz (n : ℕ) (hn : 1 ≤ n) (κ : ℝ)
    (hκ : |κ| ≤ 1.84) (x y : ℝ) :
    |edgeworthCDF n κ y - edgeworthCDF n κ x| ≤ |y - x| := by
  have hbound := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (edgeworthCDF_hasDerivAt n κ t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using edgeworthDensity_effective_bound n hn κ hκ t)
    (mem_univ x) (mem_univ y)
  norm_num [Real.norm_eq_abs] at hbound
  exact hbound

theorem manuscript_edgeworthCDF_raw_lipschitz (n : ℕ) (hn : 1 ≤ n) (κ : ℝ)
    (hκ : |κ| ≤ 1.84) (x y : ℝ) :
    Real.sqrt (n : ℝ) * |edgeworthCDF n κ (y / Real.sqrt (n : ℝ)) -
      edgeworthCDF n κ (x / Real.sqrt (n : ℝ))| ≤ |y - x| := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have h := mul_le_mul_of_nonneg_left (manuscript_edgeworthCDF_unit_lipschitz n hn κ hκ
    (x / Real.sqrt (n : ℝ)) (y / Real.sqrt (n : ℝ))) hr.le
  rw [← sub_div, abs_div, abs_of_pos hr, mul_div_cancel₀ _ hr.ne'] at h
  exact h

theorem manuscript_jitter_width_transfer (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h w ε : ℝ) (hh : 0 < h) (hw : 0 < w) (hβ : thirdMoment P ≤ 1.84)
    (hJ : ∀ x : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter h) x -
      edgeworthCDF n (signedThirdMoment P) (x / Real.sqrt (n : ℝ))| ≤ ε) (x : ℝ) :
    Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter w) x -
      edgeworthCDF n (signedThirdMoment P) (x / Real.sqrt (n : ℝ))| ≤ ε + |h - w| / 2 := by
  let r := Real.sqrt (n : ℝ)
  let d := |w - h| / 2
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hs := spanJitter_width_cdf_sandwich (iidSumLaw P.measure n) h w hh.le hw.le x
  simp only [spanJitter, if_pos hh, if_pos hw] at hs
  have hsl := mul_le_mul_of_nonneg_left hs.1 hr.le
  have hsu := mul_le_mul_of_nonneg_left hs.2 hr.le
  have hlow : |r * (cdf (iidSumLaw P.measure n ∗ uniformJitter h) (x - d) -
      edgeworthCDF n (signedThirdMoment P) ((x - d) / r))| ≤ ε := by
    rw [abs_mul, abs_of_pos hr]
    exact hJ (x - d)
  have hupp : |r * (cdf (iidSumLaw P.measure n ∗ uniformJitter h) (x + d) -
      edgeworthCDF n (signedThirdMoment P) ((x + d) / r))| ≤ ε := by
    rw [abs_mul, abs_of_pos hr]
    exact hJ (x + d)
  have hgl := manuscript_edgeworthCDF_raw_lipschitz n hn (signedThirdMoment P)
    ((signedThirdMoment_abs_le P).trans hβ) x (x - d)
  have hgu := manuscript_edgeworthCDF_raw_lipschitz n hn (signedThirdMoment P)
    ((signedThirdMoment_abs_le P).trans hβ) x (x + d)
  rw [show x - d - x = -d by ring, abs_neg, abs_of_nonneg hd] at hgl
  rw [add_sub_cancel_left, abs_of_nonneg hd] at hgu
  have hgll : |r * (edgeworthCDF n (signedThirdMoment P) ((x - d) / r) -
      edgeworthCDF n (signedThirdMoment P) (x / r))| ≤ d := by
    rw [abs_mul, abs_of_pos hr]; exact hgl
  have hgul : |r * (edgeworthCDF n (signedThirdMoment P) ((x + d) / r) -
      edgeworthCDF n (signedThirdMoment P) (x / r))| ≤ d := by
    rw [abs_mul, abs_of_pos hr]; exact hgu
  have he : |h - w| / 2 = d := by dsimp only [d]; rw [abs_sub_comm h w]
  rw [he]
  change r * |_ - _| ≤ ε + d
  rw [← abs_of_pos hr, ← abs_mul, abs_le]
  constructor
  · nlinarith only [hsl, (abs_le.mp hlow).1, (abs_le.mp hgll).1]
  · nlinarith only [hsu, (abs_le.mp hupp).2, (abs_le.mp hgul).2]

theorem manuscript_esseen_half_span_shift (n : ℕ) (hn : 1 ≤ n) (κ x : ℝ)
    (hκ : |κ| ≤ 2) :
    |Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + hE / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope hE κ x| ≤ 1 / Real.sqrt (n : ℝ) := by
  have h := manuscript_edgeworthCDF_shift_remainder n hn κ hE x
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [abs_of_pos hE_pos]
  have hsq : hE ^ 2 ≤ 9 := by nlinarith [hE_le_three, hE_pos]
  have hprod := mul_le_mul hκ hE_le_three hE_pos.le (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [hsq, hprod]

theorem manuscript_identified_esseen_envelope (P : StandardizedLaw) (w δ : ℝ) (hδ : 0 ≤ δ)
    (hβ : |thirdMoment P - betaE| ≤ δ) (hκ : |signedThirdMoment P - kappaE| ≤ δ) :
    edgeworthEnvelope hE (signedThirdMoment P) w ≤ cE * thirdMoment P + δ / 2 := by
  have hdiff := edgeworthEnvelope_parameter_bound hE (signedThirdMoment P) kappaE w
  have hmul := mul_le_mul_of_nonneg_right hκ (div_pos phi0_pos (by norm_num : (0 : ℝ) < 6)).le
  have henv := positive_esseen_envelope_away 0 w (by norm_num) (abs_nonneg w)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one] at henv
  have hβ' := mul_le_mul_of_nonneg_left (abs_le.mp hβ).1 cE_pos.le
  have hc := mul_le_mul_of_nonneg_right cE_numeric_bounds.2.le hδ
  have hp := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le hδ
  have hda := (le_abs_self _).trans hdiff
  nlinarith only [hda, hmul, henv, hβ', hc, hp, hδ]

theorem manuscript_jitter_shifted_upper (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (ε u : ℝ) (hβ : thirdMoment P ≤ 2)
    (hJ : ∀ x : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter hE) x -
      edgeworthCDF n (signedThirdMoment P) (x / Real.sqrt (n : ℝ))| ≤ ε) :
    Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n ∗ uniformJitter hE) (u + hE / 2) -
      normalCDF (u / Real.sqrt (n : ℝ))) ≤
      edgeworthEnvelope hE (signedThirdMoment P) (u / Real.sqrt (n : ℝ)) + ε + 2 / Real.sqrt (n + 1 : ℝ) := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hj := hJ (u + hE / 2)
  rw [show (u + hE / 2) / Real.sqrt (n : ℝ) = u / Real.sqrt (n : ℝ) + hE / (2 * Real.sqrt (n : ℝ)) by ring] at hj
  have hj' := (mul_le_mul_of_nonneg_left (le_abs_self _) hr.le).trans hj
  have ht := (abs_le.mp (manuscript_esseen_half_span_shift n hn (signedThirdMoment P) (u / Real.sqrt (n : ℝ))
    ((signedThirdMoment_abs_le P).trans hβ))).2
  have hsbound : Real.sqrt (n + 1 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity), hr.le, hs.le]
  have hd : 1 / Real.sqrt (n : ℝ) ≤ 2 / Real.sqrt (n + 1 : ℝ) :=
    (div_le_div_iff₀ hr hs).mpr (by linarith)
  nlinarith only [hj', ht, hd]

theorem manuscript_contact_flatness_budget (n : ℕ) (hN : appendixNConf ≤ n) :
    Real.exp (-19 * appendixA) + Real.exp (-7 * appendixA) / 2 + Real.exp (-6 * appendixA) / 2 +
      2 / Real.sqrt (n : ℝ) + 200 / (n : ℝ) ≤
        4 * Real.exp (-6 * appendixA) + 1000 / Real.sqrt (n : ℝ) ∧
    4 * Real.exp (-6 * appendixA) + 1000 / Real.sqrt (n : ℝ) ≤ Real.exp (-5 * appendixA) := by
  have hn := (appendix_sample_size_bounds n (appendix_conf_sample_size n hN).1).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.one_le_sqrt.mpr hn1]
  have hi := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 200 by norm_num) hr hroot
  have he19 : Real.exp (-19 * appendixA) ≤ Real.exp (-6 * appendixA) := Real.exp_le_exp.mpr (by norm_num [appendixA])
  have he7 : Real.exp (-7 * appendixA) ≤ Real.exp (-6 * appendixA) := Real.exp_le_exp.mpr (by norm_num [appendixA])
  refine ⟨?_, ?_⟩
  · simp only [div_eq_mul_inv] at hi ⊢
    nlinarith only [he19, he7, hi, (Real.exp_pos (-6 * appendixA)).le, inv_nonneg.mpr hr.le]
  · have hceil := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
      (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hN)
    have hs : Real.exp (500 * appendixA) ≤ Real.sqrt (n : ℝ) := by
      apply (Real.le_sqrt (Real.exp_pos _).le (Nat.cast_nonneg n)).mpr
      rw [← Real.exp_nat_mul]
      convert hceil using 1 <;> ring
    have hinv : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-500 * appendixA) := by
      rw [show -500 * appendixA = -(500 * appendixA) by ring, Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) hs
    have h1 := exponential_relative_sixteenth 1000 (500 * appendixA) (5 * appendixA)
      (by norm_num [appendixA]) (by norm_num [appendixA])
    have h2 := exponential_relative_sixteenth 4 (6 * appendixA) (5 * appendixA)
      (by norm_num [appendixA]) (by norm_num [appendixA])
    simp only [← neg_mul] at h1 h2
    have hm := mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 1000 by norm_num)
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm, h1, h2, (Real.exp_pos (-5 * appendixA)).le]

theorem manuscript_extremizer_contact_flatness (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (hN : appendixNConf ≤ n + 1) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hz : (t / Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ Real.exp (-5 * appendixA))
    (h : ℝ) (hh : 0 < h) (hspan : |h - hE| ≤ Real.exp (-7 * appendixA))
    (hβ : |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA))
    (hκ : |signedThirdMoment P - kappaE| ≤ Real.exp (-6 * appendixA))
    (hJ : ∀ u : ℝ, Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter h) u -
      edgeworthCDF n (signedThirdMoment P) (u / Real.sqrt (n : ℝ))| ≤ Real.exp (-19 * appendixA))
    (y : ℝ) (hy : y ∈ P.measure.support) (hyb : |y| ≤ 6) :
    0 ≤ Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n ∗ uniformJitter hE) (t - y + hE / 2) -
      cdf (iidSumLaw P.measure n) (t - y)) ∧
    Real.sqrt (n : ℝ) * (cdf (iidSumLaw P.measure n ∗ uniformJitter hE) (t - y + hE / 2) -
      cdf (iidSumLaw P.measure n) (t - y)) ≤ 4 * Real.exp (-6 * appendixA) + 1000 / Real.sqrt (n + 1 : ℝ) ∧
    4 * Real.exp (-6 * appendixA) + 1000 / Real.sqrt (n + 1 : ℝ) ≤ Real.exp (-5 * appendixA) := by
  have hβ184 : thirdMoment P ≤ 1.84 := by
    exact ((extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)).trans momentCutoff_bounds.2).le
  have hJE (u : ℝ) : Real.sqrt (n : ℝ) * |cdf (iidSumLaw P.measure n ∗ uniformJitter hE) u -
      edgeworthCDF n (signedThirdMoment P) (u / Real.sqrt (n : ℝ))| ≤
        Real.exp (-19 * appendixA) + Real.exp (-7 * appendixA) / 2 := by
    exact (manuscript_jitter_width_transfer P n hn h hE _ hh hE_pos hβ184 hJ u).trans (by linarith only [hspan])
  have hprev := manuscript_contact_previous_discrepancy H P n hn hN t hattain hv hz y hy hyb
  have hupper := manuscript_jitter_shifted_upper P n hn _ (t - y) (hβ184.trans (by norm_num)) hJE
  have henv := manuscript_identified_esseen_envelope P ((t - y) / Real.sqrt (n : ℝ))
    (Real.exp (-6 * appendixA)) (Real.exp_pos _).le hβ hκ
  have hbudget := manuscript_contact_flatness_budget (n + 1) hN
  simp only [Nat.cast_add, Nat.cast_one] at hbudget
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (uniformJitter_cdf_between (iidSumLaw P.measure n) hE hE_pos (t - y)).1), ?_, hbudget.2⟩
  nlinarith only [hprev, hupper, henv, hbudget.1]

theorem manuscript_effective_increment_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r u d ε : ℝ) (hr : 0 ≤ r) (hε : 0 ≤ ε) (hd : 0 ≤ d) (hdh : d < hE)
    (hflat : r * (cdf (μ ∗ uniformJitter hE) (u + hE / 2) - cdf μ u) ≤ ε) :
    r * (cdf μ (u + d) - cdf μ u) ≤ hE / (hE - d) * ε := by
  have hinc := uniformJitter_controls_cdf_increment μ hE_pos u d hd hdh.le
  have hm := mul_le_mul_of_nonneg_left hinc hr
  have hb : (hE - d) / hE * (r * (cdf μ (u + d) - cdf μ u)) ≤ ε := by nlinarith only [hm, hflat]
  apply (le_of_mul_le_mul_left ?_ (sub_pos.mpr hdh))
  have hh := (div_le_iff₀ hE_pos).mp (show (hE - d) * (r * (cdf μ (u + d) - cdf μ u)) / hE ≤ ε by convert hb using 1 <;> ring)
  convert hh using 1 <;> field_simp [(sub_pos.mpr hdh).ne'] <;> ring

end BerryEsseen
