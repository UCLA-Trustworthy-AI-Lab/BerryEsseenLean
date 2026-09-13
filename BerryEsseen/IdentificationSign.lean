import BerryEsseen.IdentificationMoments
import BerryEsseen.EffectiveMaximizerEnvelope
import BerryEsseen.EsseenEnvelopes
import BerryEsseen.PublishedNonuniform

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem edgeworthEnvelope_parameter_difference (h k h' k' z : ℝ) :
    |edgeworthEnvelope h k z - edgeworthEnvelope h' k' z| ≤ (|h - h'| / 2 + |k - k'| / 6) * phi0 := by
  have he : edgeworthEnvelope h k z - edgeworthEnvelope h' k' z = edgeworthEnvelope (h - h') (k - k') z := by
    unfold edgeworthEnvelope
    ring
  rw [he]
  exact edgeworthEnvelope_abs_bound _ _ _

theorem appendix_identification_moment_small : Real.exp (-6 * appendixA) ≤ 1 / (10 : ℝ) ^ 6 := by
  have h := exponential_sixteenth_bound ((10 : ℝ) ^ 6) (6 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(6 * appendixA) = -6 * appendixA by ring] at h
  linarith

/-- The numerical negative-sign gap printed in Appendix A. -/
theorem manuscript_esseen_negative_gap_numeric : (0.039 : ℝ) < phi0 * kappaE / 3 := by
  have hσ : sigmaE ≤ 1 / 2 := by
    nlinarith [sigmaE_sq, sigmaE_pos, pE_add_qE, sq_nonneg (pE - qE)]
  have hp : pE ≤ 0.425 := by
    unfold pE
    nlinarith [sqrt10_sq, Real.sqrt_nonneg (10 : ℝ)]
  have hk : (0.3 : ℝ) ≤ kappaE := by
    unfold kappaE
    apply (le_div_iff₀ sigmaE_pos).mpr
    linarith [pE_add_qE]
  have hm := mul_le_mul hk phi0_effective_lower.le
    (by norm_num : (0 : ℝ) ≤ 0.3989) kappaE_pos.le
  nlinarith only [hm]

theorem reflected_esseen_envelope_effective_gap (z : ℝ) :
    edgeworthEnvelope hE (-kappaE) z < cE * betaE - 0.039 := by
  have h := reflected_esseen_envelope_gap z
  nlinarith only [h, manuscript_esseen_negative_gap_numeric]

/-- The original nonuniform-bound localization of the violating threshold. -/
theorem manuscript_effective_violation_threshold_four (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (z : ℝ)
    (hpos : cE * thirdMoment P < Real.sqrt (n : ℝ) * (normalizedSumCDF P n z - normalCDF z)) :
    |z| < 4 := by
  have he : discrepancy P n z = |normalizedSumCDF P n z - normalCDF z| := by
    rw [discrepancy, normalizedSumCDF, cdf_eq_real]
    rfl
  have hraw := mul_le_mul_of_nonneg_left
    (le_abs_self (normalizedSumCDF P n z - normalCDF z)) (Real.sqrt_nonneg (n : ℝ))
  rw [← he] at hraw
  have hviol : cE < normalizedDiscrepancy P n z :=
    (lt_div_iff₀ (thirdMoment_pos P)).mpr (hpos.trans_le hraw)
  by_contra hz
  have hfar := normalizedDiscrepancy_far_bound U P n hn z 4 (by norm_num) (le_of_not_gt hz)
  norm_num at hfar
  linarith [cE_numeric_bounds.1]

/-- On |z|≤4, the exponential gap is at least z²/20, as printed. -/
theorem manuscript_gaussian_gap_on_four (z : ℝ) (hz : |z| ≤ 4) :
    z ^ 2 / 20 ≤ 1 - Real.exp (-z ^ 2 / 2) := by
  have hz2 : z ^ 2 ≤ 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg z) hz 2
    norm_num [sq_abs] at h
    exact h
  have hd : 0 < 1 + z ^ 2 / 2 := by positivity
  have he : Real.exp (-z ^ 2 / 2) ≤ 1 / (1 + z ^ 2 / 2) := by
    rw [show -z ^ 2 / 2 = -(z ^ 2 / 2) by ring, Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le hd
    linarith [Real.add_one_le_exp (z ^ 2 / 2)]
  have hrat : 1 / (1 + z ^ 2 / 2) ≤ 1 - z ^ 2 / 20 := by
    apply (div_le_iff₀ hd).mpr
    have hm := mul_nonneg (sq_nonneg z) (show 0 ≤ 18 - z ^ 2 by linarith only [hz2])
    nlinarith only [hm]
  linarith only [he, hrat]

/-- The manuscript's positive-envelope curvature estimate after |z|<4. -/
theorem manuscript_positive_esseen_envelope_quadratic_gap (z : ℝ) (hz : |z| ≤ 4) :
    z ^ 2 / 100 ≤ edgeworthEnvelope hE kappaE 0 - edgeworthEnvelope hE kappaE z := by
  have hσ : sigmaE ≤ 1 / 2 := by
    nlinarith [sigmaE_sq, sigmaE_pos, pE_add_qE, sq_nonneg (pE - qE)]
  have hh : 1 ≤ hE / 2 := by
    unfold hE
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    exact (le_div_iff₀ sigmaE_pos).mpr (by linarith only [hσ])
  have hpeak : edgeworthEnvelope hE kappaE 0 = cE * betaE := by
    simp only [edgeworthEnvelope, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one, standardNormalDensity_zero]
    exact esseen_peak_identity
  have hcoef : phi0 ≤ cE * betaE := by
    rw [← esseen_peak_identity]
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ hE / 2 + kappaE / 6 by linarith [kappaE_pos]) phi0_pos.le
    simpa only [one_mul] using hm
  have he := positive_esseen_envelope_away (|z|) z (abs_nonneg z) le_rfl
  rw [sq_abs] at he
  have hgap := manuscript_gaussian_gap_on_four z hz
  have hgap0 : 0 ≤ 1 - Real.exp (-z ^ 2 / 2) := by nlinarith only [hgap, sq_nonneg z]
  have hm := mul_nonneg (sub_nonneg.mpr hcoef) hgap0
  have hφ := mul_le_mul_of_nonneg_left hgap phi0_pos.le
  have hnum := mul_le_mul_of_nonneg_right phi0_effective_lower.le (sq_nonneg z)
  rw [hpeak]
  nlinarith only [he, hm, hφ, hnum]

theorem appendix_identification_threshold_budget : 300 * Real.exp (-6 * appendixA) ≤ Real.exp (-5 * appendixA) := by
  have h := exponential_relative_sixteenth 300 (6 * appendixA) (5 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(6 * appendixA) = -6 * appendixA by ring,
    show -(5 * appendixA) = -5 * appendixA by ring] at h
  nlinarith only [h, Real.exp_pos (-5 * appendixA)]

theorem effective_identification_sign_and_threshold (P : StandardizedLaw) (h z ε : ℝ)
    (hzfour : |z| < 4) (hε : ε ∈ ({-1, 1} : Set ℝ)) (hspan : |h - hE| ≤ Real.exp (-7 * appendixA))
    (hβ : |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA))
    (hκ : |signedThirdMoment P - ε * kappaE| ≤ Real.exp (-6 * appendixA))
    (henv : cE * thirdMoment P < edgeworthEnvelope h (signedThirdMoment P) z + Real.exp (-18 * appendixA)) :
    ε = 1 ∧ z ^ 2 ≤ Real.exp (-5 * appendixA) := by
  let δ := Real.exp (-6 * appendixA)
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδsmall : δ ≤ 1 / (10 : ℝ) ^ 6 := appendix_identification_moment_small
  have h7 : Real.exp (-7 * appendixA) ≤ δ := Real.exp_le_exp.mpr (by norm_num [appendixA])
  have h18 : Real.exp (-18 * appendixA) ≤ δ := Real.exp_le_exp.mpr (by norm_num [appendixA])
  have hd := edgeworthEnvelope_parameter_difference h (signedThirdMoment P) hE (ε * kappaE) z
  have hs : |h - hE| ≤ δ := hspan.trans h7
  have hk : |signedThirdMoment P - ε * kappaE| ≤ δ := hκ
  have hpoly : |h - hE| / 2 + |signedThirdMoment P - ε * kappaE| / 6 ≤ δ := by linarith
  have hmul := mul_le_mul hpoly phi0_lt_two_fifths.le phi0_pos.le hδ0.le
  have hd' : edgeworthEnvelope h (signedThirdMoment P) z - edgeworthEnvelope hE (ε * kappaE) z ≤ δ := by
    have hupper := (abs_le.mp hd).2
    nlinarith only [hupper, hmul, hδ0]
  have hβ' : cE * (betaE - thirdMoment P) ≤ δ := by
    have hab := (abs_le.mp hβ).1
    have hp := mul_le_mul_of_nonneg_left (show betaE - thirdMoment P ≤ δ by linarith only [hab]) cE_pos.le
    have hc := mul_le_mul_of_nonneg_right (show cE ≤ 1 by linarith [cE_numeric_bounds.2]) hδ0.le
    nlinarith only [hp, hc]
  have hperturb : cE * betaE < edgeworthEnvelope hE (ε * kappaE) z +
      2 * δ + Real.exp (-18 * appendixA) := by
    nlinarith only [henv, hd', hβ']
  have hclose : cE * betaE ≤ edgeworthEnvelope hE (ε * kappaE) z + 3 * δ := by
    linarith only [hperturb, h18]
  have hsign : ε = 1 := by
    have hcases : ε = -1 ∨ ε = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hε
    rcases hcases with hneg | hpos
    · rw [hneg, neg_one_mul] at hclose
      have hgap := reflected_esseen_envelope_effective_gap z
      nlinarith only [hclose, hgap, hδsmall]
    · exact hpos
  refine ⟨hsign, ?_⟩
  rw [hsign, one_mul] at hclose
  have hgap := manuscript_positive_esseen_envelope_quadratic_gap z hzfour.le
  have hpeak : edgeworthEnvelope hE kappaE 0 = cE * betaE := by
    simp only [edgeworthEnvelope, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one, standardNormalDensity_zero]
    exact esseen_peak_identity
  rw [hpeak] at hgap
  have hz : z ^ 2 ≤ 300 * δ := by nlinarith only [hgap, hclose]
  exact hz.trans appendix_identification_threshold_budget

end BerryEsseen
