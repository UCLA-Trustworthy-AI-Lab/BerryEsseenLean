import BerryEsseen.EffectiveClusterEnvelope

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Conditional cubic expansion followed by normalization, with the manuscript's 100s budget. -/
theorem manuscript_cubic_normalization_error (σ b s m τ : ℝ)
    (hσ : σ ∈ Icc 0.48 0.51) (hb : b ∈ Icc 0.48 (1 / 2))
    (hs : 0 ≤ s) (hscale : σ ^ 2 = b ^ 2 + s)
    (hτ : |τ| ≤ 1) (hm : |m - b ^ 2 * τ| ≤ 4 * s) :
    |m / σ ^ 3 - τ / b| ≤ 100 * s := by
  have hσ0 : 0 < σ := by linarith [hσ.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hdiff0 : 0 ≤ σ - b := by nlinarith only [hscale, hs, hσ0, hb0]
  have hdiff : σ - b ≤ 2 * s := by
    have he : (σ - b) * (σ + b) = s := by nlinarith only [hscale]
    have hp := mul_nonneg hdiff0 (show 0 ≤ σ + b - 1 / 2 by linarith [hσ.1, hb.1])
    nlinarith only [he, hp]
  have hσ2 : σ ^ 2 ≤ 0.51 ^ 2 := by nlinarith only [hσ.2, hσ0]
  have hb2 : b ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith only [hb.2, hb0]
  have hσb := mul_le_mul hσ.2 hb.2 hb0.le (by norm_num : (0 : ℝ) ≤ 0.51)
  have hpoly : σ ^ 2 + σ * b + b ^ 2 ≤ 1 := by nlinarith only [hσ2, hb2, hσb]
  have hcub : 0 ≤ σ ^ 3 - b ^ 3 ∧ σ ^ 3 - b ^ 3 ≤ 2 * s := by
    have hid : σ ^ 3 - b ^ 3 = (σ - b) * (σ ^ 2 + σ * b + b ^ 2) := by ring
    rw [hid]
    constructor
    · positivity
    · exact (mul_le_mul_of_nonneg_left hpoly hdiff0).trans (by simpa only [mul_one] using hdiff)
  have hnum : |b * m - τ * σ ^ 3| ≤ 4 * s := by
    have he : b * m - τ * σ ^ 3 = b * (m - b ^ 2 * τ) - τ * (σ ^ 3 - b ^ 3) := by ring
    rw [he]
    have htri := abs_sub (b * (m - b ^ 2 * τ)) (τ * (σ ^ 3 - b ^ 3))
    rw [abs_mul, abs_mul, abs_of_pos hb0, abs_of_nonneg hcub.1] at htri
    have hm1 := mul_le_mul hb.2 hm (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hm2 := mul_le_mul hτ hcub.2 hcub.1 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [htri, hm1, hm2]
  have hσ3 : (0.11 : ℝ) ≤ σ ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.48) hσ.1 3
    norm_num at hp
    linarith only [hp]
  have hden := mul_le_mul hb.1 hσ3 (by norm_num : (0 : ℝ) ≤ 0.11) hb0.le
  have hden' := mul_le_mul_of_nonneg_right hden hs
  have he : m / σ ^ 3 - τ / b = (b * m - τ * σ ^ 3) / (b * σ ^ 3) := by field_simp <;> ring
  rw [he, abs_div, abs_of_pos (mul_pos hb0 (pow_pos hσ0 3))]
  apply (div_le_iff₀ (mul_pos hb0 (pow_pos hσ0 3))).mpr
  nlinarith only [hnum, hden', hs]

theorem manuscript_cluster_normalized_cubic_errors (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    |thirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) -
      (p ^ 2 + (1 - p) ^ 2) / Real.sqrt (p * (1 - p))| ≤ 100 * averageNoiseVariance P Q p ∧
    |signedThirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) -
      (1 - 2 * p) / Real.sqrt (p * (1 - p))| ≤ 100 * averageNoiseVariance P Q p := by
  let σ := Real.sqrt (clusterVariance P Q p)
  let b := Real.sqrt (p * (1 - p))
  let s := averageNoiseVariance P Q p
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hs : 0 ≤ s := averageNoiseVariance_nonneg P Q p hpcc
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp01)
  have hσ2 := Real.sq_sqrt (clusterVariance_pos P Q p hp01).le
  have hb2 := Real.sq_sqrt (mul_nonneg hpcc.1 (sub_nonneg.mpr hpcc.2))
  have hσb := effective_cluster_scale_bounds P Q p ε hp hε hP hQ
  have hσ : σ ∈ Icc 0.48 0.51 := by
    refine ⟨hσb.1.1, ?_⟩
    have hv := effective_cluster_variance_bounds P Q p ε hp hε hP hQ
    change σ ^ 2 = _ at hσ2
    nlinarith only [hσ2, hv.2, hσ0]
  have hb : b ∈ Icc 0.48 (1 / 2) :=
    ⟨(effective_binomial_parameters p hp).2.1, (effective_binomial_parameters p hp).2.2.1⟩
  have hscale : σ ^ 2 = b ^ 2 + s := by
    dsimp [σ, b, s]
    rw [hσ2, hb2]
    unfold clusterVariance averageNoiseVariance
    ring
  have hτ : |p ^ 2 + (1 - p) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hpcc.1 (sub_nonneg.mpr hpcc.2)]
  have hd : |1 - 2 * p| ≤ 1 := abs_le.mpr ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hεs := mul_le_mul_of_nonneg_right hε.2 hs
  have hρ := twoCluster_abs_third_error P Q p ε hpcc (by linarith [hε.2, hp.1]) (by linarith [hε.2, hp.2]) hP hQ
  have hγ := clusterSignedThirdMoment_error P Q p ε hpcc hP hQ
  have hρ' : |clusterThirdAbsoluteMoment P Q p - b ^ 2 * (p ^ 2 + (1 - p) ^ 2)| ≤ 4 * s := by
    dsimp [b]
    rw [hb2]
    change |clusterThirdAbsoluteMoment P Q p - p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)| ≤ (3 + ε) * s at hρ
    nlinarith only [hρ, hεs, hs]
  have hγ' : |clusterSignedThirdMoment P Q p - b ^ 2 * (1 - 2 * p)| ≤ 4 * s := by
    dsimp [b]
    rw [hb2]
    change _ ≤ (3 + ε) * s at hγ
    nlinarith only [hγ, hεs, hs]
  rw [standardizedTwoClusterLaw_third, standardizedTwoCluster_signed_third]
  exact ⟨manuscript_cubic_normalization_error σ b s _ _ hσ hb hs hscale hτ hρ',
    manuscript_cubic_normalization_error σ b s _ _ hσ hb hs hscale hd hγ'⟩

theorem manuscript_cluster_envelope_comparison (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    phi0 * (1 / (2 * Real.sqrt (clusterVariance P Q p)) +
      |signedThirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1)| / 6) ≤
      phi0 * (3 + 1 - 2 * p) / (6 * Real.sqrt (p * (1 - p))) + 7 * averageNoiseVariance P Q p ∧
    phi0 * (3 + 1 - 2 * p) / (6 * Real.sqrt (p * (1 - p))) ≤
      cE * ((p ^ 2 + (1 - p) ^ 2) / Real.sqrt (p * (1 - p))) := by
  let σ := Real.sqrt (clusterVariance P Q p)
  let b := Real.sqrt (p * (1 - p))
  let s := averageNoiseVariance P Q p
  let γ := signedThirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1)
  have hp01 := (effective_binomial_parameters p hp).1
  have hs : 0 ≤ s := averageNoiseVariance_nonneg P Q p ⟨hp01.1.le, hp01.2.le⟩
  have hb0 : 0 < b := Real.sqrt_pos.mpr (mul_pos hp01.1 (sub_pos.mpr hp01.2))
  have hbσ : b ≤ σ := by
    apply Real.sqrt_le_sqrt
    have he : clusterVariance P Q p = p * (1 - p) + s := by unfold clusterVariance s averageNoiseVariance; ring
    rw [he]
    linarith only [hs]
  have hscale := one_div_le_one_div_of_le (mul_pos (show (0 : ℝ) < 2 by norm_num) hb0)
    (mul_le_mul_of_nonneg_left hbσ (by norm_num : (0 : ℝ) ≤ 2))
  have hγ := (manuscript_cluster_normalized_cubic_errors P Q p ε hp hε hP hQ).2
  change |γ - (1 - 2 * p) / b| ≤ 100 * s at hγ
  have hd : 0 ≤ (1 - 2 * p) / b := div_nonneg (by linarith [hp.2]) hb0.le
  have hγabs : |γ| ≤ (1 - 2 * p) / b + 100 * s := by
    have htri := abs_sub γ ((1 - 2 * p) / b)
    have hh := abs_add_le (γ - (1 - 2 * p) / b) ((1 - 2 * p) / b)
    rw [sub_add_cancel, abs_of_nonneg hd] at hh
    linarith only [hh, hγ]
  constructor
  · have hbnd := mul_le_mul_of_nonneg_left (show 1 / (2 * σ) + |γ| / 6 ≤
        1 / (2 * b) + ((1 - 2 * p) / b + 100 * s) / 6 by linarith only [hscale, hγabs]) phi0_pos.le
    have he : phi0 * (1 / (2 * b) + ((1 - 2 * p) / b + 100 * s) / 6) =
        phi0 * (3 + 1 - 2 * p) / (6 * b) + phi0 * 100 * s / 6 := by ring
    rw [he] at hbnd
    have hm := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le hs
    change phi0 * (1 / (2 * σ) + |γ| / 6) ≤ _
    nlinarith only [hbnd, hm, hs]
  · have hdef := bernoulli_moment_deficit_identity p
    have hnonneg := mul_nonneg (show 0 ≤ 2 * cStar by linarith [cStar_gt_one]) (sq_nonneg (p - pE))
    have hnum : 3 + 1 - 2 * p ≤ cStar * (p ^ 2 + (1 - p) ^ 2) := by nlinarith only [hdef, hnonneg]
    have hm := mul_le_mul_of_nonneg_left hnum (div_nonneg phi0_pos.le (by positivity : 0 ≤ 6 * b))
    rw [cE_eq]
    convert hm using 1 <;> ring

theorem manuscript_effective_cluster_envelope_moment (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    phi0 * (1 / (2 * Real.sqrt (clusterVariance P Q p)) +
      |signedThirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1)| / 6) ≤
      cE * thirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) +
        100 * averageNoiseVariance P Q p := by
  have henv := manuscript_cluster_envelope_comparison P Q p ε hp hε hP hQ
  have hβ := (abs_le.mp (manuscript_cluster_normalized_cubic_errors P Q p ε hp hε hP hQ).1).1
  have hm := mul_le_mul_of_nonneg_left hβ cE_pos.le
  have hp01 := (effective_binomial_parameters p hp).1
  have hs := averageNoiseVariance_nonneg P Q p ⟨hp01.1.le, hp01.2.le⟩
  have hc := mul_le_mul_of_nonneg_right cE_numeric_bounds.2.le hs
  nlinarith only [henv.1, henv.2, hm, hc, hs]

end BerryEsseen
