import BerryEsseen.EffectiveLocalMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def clusterSignedThirdMoment (P Q : CenteredFourthLaw) (p : ℝ) : ℝ :=
  ∫ x, (x - p) ^ 3 ∂twoClusterMeasure P Q p

theorem clusterSignedThirdMoment_formula (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    clusterSignedThirdMoment P Q p = p * (1 - p) * (1 - 2 * p) +
      (1 - p) * (P.thirdMoment - 3 * p * P.secondMoment) +
      p * (Q.thirdMoment + 3 * (1 - p) * Q.secondMoment) := by
  have he : (fun x : ℝ => ((1 + x) - p) ^ 3) = (fun x => (x - (p - 1)) ^ 3) := by funext x; ring
  unfold clusterSignedThirdMoment
  rw [integral_twoClusterMeasure P Q p hp _ (by fun_prop) (P.shifted_cube_integrable p)
    (by rw [he]; exact Q.shifted_cube_integrable (p - 1)), he,
    P.shifted_cube_integral, Q.shifted_cube_integral]
  ring

theorem clusterSignedThirdMoment_error (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc 0 1)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    |clusterSignedThirdMoment P Q p - p * (1 - p) * (1 - 2 * p)| ≤ (3 + ε) * averageNoiseVariance P Q p := by
  rw [clusterSignedThirdMoment_formula P Q p hp]
  have hp0 := hp.1
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hP0 := P.secondMoment_nonneg
  have hQ0 := Q.secondMoment_nonneg
  have hPl := P.thirdMoment_bound ε hP
  have hQl := Q.thirdMoment_bound ε hQ
  have hPerr : |P.thirdMoment - 3 * p * P.secondMoment| ≤ (3 + ε) * P.secondMoment := by
    have h := abs_sub P.thirdMoment (3 * p * P.secondMoment)
    rw [abs_of_nonneg (by positivity : 0 ≤ 3 * p * P.secondMoment)] at h
    nlinarith [mul_le_mul_of_nonneg_right hp.2 hP0]
  have hQerr : |Q.thirdMoment + 3 * (1 - p) * Q.secondMoment| ≤ (3 + ε) * Q.secondMoment := by
    have h := abs_add_le Q.thirdMoment (3 * (1 - p) * Q.secondMoment)
    rw [abs_of_nonneg (by positivity : 0 ≤ 3 * (1 - p) * Q.secondMoment)] at h
    nlinarith [mul_nonneg hp.1 hQ0]
  have htri := abs_add_le ((1 - p) * (P.thirdMoment - 3 * p * P.secondMoment))
    (p * (Q.thirdMoment + 3 * (1 - p) * Q.secondMoment))
  rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hp.1] at htri
  have h1 := mul_le_mul_of_nonneg_left hPerr hq
  have h2 := mul_le_mul_of_nonneg_left hQerr hp.1
  have he : p * (1 - p) * (1 - 2 * p) + (1 - p) * (P.thirdMoment - 3 * p * P.secondMoment) +
      p * (Q.thirdMoment + 3 * (1 - p) * Q.secondMoment) - p * (1 - p) * (1 - 2 * p) =
      (1 - p) * (P.thirdMoment - 3 * p * P.secondMoment) + p * (Q.thirdMoment + 3 * (1 - p) * Q.secondMoment) := by ring
  rw [he]
  unfold averageNoiseVariance
  nlinarith only [htri, h1, h2]

theorem standardizedTwoCluster_signed_third (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    signedThirdMoment (standardizedTwoClusterLaw P Q p hp) =
      clusterSignedThirdMoment P Q p / Real.sqrt (clusterVariance P Q p) ^ 3 := by
  rw [signedThirdMoment, standardizedTwoClusterLaw_measure, standardizedMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [div_pow]
  exact integral_div _ _

theorem bernoulli_moment_deficit_identity (p : ℝ) :
    cStar * (p ^ 2 + (1 - p) ^ 2) - 2 * (2 - p) = 2 * cStar * (p - pE) ^ 2 := by
  unfold cStar pE
  linear_combination ((5 / 2 : ℝ) - 2 * p - Real.sqrt 10 / 2) * sqrt10_sq

theorem effective_cluster_envelope_moment (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    phi0 * (1 / (2 * Real.sqrt (clusterVariance P Q p)) +
      |signedThirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1)| / 6) ≤
      cE * thirdMoment (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) +
        20 * averageNoiseVariance P Q p := by
  let v := p * (1 - p)
  let s := averageNoiseVariance P Q p
  let τ := p ^ 2 + (1 - p) ^ 2
  let d := 1 - 2 * p
  let ρ := clusterThirdAbsoluteMoment P Q p
  let m := clusterSignedThirdMoment P Q p
  let σ := Real.sqrt (clusterVariance P Q p)
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hs : 0 ≤ s := averageNoiseVariance_nonneg P Q p hpcc
  have hσb := effective_cluster_scale_bounds P Q p ε hp hε hP hQ
  have hσ : 0 < σ := by have h := hσb.1.1; change (0.48 : ℝ) ≤ σ at h; linarith
  have hσ2 : σ ^ 2 = v + s := by
    dsimp only [σ, v, s]
    rw [Real.sq_sqrt (clusterVariance_pos P Q p hp01).le]
    unfold clusterVariance averageNoiseVariance
    ring
  have hσ3 : (0.11 : ℝ) ≤ σ ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.48) hσb.1.1 3
    change (0.48 : ℝ) ^ 3 ≤ σ ^ 3 at hh
    norm_num at hh
    linarith
  have hmerr := clusterSignedThirdMoment_error P Q p ε hpcc hP hQ
  change |m - v * d| ≤ (3 + ε) * s at hmerr
  have hρerr := twoCluster_abs_third_error P Q p ε hpcc (by linarith [hε.2, hp.1]) (by linarith [hε.2, hp.2]) hP hQ
  change |ρ - v * τ| ≤ (3 + ε) * s at hρerr
  have hεs := mul_le_mul_of_nonneg_right hε.2 hs
  have hρlo : v * τ - 4 * s ≤ ρ := by have h := (abs_le.mp hρerr).1; nlinarith
  have hmhi : |m| ≤ v * d + 4 * s := by
    have hvd : 0 ≤ v * d := by dsimp only [v, d]; exact mul_nonneg (mul_nonneg hpcc.1 (sub_nonneg.mpr hpcc.2)) (by linarith [hp.2])
    have htri := abs_add_le (m - v * d) (v * d)
    rw [sub_add_cancel, abs_of_nonneg hvd] at htri
    nlinarith
  have hBern : phi0 * (v / 2 + v * d / 6) ≤ cE * (v * τ) := by
    have hdef := bernoulli_moment_deficit_identity p
    have hpos := mul_nonneg (show 0 ≤ 2 * cStar by linarith [cStar_gt_one]) (sq_nonneg (p - pE))
    have hv : 0 ≤ v := mul_nonneg hpcc.1 (sub_nonneg.mpr hpcc.2)
    have hmul := mul_le_mul_of_nonneg_left (show 2 * (2 - p) ≤ cStar * τ by dsimp only [τ]; linarith) (mul_nonneg phi0_pos.le hv)
    rw [cE_eq]
    dsimp only [d]
    nlinarith only [hmul]
  have hnum : phi0 * (σ ^ 2 / 2 + |m| / 6) ≤ cE * ρ + 20 * s * σ ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_left hmhi phi0_pos.le
    have h2 := mul_le_mul_of_nonneg_left hρlo cE_pos.le
    have h3 := mul_le_mul_of_nonneg_left hσ3 hs
    have h4 := mul_le_mul_of_nonneg_right cE_numeric_bounds.2.le hs
    have h5 := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le hs
    rw [hσ2]
    nlinarith only [hBern, h1, h2, h3, h4, h5, hs]
  rw [standardizedTwoCluster_signed_third, standardizedTwoClusterLaw_third, abs_div, abs_of_pos (pow_pos hσ 3)]
  change phi0 * (1 / (2 * σ) + |m| / σ ^ 3 / 6) ≤ cE * (ρ / σ ^ 3) + 20 * s
  have hid : phi0 * (1 / (2 * σ) + |m| / σ ^ 3 / 6) = phi0 * (σ ^ 2 / 2 + |m| / 6) / σ ^ 3 := by field_simp
  rw [hid]
  apply (div_le_iff₀ (pow_pos hσ 3)).mpr
  convert hnum using 1
  field_simp
  <;> ring

end BerryEsseen
