import BerryEsseen.ClusterNormalization
import BerryEsseen.GaussianScale
import BerryEsseen.ManuscriptBinomialEffective

/-! The appendix's prefactor error 50s and Gaussian variance error s. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_effective_prefactor_error (p s ρ : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hρ : |ρ - p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)| ≤ 4 * s) :
    |Real.sqrt (p * (1 - p) + s) ^ 3 / ρ -
      Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2)| ≤ 50 * s := by
  let v := p * (1 - p)
  let τ := p ^ 2 + (1 - p) ^ 2
  let AB := Real.sqrt v / τ
  have hb := effective_binomial_parameters p hp
  have hv : (0.24 : ℝ) ≤ v := by
    dsimp [v]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hv0 : 0 < v := by linarith
  have hτ : (1 / 2 : ℝ) ≤ τ := hb.2.2.2.1
  have hτ0 : 0 < τ := by linarith
  have hρl : (11 / 100 : ℝ) ≤ ρ := by
    have hm := mul_le_mul hv hτ (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0.le
    have hh := (abs_le.mp hρ).1
    change -(4 * s) ≤ ρ - v * τ at hh
    nlinarith [hs.2]
  have hρ0 : 0 < ρ := by linarith
  have hAB := bernoulli_normalization_coefficient p hb.1
  change AB ∈ Ioc 0 1 at hAB
  have hcube := sqrt_cube_increment_bound v s hv0 hs.1 (by linarith [hs.2])
  have hcube' : |Real.sqrt (v + s) ^ 3 - Real.sqrt v ^ 3| ≤ (3 / 2) * s := by
    apply hcube.trans
    have hh := mul_le_mul_of_nonneg_right hb.2.2.1 hs.1
    change Real.sqrt v * s ≤ (1 / 2) * s at hh
    linarith
  have hABcube : AB * (v * τ) = Real.sqrt v ^ 3 := by
    dsimp [AB]
    rw [pow_succ, Real.sq_sqrt hv0.le]
    field_simp [hτ0.ne']
  have hnum : |(Real.sqrt (v + s) ^ 3 / ρ - AB) * ρ| ≤ (11 / 2) * s := by
    have he : (Real.sqrt (v + s) ^ 3 / ρ - AB) * ρ =
        (Real.sqrt (v + s) ^ 3 - Real.sqrt v ^ 3) + AB * (v * τ - ρ) := by
      rw [mul_sub, hABcube, sub_mul, div_mul_cancel₀ _ hρ0.ne']
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    have hm := mul_le_mul hAB.2 hρ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    rw [one_mul] at hm
    change AB * |ρ - v * τ| ≤ 4 * s at hm
    rw [abs_sub_comm ρ] at hm
    rw [abs_mul, abs_of_pos hAB.1]
    linarith
  rw [abs_mul, abs_of_pos hρ0] at hnum
  have hm := mul_le_mul_of_nonneg_left hρl
    (abs_nonneg (Real.sqrt (v + s) ^ 3 / ρ - AB))
  change |Real.sqrt (v + s) ^ 3 / ρ - AB| ≤ 50 * s
  nlinarith only [hnum, hm]

theorem manuscript_effective_cluster_prefactor_error (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ 1 / (10 : ℝ) ^ 12) :
    |Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p -
      Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2)| ≤ 50 * averageNoiseVariance P Q p := by
  have hpcc : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hs0 := averageNoiseVariance_nonneg P Q p hpcc
  have hρ := twoCluster_abs_third_error P Q p ε hpcc
    (by linarith [hε.2, hp.1]) (by linarith [hε.2, hp.2]) hP hQ
  change |clusterThirdAbsoluteMoment P Q p - _| ≤ (3 + ε) * averageNoiseVariance P Q p at hρ
  have hρ4 : |clusterThirdAbsoluteMoment P Q p - p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)| ≤
      4 * averageNoiseVariance P Q p := by
    have hm := mul_le_mul_of_nonneg_right (show 3 + ε ≤ (4 : ℝ) by linarith [hε.2]) hs0
    exact hρ.trans hm
  have h := manuscript_effective_prefactor_error p (averageNoiseVariance P Q p)
    (clusterThirdAbsoluteMoment P Q p) hp ⟨hs0, hs⟩ hρ4
  have he : p * (1 - p) + averageNoiseVariance P Q p = clusterVariance P Q p := by
    unfold averageNoiseVariance clusterVariance
    ring
  rwa [he] at h

/-- The other two inequalities in the manuscript's prefactor display are
deduced from the same conditional cubic expansion and 50s estimate. -/
theorem manuscript_effective_cluster_prefactor_bounds (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ 1 / (10 : ℝ) ^ 12) :
    (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) ∈ Ioo (1 / 2) 2 := by
  have hb := effective_binomial_parameters p hp
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by linarith [hb.2.2.2.1]
  have hAB := bernoulli_normalization_coefficient p hb.1
  have hABlo : (9 / 10 : ℝ) ≤ Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) := by
    apply (le_div_iff₀ hτ).2
    nlinarith [hb.2.1, hb.2.2.2.2]
  have hd := abs_le.mp (manuscript_effective_cluster_prefactor_error P Q p ε hp hε hP hQ hs)
  exact ⟨by linarith [hd.1], by linarith [hd.2, hAB.2]⟩

theorem manuscript_gaussian_variance_ratio_bound (z r : ℝ) (hr : 0 ≤ r) :
    |normalCDF (z / Real.sqrt (1 + r)) - normalCDF z| ≤ r / 8 := by
  have hd (ell : ℝ) (hell : ell ∈ Icc (-r) 0) :
      HasDerivWithinAt (fun v => normalCDF (gaussianScaleArgument z v))
        (gaussianScaleFirst z ell) (Icc (-r) 0) ell :=
    (gaussianScale_hasDerivAt z ell (by linarith [hell.2])).hasDerivWithinAt
  have hb (ell : ℝ) (hell : ell ∈ Icc (-r) 0) : ‖gaussianScaleFirst z ell‖ ≤ 1 / 8 := by
    have hden : 0 < 2 * (1 - ell) := by linarith [hell.2]
    rw [Real.norm_eq_abs, gaussianScaleFirst, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have h := gaussian_first_monomial_effective (gaussianScaleArgument z ell)
    linarith [hell.2]
  have h := (convex_Icc (-r) 0).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (show (0 : ℝ) ∈ Icc (-r) 0 by constructor <;> linarith)
    (show -r ∈ Icc (-r) 0 by constructor <;> linarith)
  simpa only [gaussianScaleArgument, sub_zero, sub_neg_eq_add, Real.sqrt_one, div_one,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg hr, one_div, mul_comm] using h

theorem manuscript_effective_gaussian_variance_bound (z p s : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : 0 ≤ s) :
    |normalCDF (z / Real.sqrt (p * (1 - p) + s)) -
      normalCDF (z / Real.sqrt (p * (1 - p)))| ≤ s := by
  have hv : (0.24 : ℝ) ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hv0 : 0 < p * (1 - p) := by linarith
  have h := manuscript_gaussian_variance_ratio_bound (z / Real.sqrt (p * (1 - p)))
    (s / (p * (1 - p))) (div_nonneg hs hv0.le)
  have he : (z / Real.sqrt (p * (1 - p))) / Real.sqrt (1 + s / (p * (1 - p))) =
      z / Real.sqrt (p * (1 - p) + s) := by
    rw [div_div, ← Real.sqrt_mul hv0.le]
    congr 2
    calc
      p * (1 - p) * (1 + s / (p * (1 - p))) =
          p * (1 - p) + (p * (1 - p) * s) / (p * (1 - p)) := by ring
      _ = _ := by rw [mul_div_cancel_left₀ s hv0.ne']
  rw [he] at h
  apply h.trans
  rw [div_div]
  apply (div_le_iff₀ (mul_pos hv0 (by norm_num : (0 : ℝ) < 8))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hv hs, hs]

/-- The appendix's restoration of the original binomial normalization and
Gaussian variance. The constants are the manuscript's 50s, s, and final
100 lambda / sqrt(n), with Schulz's strict Bernoulli bound used explicitly. -/
theorem manuscript_effective_perturbed_binomial_branch_bound
    (B : PublishedBernoulliBound) (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ 1 / (10 : ℝ) ^ 12)
    (n : ℕ) (hn : 1 ≤ n) (t F : ℝ)
    (hF : |F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| ≤
      binomialKolmogorov p n) :
    |Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 /
        clusterThirdAbsoluteMoment P Q p) *
      (F - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)))| ≤
      binomialNormalizedConstant p n +
        100 * Real.sqrt (n : ℝ) * averageNoiseVariance P Q p := by
  let v := p * (1 - p)
  let τ := p ^ 2 + (1 - p) ^ 2
  let s := averageNoiseVariance P Q p
  let r := Real.sqrt (n : ℝ)
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let AB := Real.sqrt v / τ
  let G0 := normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))
  let G := normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  have hb := effective_binomial_parameters p hp
  have hs0 : 0 ≤ s := averageNoiseVariance_nonneg P Q p ⟨hb.1.1.le, hb.1.2.le⟩
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)).2 (by exact_mod_cast hn)
  have hv : 0 < v := mul_pos hb.1.1 (sub_pos.mpr hb.1.2)
  have hτ : 0 < τ := by have := hb.2.2.2.1; change (1 / 2 : ℝ) ≤ τ at this; linarith
  have hAB : AB ∈ Ioc 0 1 := bernoulli_normalization_coefficient p hb.1
  have hA : 0 ≤ A := div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (clusterThirdAbsoluteMoment_pos P Q p hb.1).le
  have hdiff : |A - AB| ≤ 50 * s := manuscript_effective_cluster_prefactor_error P Q p ε hp hε hP hQ hs
  have hA2 : A ≤ 2 := by have := (abs_le.mp hdiff).2; linarith [hAB.2, hs]
  have hroot : Real.sqrt ((n : ℝ) * p * (1 - p)) = r * Real.sqrt v := by
    rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg n)]
  have hK : binomialKolmogorov p n ≤ 1 / r := by
    have hS := (B.strict_bound p hb.1 n hn).le
    rw [hroot] at hS
    apply hS.trans
    apply (div_le_iff₀ (mul_pos hr (Real.sqrt_pos.mpr hv))).2
    have he : 1 / r * (r * Real.sqrt v) = Real.sqrt v := by field_simp [hr.ne']
    rw [he]
    have hm := mul_le_mul_of_nonneg_right cE_numeric_bounds.2.le
      (show 0 ≤ p ^ 2 + (1 - p) ^ 2 by positivity)
    have ht := mul_le_mul_of_nonneg_left hb.2.2.2.2 (by norm_num : (0 : ℝ) ≤ 0.4098)
    change cE * τ ≤ Real.sqrt v
    have hvlow : (0.48 : ℝ) ≤ Real.sqrt v := hb.2.1
    linarith
  have hGdiff : |G0 - G| ≤ s := by
    have hg := manuscript_effective_gaussian_variance_bound
      ((t - (n : ℝ) * p) / r) p s hp hs0
    have harg (w : ℝ) : ((t - (n : ℝ) * p) / r) / Real.sqrt w =
        (t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * w) := by
      rw [div_div, Real.sqrt_mul (Nat.cast_nonneg n)]
    rw [harg, harg] at hg
    have hvps : p * (1 - p) + s = clusterVariance P Q p := by
      dsimp only [s, averageNoiseVariance, clusterVariance]
      ring
    rw [hvps, ← mul_assoc] at hg
    exact (abs_sub_comm _ _).trans_le hg
  have hbase : |r * AB * (F - G0)| ≤ binomialNormalizedConstant p n := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hr.le hAB.1.le)]
    have hm := mul_le_mul_of_nonneg_left hF (mul_nonneg hr.le hAB.1.le)
    apply hm.trans_eq
    unfold binomialNormalizedConstant
    rw [hroot]
    dsimp only [AB]
    ring
  have he1 : |r * (A - AB) * (F - G0)| ≤ 50 * r * s := by
    rw [abs_mul, abs_mul, abs_of_pos hr]
    have hm := mul_le_mul hdiff (hF.trans hK) (abs_nonneg _) (by positivity : 0 ≤ 50 * s)
    have hmul := mul_le_mul_of_nonneg_left hm hr.le
    have he : r * (50 * s * (1 / r)) = 50 * s := by field_simp [hr.ne']
    rw [he] at hmul
    have hsr := mul_le_mul_of_nonneg_right hr1 hs0
    nlinarith only [hmul, hsr]
  have he2 : |r * A * (G0 - G)| ≤ 2 * r * s := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hr.le hA)]
    have hm := mul_le_mul hA2 hGdiff (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hmul := mul_le_mul_of_nonneg_left hm hr.le
    nlinarith only [hmul]
  have he : r * A * (F - G) =
      (r * AB * (F - G0) + r * (A - AB) * (F - G0)) + r * A * (G0 - G) := by ring
  change |r * A * (F - G)| ≤ binomialNormalizedConstant p n + 100 * r * s
  rw [he]
  have ht := (abs_add_le (r * AB * (F - G0) + r * (A - AB) * (F - G0))
    (r * A * (G0 - G))).trans (add_le_add (abs_add_le _ _) le_rfl)
  nlinarith only [ht, hbase, he1, he2, mul_nonneg hr.le hs0]

end BerryEsseen
