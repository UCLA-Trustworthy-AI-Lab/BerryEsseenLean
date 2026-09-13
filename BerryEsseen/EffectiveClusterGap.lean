import BerryEsseen.EffectiveClusterPeaks
import BerryEsseen.AnnularIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem cos_quarter_effective : Real.cos (1 / 4 : ℝ) ≤ 0.97 := by
  have hsin : (0.123 : ℝ) < Real.sin (1 / 8) := by
    have h := Real.sin_gt_sub_cube (x := 1 / 8) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  rw [show (1 / 4 : ℝ) = 2 * (1 / 8) by ring, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (1 / 8), sq_nonneg (Real.sin (1 / 8) - 0.123)]

theorem effective_cluster_spectral_gap (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (u : ℝ) (hu : |u| ≤ T) (haway : ∀ j : ℤ, 1 / 4 ≤ |u - (j : ℝ) * (2 * Real.pi)|) :
    twoClusterSquare P Q p u ≤ 0.99 := by
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hs0 := averageNoiseVariance_nonneg P Q p hp01
  have hsT := effective_cluster_variance_budget P Q p ε T hp01 hε hT hεT hP hQ
  have hu2 : u ^ 2 ≤ T ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hsu := mul_le_mul_of_nonneg_left hu2 hs0
  have hv : 6 / 25 ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (show 0 ≤ 3 / 5 - p by linarith [hp.2])]
  have hres : 1 / 4 ≤ |circularResidual u| := haway (round (u / (2 * Real.pi)))
  have hcos : Real.cos u ≤ 0.97 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (circularResidual_bound u) hres
    rw [Real.cos_abs, circularResidual, Real.cos_sub_int_mul_two_pi] at h
    exact h.trans cos_quarter_effective
  have hprod := mul_le_mul hv (show (0.03 : ℝ) ≤ 1 - Real.cos u by linarith)
    (by norm_num : (0 : ℝ) ≤ 0.03) (by positivity : 0 ≤ p * (1 - p))
  have hdiff := (abs_le.mp (manuscript_twoCluster_square_difference P Q p ε hp01 hP hQ u)).2
  rw [bernoulliSquare_formula] at hdiff
  nlinarith only [hprod, hdiff, hsu, hsT]

theorem effective_cluster_spectral_power (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (u : ℝ) (hu : |u| ≤ T) (haway : ∀ j : ℤ, 1 / 4 ≤ |u - (j : ℝ) * (2 * Real.pi)|) (n : ℕ) :
    ‖charFun (twoClusterMeasure P Q p) u‖ ^ n ≤ Real.exp (-(n : ℝ) / 200) := by
  have h := effective_cluster_spectral_gap P Q p ε T hp hε hT hεT hP hQ u hu haway
  have hpoint : ‖charFun (twoClusterMeasure P Q p) u‖ ^ 2 ≤ 1 - (1 / 100 : ℝ) * (1 : ℝ) ^ 2 := by
    change twoClusterSquare P Q p u ≤ _
    nlinarith only [h]
  have he := norm_pow_gaussian_of_quadratic_bound (charFun (twoClusterMeasure P Q p) u) 1 (1 / 100) hpoint n
  convert he using 1
  congr 1
  ring

end BerryEsseen
