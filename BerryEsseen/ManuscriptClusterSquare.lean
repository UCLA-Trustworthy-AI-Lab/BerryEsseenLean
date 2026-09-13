import BerryEsseen.ClusterSquare
import BerryEsseen.ManuscriptClusterConditionalTaylor
import BerryEsseen.ManuscriptClusterScalarTaylor

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem manuscript_cluster_raw_second_integrable (P Q : CenteredFourthLaw) (p : ℝ) :
    Integrable (fun x : ℝ => x ^ 2) (twoClusterMeasure P Q p) := by
  apply integrable_twoClusterMeasure P Q p (fun x => x ^ 2) (by fun_prop) (P.integrable_pow 2 (by omega))
  convert Q.shifted_square_integrable (-1) using 1
  funext x
  ring

theorem manuscript_cluster_difference_first_integrable (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)) := by
  letI := twoClusterMeasure_probability P Q p hp
  have hi := twoCluster_first_integrable P Q p
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    ((hi.comp_fst _).sub (hi.comp_snd _))

theorem manuscript_cluster_difference_second_integrable (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    Integrable (fun x : ℝ => x ^ 2) (manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)) := by
  letI := twoClusterMeasure_probability P Q p hp
  have h1 := twoCluster_first_integrable P Q p
  have h2 := manuscript_cluster_raw_second_integrable P Q p
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  convert ((h2.comp_fst _).sub ((h1.mul_prod h1).const_mul 2)).add (h2.comp_snd _) using 1
  funext x
  dsimp
  ring

theorem manuscript_cluster_square_slope_weighted (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    twoClusterSquareSlope P Q p u =
      -(weightedCharFun (manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)) 1 u).im := by
  letI := twoClusterMeasure_probability P Q p hp
  let ν := manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)
  have h1 := manuscript_cluster_difference_first_integrable P Q p hp
  have h0 : Integrable (fun x : ℝ => x ^ 0) ν := by simpa using integrable_const (1 : ℝ)
  have hc : HasDerivAt (charFun ν) (Complex.I * weightedCharFun ν 1 u) u := by
    have h := weightedCharFun_hasDerivAt ν 0 h0 (by simpa using h1) u
    convert h using 1
    funext v
    exact (weightedCharFun_zero ν v).symm
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hc
  have he : (fun v => (charFun ν v).re) = twoClusterSquare P Q p := by
    funext v
    rw [manuscriptDifferenceLaw_charFun, Complex.mul_conj]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq, twoClusterSquare]
  change HasDerivAt (fun v => (charFun ν v).re) _ u at hd
  rw [he] at hd
  have hd' : HasDerivAt (twoClusterSquare P Q p) (-(weightedCharFun ν 1 u).im) u := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] using hd
  exact (twoClusterSquare_hasDerivAt P Q p hp u).unique hd'

theorem manuscript_cluster_square_curvature_weighted (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    twoClusterSquareCurvature P Q p u =
      -(weightedCharFun (manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)) 2 u).re := by
  letI := twoClusterMeasure_probability P Q p hp
  let ν := manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)
  have h1 := manuscript_cluster_difference_first_integrable P Q p hp
  have h2 := manuscript_cluster_difference_second_integrable P Q p hp
  have hd := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u
    (weightedCharFun_hasDerivAt ν 1 (by simpa using h1) h2 u)).neg
  have he : (fun v => -(weightedCharFun ν 1 v).im) = twoClusterSquareSlope P Q p := by
    funext v
    exact (manuscript_cluster_square_slope_weighted P Q p hp v).symm
  change HasDerivAt (fun v => -(weightedCharFun ν 1 v).im) _ u at hd
  rw [he] at hd
  have hd' : HasDerivAt (twoClusterSquareSlope P Q p) (-(weightedCharFun ν 2 u).re) u := by
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] using hd
  exact (twoClusterSquareSlope_hasDerivAt P Q p hp u).unique hd'

theorem manuscript_cluster_square_slope_integral (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    twoClusterSquareSlope P Q p u =
      ∫ x, -x * Real.sin (u*x) ∂manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p) := by
  rw [manuscript_cluster_square_slope_weighted P Q p hp u]
  change -RCLike.im (∫ x : ℝ, (x : ℂ)^1 * realPhase u x ∂_) = _
  rw [← integral_im (weightedCharFun_integrable _ 1 (by simpa using manuscript_cluster_difference_first_integrable P Q p hp) u), ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change -(((x : ℂ)^1 * realPhase u x).im) = _
    simp only [pow_one, realPhase, ← Complex.ofReal_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im, neg_mul])

theorem manuscript_cluster_square_curvature_integral (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    twoClusterSquareCurvature P Q p u =
      ∫ x, -x^2 * Real.cos (u*x) ∂manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p) := by
  rw [manuscript_cluster_square_curvature_weighted P Q p hp u]
  change -RCLike.re (∫ x : ℝ, (x : ℂ)^2 * realPhase u x ∂_) = _
  rw [← integral_re (weightedCharFun_integrable _ 2 (manuscript_cluster_difference_second_integrable P Q p hp) u), ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change -(((x : ℂ)^2 * realPhase u x).re) = _
    simp only [realPhase, ← Complex.ofReal_mul, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, neg_mul])

/-- First original conditional-copy comparison. -/
theorem manuscript_twoCluster_square_difference (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc 0 1)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    |twoClusterSquare P Q p u - bernoulliSquare p u| ≤ averageNoiseVariance P Q p * u ^ 2 := by
  letI := twoClusterMeasure_probability P Q p hp
  have h := manuscript_cluster_conditional_taylor P Q p ε (u ^ 2) hp hP hQ
    (manuscriptClusterCos u) (fun a => -u * Real.sin (u*a)) (by unfold manuscriptClusterCos; fun_prop)
    (fun a ha x hx => by
      have hh := manuscript_cluster_cos_taylor u a x
      convert hh using 1 <;> ring)
  have hb : (1-p)^2 * manuscriptClusterCos u 0 + (1-p)*p*manuscriptClusterCos u (-1) +
      (p*(1-p)*manuscriptClusterCos u 1 + p^2*manuscriptClusterCos u 0) = bernoulliSquare p u := by
    rw [bernoulliSquare_formula]
    simp only [manuscriptClusterCos, mul_zero, Real.cos_zero, mul_neg_one, Real.cos_neg, mul_one]
    ring
  rw [hb] at h
  change |(∫ x, Real.cos (u*x) ∂_) - bernoulliSquare p u| ≤ _ at h
  rw [manuscriptDifferenceLaw_cos] at h
  exact h

/-- Exact coefficient 1+2ε from conditional Taylor of -ξ sin(uξ). -/
theorem manuscript_twoCluster_square_slope_difference_exact (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc 0 1) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    |twoClusterSquareSlope P Q p u - bernoulliSquareSlope p u| ≤
      averageNoiseVariance P Q p * (2*|u|+(1+2*ε)*u^2) := by
  have h := manuscript_cluster_conditional_taylor P Q p ε (2*|u|+(1+2*ε)*u^2) hp hP hQ
    (manuscriptClusterSinWeight u) (fun a => -Real.sin (u*a)-a*u*Real.cos (u*a))
    (by unfold manuscriptClusterSinWeight; fun_prop)
    (fun a ha x hx => by
      have hh := manuscript_cluster_sinWeight_taylor u a x ε hε (abs_le.mpr ha) hx
      convert hh using 1 <;> ring)
  have hb : (1-p)^2 * manuscriptClusterSinWeight u 0 + (1-p)*p*manuscriptClusterSinWeight u (-1) +
      (p*(1-p)*manuscriptClusterSinWeight u 1 + p^2*manuscriptClusterSinWeight u 0) = bernoulliSquareSlope p u := by
    rw [bernoulliSquareSlope_formula]
    simp only [manuscriptClusterSinWeight, neg_zero, zero_mul, mul_zero, Real.sin_zero,
      mul_neg_one, Real.sin_neg, neg_neg, one_mul, neg_mul, mul_one]
    ring
  rw [hb] at h
  change |(∫ x, -x*Real.sin (u*x) ∂_) - bernoulliSquareSlope p u| ≤ _ at h
  rw [← manuscript_cluster_square_slope_integral P Q p hp u] at h
  exact h

/-- Exact second derivative bound from conditional Taylor of -ξ² cos(uξ). -/
theorem manuscript_twoCluster_square_curvature_difference_exact (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc 0 1) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    |twoClusterSquareCurvature P Q p u - bernoulliSquareCurvature p u| ≤
      averageNoiseVariance P Q p * (2+4*(1+2*ε)*|u|+(1+2*ε)^2*u^2) := by
  have h := manuscript_cluster_conditional_taylor P Q p ε (2+4*(1+2*ε)*|u|+(1+2*ε)^2*u^2) hp hP hQ
    (manuscriptClusterCosSquareWeight u) (fun a => -2*a*Real.cos (u*a)+a^2*u*Real.sin (u*a))
    (by unfold manuscriptClusterCosSquareWeight; fun_prop)
    (fun a ha x hx => by
      have hh := manuscript_cluster_cosSquareWeight_taylor u a x ε hε (abs_le.mpr ha) hx
      convert hh using 1 <;> ring)
  have hb : (1-p)^2 * manuscriptClusterCosSquareWeight u 0 + (1-p)*p*manuscriptClusterCosSquareWeight u (-1) +
      (p*(1-p)*manuscriptClusterCosSquareWeight u 1 + p^2*manuscriptClusterCosSquareWeight u 0) = bernoulliSquareCurvature p u := by
    rw [bernoulliSquareCurvature_formula]
    norm_num [manuscriptClusterCosSquareWeight, Real.cos_neg]
    ring
  rw [hb] at h
  change |(∫ x, -x^2*Real.cos (u*x) ∂_) - bernoulliSquareCurvature p u| ≤ _ at h
  rw [← manuscript_cluster_square_curvature_integral P Q p hp u] at h
  exact h

theorem manuscript_twoCluster_square_slope_difference (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc 0 1) (hε : ε ∈ Icc 0 (1/10))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    |twoClusterSquareSlope P Q p u - bernoulliSquareSlope p u| ≤
      averageNoiseVariance P Q p * (2*|u|+(3/2)*u^2) := by
  apply (manuscript_twoCluster_square_slope_difference_exact P Q p ε hp hε.1 hP hQ u).trans
  apply mul_le_mul_of_nonneg_left _ (averageNoiseVariance_nonneg P Q p hp)
  nlinarith [mul_le_mul_of_nonneg_right hε.2 (sq_nonneg u)]

theorem manuscript_twoCluster_square_curvature_difference (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc 0 1) (hε : ε ∈ Icc 0 (1/10))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    |twoClusterSquareCurvature P Q p u - bernoulliSquareCurvature p u| ≤
      10*averageNoiseVariance P Q p*(1+u^2) := by
  apply (manuscript_twoCluster_square_curvature_difference_exact P Q p ε hp hε.1 hP hQ u).trans
  have hM : 1+2*ε ≤ (1.2 : ℝ) := by linarith [hε.2]
  have hM0 : 0 ≤ 1+2*ε := by linarith [hε.1]
  have h1 := mul_le_mul_of_nonneg_right hM (abs_nonneg u)
  have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM0 hM 2) (sq_nonneg u)
  have hp : 2+4*(1+2*ε)*|u|+(1+2*ε)^2*u^2 ≤ 10*(1+u^2) := by
    nlinarith [sq_nonneg (|u|-1), sq_abs u]
  have hm := mul_le_mul_of_nonneg_left hp (averageNoiseVariance_nonneg P Q p ‹p ∈ Icc 0 1›)
  nlinarith only [hm]

end BerryEsseen
