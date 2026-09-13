import BerryEsseen.ClusterCharacteristic

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem complex_norm_square_difference (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have he : ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ + ‖w‖) * (‖z‖ - ‖w‖) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w))]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le z w) (by positivity)

theorem complex_inner_difference_bound (z w z' w' : ℂ) :
    |inner ℝ z z' - inner ℝ w w'| ≤ ‖z‖ * ‖z' - w'‖ + ‖w'‖ * ‖z - w‖ := by
  have he : inner ℝ z z' - inner ℝ w w' =
      inner ℝ z (z' - w') + inner ℝ (z - w) w' := by
    simp only [inner_sub_right, inner_sub_left]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _)
    ((abs_real_inner_le_norm _ _).trans_eq (mul_comm _ _)))

def twoClusterSquare (P Q : CenteredFourthLaw) (p u : ℝ) : ℝ :=
  ‖charFun (twoClusterMeasure P Q p) u‖ ^ 2

def twoClusterSquareSlope (P Q : CenteredFourthLaw) (p u : ℝ) : ℝ :=
  2 * inner ℝ (charFun (twoClusterMeasure P Q p) u) (rawTwoClusterDerivative P Q p u)

def twoClusterSquareCurvature (P Q : CenteredFourthLaw) (p u : ℝ) : ℝ :=
  2 * (inner ℝ (charFun (twoClusterMeasure P Q p) u) (rawTwoClusterSecondDerivative P Q p u) +
    inner ℝ (rawTwoClusterDerivative P Q p u) (rawTwoClusterDerivative P Q p u))

def bernoulliSquare (p u : ℝ) : ℝ := ‖rawBernoulliCF p u‖ ^ 2

def bernoulliSquareSlope (p u : ℝ) : ℝ :=
  2 * inner ℝ (rawBernoulliCF p u) (rawBernoulliDerivative p u)

def bernoulliSquareCurvature (p u : ℝ) : ℝ :=
  2 * (inner ℝ (rawBernoulliCF p u) (rawBernoulliSecondDerivative p u) +
    inner ℝ (rawBernoulliDerivative p u) (rawBernoulliDerivative p u))

theorem twoClusterSquare_hasDerivAt (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc 0 1) (u : ℝ) :
    HasDerivAt (twoClusterSquare P Q p) (twoClusterSquareSlope P Q p u) u :=
  (rawTwoCluster_hasDerivAt P Q p hp u).norm_sq

theorem twoClusterSquareSlope_hasDerivAt (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc 0 1) (u : ℝ) :
    HasDerivAt (twoClusterSquareSlope P Q p) (twoClusterSquareCurvature P Q p u) u :=
  ((rawTwoCluster_hasDerivAt P Q p hp u).inner ℝ (rawTwoClusterDerivative_hasDerivAt P Q p u)).const_mul 2

theorem bernoulliSquare_hasDerivAt (p u : ℝ) :
    HasDerivAt (bernoulliSquare p) (bernoulliSquareSlope p u) u :=
  (rawBernoulliCF_hasDerivAt p u).norm_sq

theorem bernoulliSquareSlope_hasDerivAt (p u : ℝ) :
    HasDerivAt (bernoulliSquareSlope p) (bernoulliSquareCurvature p u) u :=
  ((rawBernoulliCF_hasDerivAt p u).inner ℝ (rawBernoulliDerivative_hasDerivAt p u)).const_mul 2

theorem twoCluster_square_difference (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    |twoClusterSquare P Q p u - bernoulliSquare p u| ≤ averageNoiseVariance P Q p * u ^ 2 := by
  letI := twoClusterMeasure_probability P Q p hp
  have h := complex_norm_square_difference (charFun (twoClusterMeasure P Q p) u) (rawBernoulliCF p u)
  have hb := mul_le_mul (add_le_add (norm_charFun_le_one (μ := twoClusterMeasure P Q p) u)
    (rawBernoulliCF_norm_le p hp u)) (twoCluster_characteristic_difference_bound P Q p hp u)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 + 1)
  change |twoClusterSquare P Q p u - bernoulliSquare p u| ≤ _ at h
  nlinarith only [h, hb]

theorem twoCluster_square_slope_difference (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 (1 / 2)) (u : ℝ) :
    |twoClusterSquareSlope P Q p u - bernoulliSquareSlope p u| ≤
      averageNoiseVariance P Q p * (2 * |u| + (3 / 2) * u ^ 2) := by
  have hp01 : p ∈ Icc 0 1 := ⟨hp.1, by linarith [hp.2]⟩
  letI := twoClusterMeasure_probability P Q p hp01
  have h := complex_inner_difference_bound (charFun (twoClusterMeasure P Q p) u) (rawBernoulliCF p u)
    (rawTwoClusterDerivative P Q p u) (rawBernoulliDerivative p u)
  rw [rawBernoulliDerivative_norm p hp.1] at h
  have h1 := mul_le_mul_of_nonneg_right (norm_charFun_le_one (μ := twoClusterMeasure P Q p) u)
    (norm_nonneg (rawTwoClusterDerivative P Q p u - rawBernoulliDerivative p u))
  have h2 := mul_le_mul_of_nonneg_left (twoCluster_characteristic_difference_bound P Q p hp01 u) hp.1
  have h3 := twoCluster_characteristic_derivative_difference P Q p hp01 u
  have hs := averageNoiseVariance_nonneg P Q p hp01
  have h4 := mul_le_mul_of_nonneg_right hp.2 (mul_nonneg hs (sq_nonneg u))
  have he : twoClusterSquareSlope P Q p u - bernoulliSquareSlope p u =
      2 * (inner ℝ (charFun (twoClusterMeasure P Q p) u) (rawTwoClusterDerivative P Q p u) -
        inner ℝ (rawBernoulliCF p u) (rawBernoulliDerivative p u)) := by
    unfold twoClusterSquareSlope bernoulliSquareSlope
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [h, h1, h2, h3, h4]

theorem twoCluster_square_curvature_difference (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc 0 (9 / 20)) (hε : ε ≤ 1 / 10)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    |twoClusterSquareCurvature P Q p u - bernoulliSquareCurvature p u| ≤
      10 * averageNoiseVariance P Q p * (1 + u ^ 2) := by
  have hp01 : p ∈ Icc 0 1 := ⟨hp.1, by linarith [hp.2]⟩
  letI := twoClusterMeasure_probability P Q p hp01
  have hi := complex_inner_difference_bound (charFun (twoClusterMeasure P Q p) u) (rawBernoulliCF p u)
    (rawTwoClusterSecondDerivative P Q p u) (rawBernoulliSecondDerivative p u)
  rw [rawBernoulliSecondDerivative_norm p hp.1] at hi
  have h1 := mul_le_mul_of_nonneg_right (norm_charFun_le_one (μ := twoClusterMeasure P Q p) u)
    (norm_nonneg (rawTwoClusterSecondDerivative P Q p u - rawBernoulliSecondDerivative p u))
  have h2 := mul_le_mul_of_nonneg_left (twoCluster_characteristic_difference_bound P Q p hp01 u) hp.1
  have h3 := twoCluster_characteristic_second_derivative_difference P Q p hp01 u
  have hs := averageNoiseVariance_nonneg P Q p hp01
  have h4 := mul_le_mul_of_nonneg_right (show p ≤ 1 / 2 by linarith [hp.2]) (mul_nonneg hs (sq_nonneg u))
  have hnorm : ‖rawTwoClusterDerivative P Q p u‖ + ‖rawBernoulliDerivative p u‖ ≤ 1 := by
    rw [rawBernoulliDerivative_norm p hp.1]
    linarith [rawTwoClusterDerivative_norm_le P Q p ε hp01 hP hQ u, hp.2]
  have hsq := complex_norm_square_difference (rawTwoClusterDerivative P Q p u) (rawBernoulliDerivative p u)
  have hsq1 := mul_le_mul_of_nonneg_right hnorm
    (norm_nonneg (rawTwoClusterDerivative P Q p u - rawBernoulliDerivative p u))
  have hsq2 := twoCluster_characteristic_derivative_difference P Q p hp01 u
  have he : twoClusterSquareCurvature P Q p u - bernoulliSquareCurvature p u =
      2 * ((inner ℝ (charFun (twoClusterMeasure P Q p) u) (rawTwoClusterSecondDerivative P Q p u) -
        inner ℝ (rawBernoulliCF p u) (rawBernoulliSecondDerivative p u)) +
        (‖rawTwoClusterDerivative P Q p u‖ ^ 2 - ‖rawBernoulliDerivative p u‖ ^ 2)) := by
    simp only [twoClusterSquareCurvature, bernoulliSquareCurvature, real_inner_self_eq_norm_sq]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ha := abs_add_le
    (inner ℝ (charFun (twoClusterMeasure P Q p) u) (rawTwoClusterSecondDerivative P Q p u) -
      inner ℝ (rawBernoulliCF p u) (rawBernoulliSecondDerivative p u))
    (‖rawTwoClusterDerivative P Q p u‖ ^ 2 - ‖rawBernoulliDerivative p u‖ ^ 2)
  have hpoly : 2 + 6 * |u| + (5 / 2 : ℝ) * u ^ 2 ≤ 10 * (1 + u ^ 2) := by
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hmul := mul_le_mul_of_nonneg_left hpoly hs
  nlinarith only [hi, h1, h2, h3, h4, hsq, hsq1, hsq2, ha, hmul]

theorem bernoulliSquare_formula (p u : ℝ) :
    bernoulliSquare p u = 1 - 2 * p * (1 - p) * (1 - Real.cos u) := by
  unfold bernoulliSquare
  rw [← Complex.normSq_eq_norm_sq]
  simp only [rawBernoulliCF, realPhase, mul_one, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  nlinarith [mul_nonneg (sq_nonneg p) (sq_nonneg (Real.sin u)), Real.sin_sq_add_cos_sq u,
    congrArg (fun r : ℝ => p ^ 2 * r) (Real.sin_sq_add_cos_sq u)]

theorem bernoulliSquareSlope_formula (p u : ℝ) :
    bernoulliSquareSlope p u = -2 * p * (1 - p) * Real.sin u := by
  have h := (((Real.hasDerivAt_cos u).const_sub 1).const_mul (2 * p * (1 - p))).const_sub 1
  have h' : HasDerivAt (bernoulliSquare p) (-2 * p * (1 - p) * Real.sin u) u := by
    convert h using 1
    · funext x
      exact bernoulliSquare_formula p x
    · ring
  exact (bernoulliSquare_hasDerivAt p u).unique h'

theorem bernoulliSquareCurvature_formula (p u : ℝ) :
    bernoulliSquareCurvature p u = -2 * p * (1 - p) * Real.cos u := by
  have h := (Real.hasDerivAt_sin u).const_mul (-2 * p * (1 - p))
  have h' : HasDerivAt (bernoulliSquareSlope p) (-2 * p * (1 - p) * Real.cos u) u := by
    convert h using 1
    funext x
    exact bernoulliSquareSlope_formula p x
  exact (bernoulliSquareSlope_hasDerivAt p u).unique h'

end BerryEsseen
