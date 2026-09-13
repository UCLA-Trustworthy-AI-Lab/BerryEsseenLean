import BerryEsseen.WeightedCharacteristicLimits

/-! A uniform Lipschitz bound for q'' using third absolute moments only. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem norm_weightedCharFun_le (μ : Measure ℝ) (k : ℕ) (u : ℝ) :
    ‖weightedCharFun μ k u‖ ≤ ∫ x : ℝ, |x| ^ k ∂μ := by
  have h := norm_integral_le_integral_norm (fun x : ℝ => (x : ℂ) ^ k * realPhase u x) (μ := μ)
  simpa only [weightedCharFun, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    realPhase_norm, mul_one] using h

theorem norm_weightedCharFun_one_le (P : StandardizedLaw) (u : ℝ) :
    ‖weightedCharFun P.measure 1 u‖ ≤ 2 := by
  calc
    _ ≤ ∫ x : ℝ, |x| ∂P.measure := by simpa only [pow_one] using norm_weightedCharFun_le P.measure 1 u
    _ ≤ ∫ x : ℝ, x ^ 2 + 1 ∂P.measure := by
      apply integral_mono P.first_integrable.abs (P.second_integrable.add (integrable_const _))
      intro x
      change |x| ≤ x ^ 2 + 1
      nlinarith [sq_nonneg (|x| - 1), sq_abs x]
    _ = 2 := by rw [integral_add P.second_integrable (integrable_const _), P.second_one]; norm_num

theorem norm_weightedCharFun_two_le (P : StandardizedLaw) (u : ℝ) :
    ‖weightedCharFun P.measure 2 u‖ ≤ 1 := by
  simpa only [sq_abs, P.second_one] using norm_weightedCharFun_le P.measure 2 u

theorem norm_weightedCharFun_three_le (P : StandardizedLaw) (u : ℝ) :
    ‖weightedCharFun P.measure 3 u‖ ≤ thirdMoment P := norm_weightedCharFun_le _ _ _

theorem charFunDerivative_norm_le (P : StandardizedLaw) (u : ℝ) : ‖charFunDerivative P u‖ ≤ 2 := by
  rw [charFunDerivative, norm_mul, Complex.norm_I, one_mul]
  exact norm_weightedCharFun_one_le P u

def characteristicSquareThird (P : StandardizedLaw) (u : ℝ) : ℝ :=
  2 * (inner ℝ (charFun P.measure u) (-Complex.I * weightedCharFun P.measure 3 u) +
    3 * inner ℝ (charFunDerivative P u) (-weightedCharFun P.measure 2 u))

theorem characteristicSquareCurvature_hasDerivAt (P : StandardizedLaw) (u : ℝ) :
    HasDerivAt (characteristicSquareCurvature P) (characteristicSquareThird P u) u := by
  have hd2 := (weightedCharFun_hasDerivAt P.measure 2 P.second_integrable
    (signedThirdMoment_integrable P) u).neg
  have hd := (((charFun_hasDerivAt P u).inner ℝ hd2).add
    ((charFunDerivative_hasDerivAt P u).inner ℝ (charFunDerivative_hasDerivAt P u))).const_mul 2
  convert hd using 1
  change 2 * (inner ℝ (charFun P.measure u) (-Complex.I * weightedCharFun P.measure 3 u) +
      3 * inner ℝ (charFunDerivative P u) (-weightedCharFun P.measure 2 u)) =
    2 * (inner ℝ (charFun P.measure u) (-(Complex.I * weightedCharFun P.measure 3 u)) +
      inner ℝ (charFunDerivative P u) (-weightedCharFun P.measure 2 u) +
      (inner ℝ (charFunDerivative P u) (-weightedCharFun P.measure 2 u) +
       inner ℝ (-weightedCharFun P.measure 2 u) (charFunDerivative P u)))
  rw [real_inner_comm (-weightedCharFun P.measure 2 u) (charFunDerivative P u), neg_mul]
  ring

theorem characteristicSquareThird_abs_le (P : StandardizedLaw) (u : ℝ) :
    |characteristicSquareThird P u| ≤ 12 + 2 * thirdMoment P := by
  have hf : ‖charFun P.measure u‖ ≤ 1 := norm_charFun_le_one u
  have hd := charFunDerivative_norm_le P u
  have h2 := norm_weightedCharFun_two_le P u
  have h3 := norm_weightedCharFun_three_le P u
  have hfirst : |inner ℝ (charFun P.measure u) (-Complex.I * weightedCharFun P.measure 3 u)| ≤ thirdMoment P := by
    have hi := abs_real_inner_le_norm (charFun P.measure u) (-Complex.I * weightedCharFun P.measure 3 u)
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul] at hi
    exact hi.trans (by nlinarith [mul_le_mul hf h3 (norm_nonneg _) (by positivity : 0 ≤ (1 : ℝ))])
  have hsecond : |inner ℝ (charFunDerivative P u) (-weightedCharFun P.measure 2 u)| ≤ 2 := by
    have hi := abs_real_inner_le_norm (charFunDerivative P u) (-weightedCharFun P.measure 2 u)
    rw [norm_neg] at hi
    exact hi.trans (by nlinarith [mul_le_mul hd h2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)])
  unfold characteristicSquareThird
  rw [abs_mul]
  have ht := abs_add_le
    (inner ℝ (charFun P.measure u) (-Complex.I * weightedCharFun P.measure 3 u))
    (3 * inner ℝ (charFunDerivative P u) (-weightedCharFun P.measure 2 u))
  rw [abs_mul] at ht
  simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ht ⊢
  linarith

theorem characteristicSquare_lipschitz (P : StandardizedLaw) : LipschitzWith 4 (characteristicSquare P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (characteristicSquare_hasDerivAt P u).hasDerivWithinAt)
    (fun u _ => show ‖characteristicSquareSlope P u‖ ≤ (4 : ℝ) by
      unfold characteristicSquareSlope
      rw [Real.norm_eq_abs, abs_mul]
      have hi := abs_real_inner_le_norm (charFun P.measure u) (charFunDerivative P u)
      have hp := mul_le_mul (norm_charFun_le_one (μ := P.measure) u) (charFunDerivative_norm_le P u)
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith)
    (mem_univ y) (mem_univ x)
  simpa only [dist_eq_norm, Real.norm_eq_abs] using h

theorem characteristicSquareCurvature_lipschitz (P : StandardizedLaw) (B : ℝ)
    (hB : thirdMoment P ≤ B) :
    LipschitzWith ⟨12 + 2 * B, by have := thirdMoment_pos P; linarith⟩
      (characteristicSquareCurvature P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (characteristicSquareCurvature_hasDerivAt P u).hasDerivWithinAt)
    (fun u _ => show ‖characteristicSquareThird P u‖ ≤ 12 + 2 * B by
      rw [Real.norm_eq_abs]
      exact (characteristicSquareThird_abs_le P u).trans (by linarith))
    (mem_univ y) (mem_univ x)
  simpa only [dist_eq_norm, Real.norm_eq_abs] using h

theorem weak_charFun_tendsto (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure)) (u : ℝ) :
    Tendsto (fun j => charFun (P j).measure u) atTop (𝓝 (charFun Q.measure u)) := by
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hw
    (BoundedContinuousFunction.innerProbChar u)
  simpa only [charFun_eq_integral_innerProbChar] using hh

theorem weak_characteristicSquare_tendsto (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure)) (u : ℝ) :
    Tendsto (fun j => characteristicSquare (P j) u) atTop (𝓝 (characteristicSquare Q u)) :=
  ((weak_charFun_tendsto P Q hw u).norm).pow 2

theorem weak_characteristicSquareCurvature_tendsto (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (u : ℝ) :
    Tendsto (fun j => characteristicSquareCurvature (P j) u) atTop (𝓝 (characteristicSquareCurvature Q u)) := by
  have h0 := weak_charFun_tendsto P Q hw u
  have h1 := (weak_weightedCharFun_first P Q hw u).const_mul Complex.I
  have h2 := weak_weightedCharFun_second P Q hw B hB u
  exact ((h0.inner (𝕜 := ℝ) h2.neg).add (h1.inner (𝕜 := ℝ) h1)).const_mul 2

end BerryEsseen
