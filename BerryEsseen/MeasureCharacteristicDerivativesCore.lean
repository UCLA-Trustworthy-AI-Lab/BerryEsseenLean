import BerryEsseen.CharacteristicDerivatives

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def measureCharFunDerivative (μ : Measure ℝ) (u : ℝ) : ℂ := Complex.I * weightedCharFun μ 1 u
def measureCharacteristicSquare (μ : Measure ℝ) (u : ℝ) : ℝ := ‖charFun μ u‖ ^ 2
def measureCharacteristicSquareSlope (μ : Measure ℝ) (u : ℝ) : ℝ :=
  2 * inner ℝ (charFun μ u) (measureCharFunDerivative μ u)
def measureCharacteristicSquareCurvature (μ : Measure ℝ) (u : ℝ) : ℝ :=
  2 * (inner ℝ (charFun μ u) (-weightedCharFun μ 2 u) +
    inner ℝ (measureCharFunDerivative μ u) (measureCharFunDerivative μ u))
def measureCharacteristicSquareThird (μ : Measure ℝ) (u : ℝ) : ℝ :=
  2 * (inner ℝ (charFun μ u) (-Complex.I * weightedCharFun μ 3 u) +
    3 * inner ℝ (measureCharFunDerivative μ u) (-weightedCharFun μ 2 u))

theorem measure_charFun_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (u : ℝ) :
    HasDerivAt (charFun μ) (measureCharFunDerivative μ u) u := by
  have hi0 : Integrable (fun x : ℝ => x ^ 0) μ := by simpa using integrable_const (1 : ℝ)
  have hi1 : Integrable (fun x : ℝ => x ^ (0 + 1)) μ := by simpa using h1
  have hd := weightedCharFun_hasDerivAt μ 0 hi0 hi1 u
  convert hd using 1
  funext t
  exact (weightedCharFun_zero μ t).symm

theorem measure_charFunDerivative_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (u : ℝ) :
    HasDerivAt (measureCharFunDerivative μ) (-weightedCharFun μ 2 u) u := by
  have hi1 : Integrable (fun x : ℝ => x ^ 1) μ := by simpa using h1
  have hd := (weightedCharFun_hasDerivAt μ 1 hi1 h2 u).const_mul Complex.I
  simpa only [measureCharFunDerivative, ← mul_assoc, Complex.I_mul_I, neg_one_mul] using hd

theorem measureCharacteristicSquare_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (u : ℝ) :
    HasDerivAt (measureCharacteristicSquare μ) (measureCharacteristicSquareSlope μ u) u :=
  (measure_charFun_hasDerivAt μ h1 u).norm_sq

theorem measureCharacteristicSquareSlope_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ) (u : ℝ) :
    HasDerivAt (measureCharacteristicSquareSlope μ) (measureCharacteristicSquareCurvature μ u) u :=
  ((measure_charFun_hasDerivAt μ h1 u).inner ℝ (measure_charFunDerivative_hasDerivAt μ h1 h2 u)).const_mul 2

theorem measureCharacteristicSquareCurvature_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (h3 : Integrable (fun x : ℝ => x ^ 3) μ) (u : ℝ) :
    HasDerivAt (measureCharacteristicSquareCurvature μ) (measureCharacteristicSquareThird μ u) u := by
  have hd2 := (weightedCharFun_hasDerivAt μ 2 h2 h3 u).neg
  have hd := (((measure_charFun_hasDerivAt μ h1 u).inner ℝ hd2).add
    ((measure_charFunDerivative_hasDerivAt μ h1 h2 u).inner ℝ
      (measure_charFunDerivative_hasDerivAt μ h1 h2 u))).const_mul 2
  convert hd using 1
  change 2 * (inner ℝ (charFun μ u) (-Complex.I * weightedCharFun μ 3 u) +
    3 * inner ℝ (measureCharFunDerivative μ u) (-weightedCharFun μ 2 u)) =
    2 * (inner ℝ (charFun μ u) (-(Complex.I * weightedCharFun μ 3 u)) +
      inner ℝ (measureCharFunDerivative μ u) (-weightedCharFun μ 2 u) +
      (inner ℝ (measureCharFunDerivative μ u) (-weightedCharFun μ 2 u) +
        inner ℝ (-weightedCharFun μ 2 u) (measureCharFunDerivative μ u)))
  rw [real_inner_comm (-weightedCharFun μ 2 u) (measureCharFunDerivative μ u), neg_mul]
  ring

theorem measureCharacteristicSquareSlope_at_resonance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (hu : u ∈ resonanceSubgroup μ) : measureCharacteristicSquareSlope μ u = 0 := by
  have h1 := weightedCharFun_at_resonance μ u hu 1
  simp only [pow_one] at h1
  unfold measureCharacteristicSquareSlope measureCharFunDerivative
  rw [h1]
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring


end BerryEsseen
