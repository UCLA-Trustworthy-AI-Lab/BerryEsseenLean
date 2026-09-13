import BerryEsseen.BoundedRawStandardization
import BerryEsseen.MeasureCharacteristicDerivativesCore

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem measureCharacteristicSquareCurvature_at_resonance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (u : ℝ) (hu : u ∈ resonanceSubgroup μ) :
    measureCharacteristicSquareCurvature μ u = -2 * rawStdDev μ ^ 2 := by
  have hw1 := weightedCharFun_at_resonance μ u hu 1
  have hw2 := weightedCharFun_at_resonance μ u hu 2
  simp only [pow_one] at hw1
  have hn := (mem_resonanceSubgroup_iff μ u).mp hu
  have hn2 : (charFun μ u).re ^ 2 + (charFun μ u).im ^ 2 = 1 := by
    have hsq := congrArg (fun x : ℝ => x ^ 2) hn
    simpa only [Complex.sq_norm, Complex.normSq_apply, one_pow, ← sq] using hsq
  rw [raw_centered_variance_formula μ h1 h2]
  unfold measureCharacteristicSquareCurvature measureCharFunDerivative rawMean
  rw [hw1, hw2]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    map_neg, map_mul, Complex.conj_re, Complex.conj_im, zero_mul, mul_zero, one_mul, sub_zero,
    zero_sub, add_zero, zero_add, neg_neg]
  calc
    _ = (-2 * (∫ x : ℝ, x ^ 2 ∂μ) + 2 * (∫ x : ℝ, x ∂μ) ^ 2) *
        ((charFun μ u).re ^ 2 + (charFun μ u).im ^ 2) := by ring
    _ = _ := by rw [hn2]; ring

end BerryEsseen
