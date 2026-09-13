import BerryEsseen.ContaminationMoments
import BerryEsseen.SupportContact
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-! CDF convolution identities and contact for the actual influence numerator.
The nonpositive variational inequality remains an explicit premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem probability_cdf_upperSemicontinuous (μ : Measure ℝ) :
    UpperSemicontinuous (cdf μ) := by
  intro x z hz
  rw [← nhdsLE_sup_nhdsGE x, eventually_sup]
  constructor
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact lt_of_le_of_lt (monotone_cdf μ ha) hz
  · exact (cdf μ).right_continuous x |>.upperSemicontinuousWithinAt z hz

theorem cdf_convolution_integral (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
    cdf (μ ∗ ν) t = ∫ x, cdf ν (t - x) ∂μ := by
  have hi : Integrable ((Iic t).indicator (fun _ : ℝ => (1 : ℝ))) (μ ∗ ν) :=
    (integrable_const 1).indicator measurableSet_Iic
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  change (∫ x, (Iic t).indicator (fun _ : ℝ => (1 : ℝ)) x ∂(μ ∗ ν)) = _
  rw [integral_conv hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [cdf_eq_real, ← integral_indicator_one measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [indicator_apply, mem_Iic, Pi.one_apply]
  simp only [show x + y ≤ t ↔ y ≤ t - x by constructor <;> intro h <;> linarith]

theorem sum_cdf_convolution_integral (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    (∫ x, cdf (iidSumLaw P.measure n) (t - x) ∂P.measure) =
      cdf (iidSumLaw P.measure (n + 1)) t := by
  exact (cdf_convolution_integral P.measure (iidSumLaw P.measure n) t).symm

theorem translated_cdf_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x => cdf ν (t - x)) μ := by
  refine (integrable_const (1 : ℝ)).mono' ?_ ?_
  · exact ((monotone_cdf ν).measurable.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg ν _)]
    exact cdf_le_one ν _

def influenceNumerator (P : StandardizedLaw) (n : ℕ) (t s z φ R y : ℝ) : ℝ :=
  s ^ 3 * (cdf (iidSumLaw P.measure n) (t - y) - cdf (iidSumLaw P.measure (n + 1)) t)
    + s ^ 2 * φ * y
    + (s / 2 * z * φ + 3 / 2 * R * thirdMoment P) * (y ^ 2 - 1)
    - R * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y)

theorem influenceNumerator_integrable (P : StandardizedLaw) (n : ℕ) (t s z φ R : ℝ) :
    Integrable (influenceNumerator P n t s z φ R) P.measure := by
  have h1 := ((translated_cdf_integrable P.measure (iidSumLaw P.measure n) t).sub
    (integrable_const (cdf (iidSumLaw P.measure (n + 1)) t))).const_mul (s ^ 3)
  have h2 := P.first_integrable.const_mul (s ^ 2 * φ)
  have h3 := (P.second_integrable.sub (integrable_const 1)).const_mul
    (s / 2 * z * φ + 3 / 2 * R * thirdMoment P)
  have h4 := ((P.third_integrable.sub (integrable_const (thirdMoment P))).sub
    (P.first_integrable.const_mul (3 * signedSecondMoment P))).const_mul R
  exact ((h1.add h2).add h3).sub h4

theorem influenceNumerator_integral_zero (P : StandardizedLaw) (n : ℕ) (t s z φ R : ℝ) :
    (∫ y, influenceNumerator P n t s z φ R y ∂P.measure) = 0 := by
  let g : ℝ → ℝ := fun y =>
    s ^ 3 * (cdf (iidSumLaw P.measure n) (t - y) - cdf (iidSumLaw P.measure (n + 1)) t)
  let h : ℝ → ℝ := fun y => s ^ 2 * φ * y
  let j : ℝ → ℝ := fun y =>
    (s / 2 * z * φ + 3 / 2 * R * thirdMoment P) * (y ^ 2 - 1)
  let k : ℝ → ℝ := fun y => R * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y)
  have hg : Integrable g P.measure :=
    ((translated_cdf_integrable P.measure (iidSumLaw P.measure n) t).sub
      (integrable_const _)).const_mul _
  have hh : Integrable h P.measure := P.first_integrable.const_mul _
  have hj : Integrable j P.measure := (P.second_integrable.sub (integrable_const 1)).const_mul _
  have hk : Integrable k P.measure :=
    ((P.third_integrable.sub (integrable_const _)).sub
      (P.first_integrable.const_mul _)).const_mul _
  have hg0 : (∫ y, g y ∂P.measure) = 0 := by
    dsimp [g]
    rw [integral_const_mul,
      integral_sub (translated_cdf_integrable P.measure (iidSumLaw P.measure n) t)
        (integrable_const _), sum_cdf_convolution_integral]
    simp
  have hh0 : (∫ y, h y ∂P.measure) = 0 := by
    dsimp [h]
    rw [integral_const_mul, P.mean_zero, mul_zero]
  have hj0 : (∫ y, j y ∂P.measure) = 0 := by
    dsimp [j]
    rw [integral_const_mul, integral_sub P.second_integrable (integrable_const 1), P.second_one]
    simp
  have hk0 : (∫ y, k y ∂P.measure) = 0 := by
    dsimp [k]
    have ht : Integrable (fun y : ℝ => |y| ^ 3 - thirdMoment P) P.measure :=
      P.third_integrable.sub (integrable_const _)
    rw [integral_const_mul, integral_sub ht (P.first_integrable.const_mul _),
      integral_sub P.third_integrable (integrable_const _), integral_const_mul, P.mean_zero]
    simp [thirdMoment]
  change (∫ y, g y + h y + j y - k y ∂P.measure) = 0
  have hgh : Integrable (fun y => g y + h y) P.measure := hg.add hh
  have hghj : Integrable (fun y => g y + h y + j y) P.measure := hgh.add hj
  rw [integral_sub hghj hk, integral_add hgh hj, integral_add hg hh, hg0, hh0, hj0, hk0]
  ring

theorem influenceNumerator_upperSemicontinuous (P : StandardizedLaw) (n : ℕ)
    (t s z φ R : ℝ) (hs : 0 ≤ s) :
    UpperSemicontinuous (influenceNumerator P n t s z φ R) := by
  have hc : UpperSemicontinuous (fun y => cdf (iidSumLaw P.measure n) (t - y)) :=
    (probability_cdf_upperSemicontinuous _).comp (by fun_prop)
  have ha : Continuous (fun x : ℝ => s ^ 3 * (x - cdf (iidSumLaw P.measure (n + 1)) t)) :=
    by fun_prop
  have hmono : Monotone (fun x : ℝ => s ^ 3 * (x - cdf (iidSumLaw P.measure (n + 1)) t)) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hab _) (pow_nonneg hs _)
  have hhead := ha.comp_upperSemicontinuous hc hmono
  have htail : Continuous (fun y : ℝ => s ^ 2 * φ * y +
      (s / 2 * z * φ + 3 / 2 * R * thirdMoment P) * (y ^ 2 - 1) -
      R * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y)) := by fun_prop
  convert hhead.add htail.upperSemicontinuous using 1
  funext y
  dsimp [influenceNumerator]
  ring

/-- The actual convolution expression is zero on the entire support once
the variational inequality has been established. No integral or continuity
premise is hidden here. -/
theorem influenceNumerator_contact (P : StandardizedLaw) (n : ℕ)
    (t s z φ R : ℝ) (hs : 0 ≤ s)
    (hmax : ∀ y, influenceNumerator P n t s z φ R y ≤ 0) :
    ∀ y ∈ P.measure.support, influenceNumerator P n t s z φ R y = 0 := by
  exact contact_on_entire_support P.measure _
    (influenceNumerator_integrable P n t s z φ R) hmax
    (influenceNumerator_integral_zero P n t s z φ R)
    (influenceNumerator_upperSemicontinuous P n t s z φ R hs)

end BerryEsseen
