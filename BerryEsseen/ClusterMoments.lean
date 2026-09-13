import BerryEsseen.UniformBlockLeakage
import BerryEsseen.ClusterCentralComparison

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace BerryEsseen

theorem integral_mixtureMeasure (μ ν : Measure ℝ) (p : ℝ) (hp : p ∈ Icc 0 1)
    (f : ℝ → ℝ) (hμ : Integrable f μ) (hν : Integrable f ν) :
    (∫ x, f x ∂mixtureMeasure μ ν p) = (1 - p) * (∫ x, f x ∂μ) + p * (∫ x, f x ∂ν) := by
  rw [mixtureMeasure, integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top) (hν.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.2 hp.2)]

theorem integral_twoClusterMeasure (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (f : ℝ → ℝ) (hf : Measurable f) (hP : Integrable f P.measure)
    (hQ : Integrable (fun x => f (1 + x)) Q.measure) :
    (∫ x, f x ∂twoClusterMeasure P Q p) =
      (1 - p) * (∫ x, f x ∂P.measure) + p * (∫ x, f (1 + x) ∂Q.measure) := by
  have hi : Integrable f (Q.measure.map (fun x => 1 + x)) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2 hQ
  rw [twoClusterMeasure, integral_mixtureMeasure _ _ p hp f hP hi,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

theorem CenteredFourthLaw.shifted_square_integrable (P : CenteredFourthLaw) (a : ℝ) :
    Integrable (fun x : ℝ => (x - a) ^ 2) P.measure := by
  convert ((P.integrable_pow 2 (by omega)).sub (P.first_integrable.const_mul (2 * a))).add (integrable_const (a ^ 2)) using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem CenteredFourthLaw.shifted_cube_integrable (P : CenteredFourthLaw) (a : ℝ) :
    Integrable (fun x : ℝ => (x - a) ^ 3) P.measure := by
  convert (((P.integrable_pow 3 (by omega)).sub ((P.integrable_pow 2 (by omega)).const_mul (3 * a))).add
    (P.first_integrable.const_mul (3 * a ^ 2))).sub (integrable_const (a ^ 3)) using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem CenteredFourthLaw.shifted_abs_cube_integrable (P : CenteredFourthLaw) (a : ℝ) :
    Integrable (fun x : ℝ => |x - a| ^ 3) P.measure := by
  simpa only [Real.norm_eq_abs, abs_pow] using (P.shifted_cube_integrable a).norm

theorem CenteredFourthLaw.shifted_square_integral (P : CenteredFourthLaw) (a : ℝ) :
    (∫ x, (x - a) ^ 2 ∂P.measure) = P.secondMoment + a ^ 2 := by
  have he : (fun x : ℝ => (x - a) ^ 2) = (fun x => x ^ 2 - 2 * a * x + a ^ 2) := by funext x; ring
  have hi : Integrable (fun x : ℝ => x ^ 2 - 2 * a * x) P.measure :=
    (P.integrable_pow 2 (by omega)).sub (P.first_integrable.const_mul _)
  rw [he, integral_add hi (integrable_const _),
    integral_sub (P.integrable_pow 2 (by omega)) (P.first_integrable.const_mul _), integral_const_mul,
    P.mean_zero, integral_const, probReal_univ, one_smul, mul_zero, sub_zero]
  rfl

def CenteredFourthLaw.thirdMoment (P : CenteredFourthLaw) : ℝ := ∫ x, x ^ 3 ∂P.measure

theorem CenteredFourthLaw.shifted_cube_integral (P : CenteredFourthLaw) (a : ℝ) :
    (∫ x, (x - a) ^ 3 ∂P.measure) = P.thirdMoment - 3 * a * P.secondMoment - a ^ 3 := by
  have h1 : Integrable (fun x : ℝ => x ^ 3 - 3 * a * x ^ 2) P.measure :=
    (P.integrable_pow 3 (by omega)).sub ((P.integrable_pow 2 (by omega)).const_mul _)
  have h2 : Integrable (fun x : ℝ => x ^ 3 - 3 * a * x ^ 2 + 3 * a ^ 2 * x) P.measure :=
    h1.add (P.first_integrable.const_mul _)
  have he : (fun x : ℝ => (x - a) ^ 3) = (fun x => (x ^ 3 - 3 * a * x ^ 2 + 3 * a ^ 2 * x) - a ^ 3) := by funext x; ring
  rw [he, integral_sub h2 (integrable_const _), integral_add h1 (P.first_integrable.const_mul _),
    integral_sub (P.integrable_pow 3 (by omega)) ((P.integrable_pow 2 (by omega)).const_mul _),
    integral_const_mul, integral_const_mul, P.mean_zero, integral_const, probReal_univ, one_smul, mul_zero, add_zero]
  rfl

theorem twoCluster_mean (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (∫ x, x ∂twoClusterMeasure P Q p) = p := by
  rw [integral_twoClusterMeasure P Q p hp (fun x => x) measurable_id P.first_integrable
    ((integrable_const 1).add Q.first_integrable), P.mean_zero,
    integral_add (integrable_const 1) Q.first_integrable, Q.mean_zero,
    integral_const, probReal_univ, one_smul]
  ring

theorem twoCluster_variance (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    (∫ x, (x - p) ^ 2 ∂twoClusterMeasure P Q p) =
      p * (1 - p) + (1 - p) * P.secondMoment + p * Q.secondMoment := by
  have he : (fun x : ℝ => (1 + x - p) ^ 2) = (fun x => (x - (p - 1)) ^ 2) := by funext x; ring
  have hQ : Integrable (fun x : ℝ => (1 + x - p) ^ 2) Q.measure := by rw [he]; exact Q.shifted_square_integrable _
  rw [integral_twoClusterMeasure P Q p hp (fun x => (x - p) ^ 2) (by fun_prop)
    (P.shifted_square_integrable p) hQ, he, P.shifted_square_integral, Q.shifted_square_integral]
  ring

theorem twoCluster_abs_third (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc 0 1)
    (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    (∫ x, |x - p| ^ 3 ∂twoClusterMeasure P Q p) =
      p * (1 - p) * (p ^ 2 + (1 - p) ^ 2) +
        (1 - p) * (3 * p * P.secondMoment - P.thirdMoment) +
        p * (3 * (1 - p) * Q.secondMoment + Q.thirdMoment) := by
  have he : (fun x : ℝ => |1 + x - p| ^ 3) = (fun x => |x - (p - 1)| ^ 3) := by
    funext x; congr 2; ring
  have hiQ : Integrable (fun x : ℝ => |1 + x - p| ^ 3) Q.measure := by rw [he]; exact Q.shifted_abs_cube_integrable _
  rw [integral_twoClusterMeasure P Q p hp (fun x => |x - p| ^ 3) (by fun_prop)
    (P.shifted_abs_cube_integrable p) hiQ, he]
  have hl : (∫ x, |x - p| ^ 3 ∂P.measure) = -(∫ x, (x - p) ^ 3 ∂P.measure) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hP] with x hx
    rw [abs_of_nonpos (by linarith [le_abs_self x] : x - p ≤ 0)]
    ring
  have hr : (∫ x, |x - (p - 1)| ^ 3 ∂Q.measure) = ∫ x, (x - (p - 1)) ^ 3 ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [hQ] with x hx
    rw [abs_of_nonneg (by linarith [neg_abs_le x] : 0 ≤ x - (p - 1))]
  rw [hl, hr, P.shifted_cube_integral, Q.shifted_cube_integral]
  ring

theorem CenteredFourthLaw.thirdMoment_bound (P : CenteredFourthLaw) (ε : ℝ)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) : |P.thirdMoment| ≤ ε * P.secondMoment := by
  have h := abs_integral_le_integral_abs (f := fun x : ℝ => x ^ 3) (μ := P.measure)
  apply h.trans
  change (∫ x, |x ^ 3| ∂P.measure) ≤ ε * (∫ x, x ^ 2 ∂P.measure)
  rw [← integral_const_mul]
  apply integral_mono_ae (P.integrable_pow 3 (by omega)).abs ((P.integrable_pow 2 (by omega)).const_mul ε)
  filter_upwards [hP] with x hx
  rw [abs_pow]
  have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  calc
    |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    _ ≤ ε * x ^ 2 := hh

theorem twoCluster_abs_third_error (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc 0 1)
    (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    |(∫ x, |x - p| ^ 3 ∂twoClusterMeasure P Q p) - p * (1 - p) * (p ^ 2 + (1 - p) ^ 2)| ≤
      (3 + ε) * ((1 - p) * P.secondMoment + p * Q.secondMoment) := by
  rw [twoCluster_abs_third P Q p ε hp hεp hεq hP hQ]
  have hq : 0 ≤ 1 - p := sub_nonneg.2 hp.2
  have hP0 := P.secondMoment_nonneg
  have hQ0 := Q.secondMoment_nonneg
  have hl := P.thirdMoment_bound ε hP
  have hr := Q.thirdMoment_bound ε hQ
  have hl' : |3 * p * P.secondMoment - P.thirdMoment| ≤ (3 + ε) * P.secondMoment := by
    have h := abs_sub (3 * p * P.secondMoment) P.thirdMoment
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.1) hP0)] at h
    have hmul := mul_le_mul_of_nonneg_right hp.2 hP0
    nlinarith
  have hr' : |3 * (1 - p) * Q.secondMoment + Q.thirdMoment| ≤ (3 + ε) * Q.secondMoment := by
    have h := abs_add_le (3 * (1 - p) * Q.secondMoment) Q.thirdMoment
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq) hQ0)] at h
    have hmul := mul_nonneg hp.1 hQ0
    nlinarith
  have h := abs_add_le ((1 - p) * (3 * p * P.secondMoment - P.thirdMoment))
    (p * (3 * (1 - p) * Q.secondMoment + Q.thirdMoment))
  simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg hp.1] at h
  have h1 := mul_le_mul_of_nonneg_left hl' hq
  have h2 := mul_le_mul_of_nonneg_left hr' hp.1
  have he : p * (1 - p) * (p ^ 2 + (1 - p) ^ 2) +
      (1 - p) * (3 * p * P.secondMoment - P.thirdMoment) +
      p * (3 * (1 - p) * Q.secondMoment + Q.thirdMoment) -
      p * (1 - p) * (p ^ 2 + (1 - p) ^ 2) =
      (1 - p) * (3 * p * P.secondMoment - P.thirdMoment) +
      p * (3 * (1 - p) * Q.secondMoment + Q.thirdMoment) := by ring
  rw [he]
  nlinarith only [h, h1, h2]

end BerryEsseen
