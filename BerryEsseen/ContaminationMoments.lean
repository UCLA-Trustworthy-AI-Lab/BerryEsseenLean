import BerryEsseen.Statement
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Tactic

/-! Actual moment formulas for the contaminated probability measure, and
differentiation under its third-absolute-moment integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

def contaminatedMeasure (P : StandardizedLaw) (y e : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - e) • P.measure + ENNReal.ofReal e • Measure.dirac y

theorem contaminatedMeasure_zero (P : StandardizedLaw) (y : ℝ) :
    contaminatedMeasure P y 0 = P.measure := by simp [contaminatedMeasure]

theorem contaminatedMeasure_probability (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Icc 0 1) : IsProbabilityMeasure (contaminatedMeasure P y e) := by
  constructor
  simp only [contaminatedMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr he.2) he.1]
  norm_num

theorem integral_contaminatedMeasure (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Icc 0 1) {f : ℝ → ℝ} (hf : Integrable f P.measure) :
    (∫ x, f x ∂contaminatedMeasure P y e) =
      (1 - e) * (∫ x, f x ∂P.measure) + e * f y := by
  have h1 : Integrable f (ENNReal.ofReal (1 - e) • P.measure) :=
    hf.smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable f (ENNReal.ofReal e • Measure.dirac y) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [contaminatedMeasure, integral_add_measure h1 h2]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (sub_nonneg.mpr he.2),
    ENNReal.toReal_ofReal he.1, integral_dirac, smul_eq_mul]

theorem contaminated_mean (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Icc 0 1) :
    (∫ x, x ∂contaminatedMeasure P y e) = e * y := by
  rw [integral_contaminatedMeasure P y he P.first_integrable, P.mean_zero]
  ring

theorem contaminated_raw_second (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Icc 0 1) :
    (∫ x, x ^ 2 ∂contaminatedMeasure P y e) = 1 + e * (y ^ 2 - 1) := by
  rw [integral_contaminatedMeasure P y he P.second_integrable, P.second_one]
  ring

theorem hasDerivAt_abs_cube (x : ℝ) :
    HasDerivAt (fun t : ℝ => |t| ^ 3) (3 * x * |x|) x := by
  convert hasDerivAt_abs_rpow x (p := 3) (by norm_num) using 1
  · funext t
    exact (Real.rpow_natCast |t| 3).symm
  · norm_num
    ring

theorem hasDerivAt_shifted_abs_cube (x y e : ℝ) :
    HasDerivAt (fun t : ℝ => |x - t * y| ^ 3)
      (-3 * y * (x - e * y) * |x - e * y|) e := by
  convert (hasDerivAt_abs_cube (x - e * y)).comp e
    ((hasDerivAt_const e x).sub ((hasDerivAt_id e).mul_const y)) using 1
  ring

theorem shifted_abs_cube_derivative_bound (x y e : ℝ) (he : |e| ≤ 1) :
    ‖-3 * y * (x - e * y) * |x - e * y|‖ ≤ 6 * |y| * (x ^ 2 + y ^ 2) := by
  have he2 : e ^ 2 ≤ 1 := by
    have h := sq_le_sq₀ (abs_nonneg e) (by norm_num : (0 : ℝ) ≤ 1)
    have h' := h.mpr he
    simpa only [sq_abs, one_pow] using h'
  have hmul := mul_le_mul_of_nonneg_right he2 (sq_nonneg y)
  have hs : (x - e * y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x + e * y)]
  have hn : ‖-3 * y * (x - e * y) * |x - e * y|‖ =
      3 * |y| * (x - e * y) ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_abs]
    norm_num
    calc
      3 * |y| * |x - e * y| * |x - e * y| = 3 * |y| * |x - e * y| ^ 2 := by ring
      _ = _ := by rw [sq_abs]
  rw [hn]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 3 * |y|)]

def signedSecondMoment (P : StandardizedLaw) : ℝ := ∫ x, x * |x| ∂P.measure

theorem signedSecond_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x * |x|) P.measure := by
  refine P.second_integrable.mono' (by fun_prop) ?_
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, abs_mul, abs_abs]
  nlinarith [sq_abs x]

theorem shifted_abs_cube_integral_derivative (P : StandardizedLaw) (y : ℝ) :
    HasDerivAt (fun e : ℝ => ∫ x, |x - e * y| ^ 3 ∂P.measure)
      (-3 * y * signedSecondMoment P) 0 := by
  let F : ℝ → ℝ → ℝ := fun e x => |x - e * y| ^ 3
  let F' : ℝ → ℝ → ℝ := fun e x => -3 * y * (x - e * y) * |x - e * y|
  let bound : ℝ → ℝ := fun x => 6 * |y| * (x ^ 2 + y ^ 2)
  have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ᶠ e in 𝓝 (0 : ℝ), AEStronglyMeasurable (F e) P.measure :=
    Eventually.of_forall (fun e => by dsimp [F]; fun_prop)
  have hint : Integrable (F 0) P.measure := by simpa [F] using P.third_integrable
  have hmeas' : AEStronglyMeasurable (F' 0) P.measure := by dsimp [F']; fun_prop
  have hb : ∀ᵐ x ∂P.measure, ∀ e ∈ Ioo (-1 : ℝ) 1, ‖F' e x‖ ≤ bound x := by
    filter_upwards [] with x e he
    exact shifted_abs_cube_derivative_bound x y e (abs_le.mpr ⟨he.1.le, he.2.le⟩)
  have hbi : Integrable bound P.measure :=
    (P.second_integrable.add (integrable_const (y ^ 2))).const_mul (6 * |y|)
  have hdiff : ∀ᵐ x ∂P.measure, ∀ e ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t => F t x) (F' e x) e := by
    filter_upwards [] with x e _
    exact hasDerivAt_shifted_abs_cube x y e
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hmeas'
    hb hbi hdiff).2
  have he : (∫ x, F' 0 x ∂P.measure) = -3 * y * signedSecondMoment P := by
    simp only [F', zero_mul, sub_zero]
    simp_rw [mul_assoc (-3 * y)]
    rw [integral_const_mul]
    rfl
  rw [he] at hh
  exact hh

def contaminationThirdExtension (P : StandardizedLaw) (y e : ℝ) : ℝ :=
  (1 - e) * (∫ x, |x - e * y| ^ 3 ∂P.measure) + e * |(1 - e) * y| ^ 3

theorem contaminationThirdExtension_zero (P : StandardizedLaw) (y : ℝ) :
    contaminationThirdExtension P y 0 = thirdMoment P := by
  simp [contaminationThirdExtension, thirdMoment]

theorem contaminationThirdExtension_derivative (P : StandardizedLaw) (y : ℝ) :
    HasDerivAt (contaminationThirdExtension P y)
      (|y| ^ 3 - thirdMoment P - 3 * y * signedSecondMoment P) 0 := by
  have hi := shifted_abs_cube_integral_derivative P y
  have hj : HasDerivAt (fun e : ℝ => |(1 - e) * y| ^ 3) (-3 * y * y * |y|) 0 := by
    convert hasDerivAt_shifted_abs_cube y y 0 using 1
    · funext e
      rw [show (1 - e) * y = y - e * y by ring]
    · simp
  convert (((hasDerivAt_const 0 1).sub (hasDerivAt_id 0)).mul hi).add
    ((hasDerivAt_id 0).mul hj) using 1
  dsimp [thirdMoment]
  simp only [zero_mul, sub_zero, one_mul, add_zero]
  ring

theorem shifted_abs_cube_bound (x a : ℝ) : |x - a| ^ 3 ≤ 4 * (|x| ^ 3 + |a| ^ 3) := by
  have h1 : |x - a| ≤ |x| + |a| := abs_sub x a
  have h2 := pow_le_pow_left₀ (abs_nonneg (x - a)) h1 3
  have h3 := mul_nonneg (add_nonneg (abs_nonneg x) (abs_nonneg a))
    (sq_nonneg (|x| - |a|))
  nlinarith

theorem shifted_abs_cube_integrable (P : StandardizedLaw) (a : ℝ) :
    Integrable (fun x : ℝ => |x - a| ^ 3) P.measure := by
  refine ((P.third_integrable.add (integrable_const (|a| ^ 3))).const_mul 4).mono'
    (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |x - a| ^ 3)]
  exact shifted_abs_cube_bound x a

theorem shifted_second_integrable (P : StandardizedLaw) (a : ℝ) :
    Integrable (fun x : ℝ => (x - a) ^ 2) P.measure := by
  have h := (P.second_integrable.sub (P.first_integrable.const_mul (2 * a))).add
    (integrable_const (a ^ 2))
  convert h using 1
  funext x
  dsimp
  ring

theorem shifted_second_integral (P : StandardizedLaw) (a : ℝ) :
    (∫ x, (x - a) ^ 2 ∂P.measure) = 1 + a ^ 2 := by
  have he : (fun x : ℝ => (x - a) ^ 2) = (fun x => x ^ 2 - 2 * a * x + a ^ 2) := by
    funext x; ring
  have hi : Integrable (fun x : ℝ => x ^ 2 - 2 * a * x) P.measure :=
    P.second_integrable.sub (P.first_integrable.const_mul (2 * a))
  rw [he, integral_add hi (integrable_const (a ^ 2)),
    integral_sub P.second_integrable (P.first_integrable.const_mul (2 * a)),
    integral_const_mul, P.second_one, P.mean_zero]
  simp

def contaminatedVariance (P : StandardizedLaw) (y e : ℝ) : ℝ :=
  ∫ x, (x - ∫ z, z ∂contaminatedMeasure P y e) ^ 2 ∂contaminatedMeasure P y e

def contaminatedThird (P : StandardizedLaw) (y e : ℝ) : ℝ :=
  ∫ x, |x - ∫ z, z ∂contaminatedMeasure P y e| ^ 3 ∂contaminatedMeasure P y e

theorem contaminated_variance_formula (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Icc 0 1) :
    contaminatedVariance P y e = 1 + e * (y ^ 2 - 1) - e ^ 2 * y ^ 2 := by
  rw [contaminatedVariance, contaminated_mean P y he,
    integral_contaminatedMeasure P y he (shifted_second_integrable P (e * y)),
    shifted_second_integral]
  ring

theorem contaminated_third_formula (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Icc 0 1) :
    contaminatedThird P y e = contaminationThirdExtension P y e := by
  rw [contaminatedThird, contaminated_mean P y he,
    integral_contaminatedMeasure P y he (shifted_abs_cube_integrable P (e * y))]
  unfold contaminationThirdExtension
  rw [show y - e * y = (1 - e) * y by ring]

theorem contaminated_mean_right_derivative (P : StandardizedLaw) (y : ℝ) :
    HasDerivWithinAt (fun e => ∫ x, x ∂contaminatedMeasure P y e) y (Icc 0 1) 0 := by
  have h : HasDerivAt (fun e : ℝ => e * y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const y
  exact h.hasDerivWithinAt.congr_of_mem (fun e he => contaminated_mean P y he) (by norm_num)

theorem contaminated_variance_right_derivative (P : StandardizedLaw) (y : ℝ) :
    HasDerivWithinAt (contaminatedVariance P y) (y ^ 2 - 1) (Icc 0 1) 0 := by
  have h : HasDerivAt (fun e : ℝ => 1 + e * (y ^ 2 - 1) - e ^ 2 * y ^ 2)
      (y ^ 2 - 1) 0 := by
    convert ((hasDerivAt_const 0 1).add ((hasDerivAt_id 0).mul_const (y ^ 2 - 1))).sub
      (((hasDerivAt_id 0).pow 2).mul_const (y ^ 2)) using 1
    simp
  exact h.hasDerivWithinAt.congr_of_mem (fun e he => contaminated_variance_formula P y he)
    (by norm_num)

theorem contaminated_third_right_derivative (P : StandardizedLaw) (y : ℝ) :
    HasDerivWithinAt (contaminatedThird P y)
      (|y| ^ 3 - thirdMoment P - 3 * y * signedSecondMoment P) (Icc 0 1) 0 := by
  exact (contaminationThirdExtension_derivative P y).hasDerivWithinAt.congr_of_mem
    (fun e he => contaminated_third_formula P y he) (by norm_num)

end BerryEsseen
