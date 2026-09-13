import BerryEsseen.ConvolutionContact

/-! A finite-convolution contamination derivative. A recursive polynomial
extension acts on bounded measurable test functions, so differentiation never
acts on the CDF threshold and requires no regularity of the summand law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def testAverage (μ : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ z, f (x + z) ∂μ
def testShift (y : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + y)

theorem testAverage_shift_comm (μ : Measure ℝ) (y : ℝ) (f : ℝ → ℝ) :
    testAverage μ (testShift y f) = testShift y (testAverage μ f) := by
  funext x
  dsimp [testAverage, testShift]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [add_right_comm x z y]

def contaminationExpectation (μ : Measure ℝ) (y : ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, _ => f 0
  | n + 1, f, e => (1 - e) * contaminationExpectation μ y n (testAverage μ f) e +
      e * contaminationExpectation μ y n (testShift y f) e

theorem contaminationExpectation_zero_succ (μ : Measure ℝ) (y : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    contaminationExpectation μ y (n + 1) f 0 =
      contaminationExpectation μ y n (testAverage μ f) 0 := by
  simp [contaminationExpectation]

theorem contaminationExpectation_derivative (μ : Measure ℝ) (y : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    HasDerivAt (contaminationExpectation μ y (n + 1) f)
      ((n + 1 : ℝ) * (contaminationExpectation μ y n (testShift y f) 0 -
        contaminationExpectation μ y (n + 1) f 0)) 0 := by
  induction n generalizing f with
  | zero =>
    convert (((hasDerivAt_const 0 1).sub (hasDerivAt_id 0)).mul_const
      (testAverage μ f 0)).add ((hasDerivAt_id 0).mul_const (testShift y f 0)) using 1
    simp [contaminationExpectation]
    ring
  | succ n ih =>
    have h := (((hasDerivAt_const 0 1).sub (hasDerivAt_id 0)).mul (ih (testAverage μ f))).add
      ((hasDerivAt_id 0).mul (ih (testShift y f)))
    convert h using 1
    dsimp
    simp only [zero_mul, one_mul, sub_zero, add_zero,
      contaminationExpectation_zero_succ]
    rw [← testAverage_shift_comm]
    push_cast
    ring

def BoundedMeasurableTest (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

theorem boundedMeasurableTest_integrable {f : ℝ → ℝ} (hf : BoundedMeasurableTest f)
    (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨hm, C, hC⟩ := hf
  exact (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall hC)

theorem boundedMeasurableTest_shift {f : ℝ → ℝ} (hf : BoundedMeasurableTest f) (y : ℝ) :
    BoundedMeasurableTest (testShift y f) := by
  obtain ⟨hm, C, hC⟩ := hf
  exact ⟨hm.comp (by fun_prop), C, fun x => hC (x + y)⟩

theorem boundedMeasurableTest_average {f : ℝ → ℝ} (hf : BoundedMeasurableTest f)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : BoundedMeasurableTest (testAverage μ f) := by
  obtain ⟨hm, C, hC⟩ := hf
  have hmeas : StronglyMeasurable (fun p : ℝ × ℝ => f (p.1 + p.2)) :=
    (hm.comp (by fun_prop)).stronglyMeasurable
  refine ⟨hmeas.integral_prod_right'.measurable, C, ?_⟩
  intro x
  have h := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall (fun z => hC (x + z)))
  simpa [testAverage] using h

theorem contaminationExpectation_eq_integral (P : StandardizedLaw) (y : ℝ)
    (n : ℕ) {f : ℝ → ℝ} (hf : BoundedMeasurableTest f) {e : ℝ} (he : e ∈ Icc 0 1) :
    contaminationExpectation P.measure y n f e =
      ∫ x, f x ∂iidSumLaw (contaminatedMeasure P y e) n := by
  letI := contaminatedMeasure_probability P y he
  induction n generalizing f with
  | zero => simp [contaminationExpectation, iidSumLaw]
  | succ n ih =>
    have havg := boundedMeasurableTest_average hf P.measure
    have hshift := boundedMeasurableTest_shift hf y
    rw [contaminationExpectation, ih havg, ih hshift]
    have heq : iidSumLaw (contaminatedMeasure P y e) (n + 1) =
        iidSumLaw (contaminatedMeasure P y e) n ∗ contaminatedMeasure P y e :=
      Measure.conv_comm _ _
    rw [heq, integral_conv (boundedMeasurableTest_integrable hf _)]
    have hinner (x : ℝ) :
        (∫ z, f (x + z) ∂contaminatedMeasure P y e) =
          (1 - e) * testAverage P.measure f x + e * testShift y f x := by
      apply integral_contaminatedMeasure P y he
      apply boundedMeasurableTest_integrable
      exact ⟨hf.1.comp (by fun_prop), hf.2.imp (fun C hC z => hC (x + z))⟩
    simp_rw [hinner]
    rw [integral_add ((boundedMeasurableTest_integrable havg _).const_mul (1 - e))
      ((boundedMeasurableTest_integrable hshift _).const_mul e),
      integral_const_mul, integral_const_mul]

def cdfTest (t : ℝ) : ℝ → ℝ := (Iic t).indicator (fun _ => 1)

theorem cdfTest_boundedMeasurable (t : ℝ) : BoundedMeasurableTest (cdfTest t) := by
  refine ⟨measurable_const.indicator measurableSet_Iic, 1, ?_⟩
  intro x
  by_cases hx : x ∈ Iic t <;> simp [cdfTest, hx]

theorem integral_cdfTest (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (∫ x, cdfTest t x ∂μ) = cdf μ t := by
  rw [cdf_eq_real]
  exact integral_indicator_one measurableSet_Iic

theorem integral_shift_cdfTest (μ : Measure ℝ) [IsProbabilityMeasure μ] (t y : ℝ) :
    (∫ x, testShift y (cdfTest t) x ∂μ) = cdf μ (t - y) := by
  rw [← integral_cdfTest]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [testShift, cdfTest, indicator_apply, mem_Iic]
  simp only [show x + y ≤ t ↔ x ≤ t - y by constructor <;> intro h <;> linarith]

theorem contaminated_convolution_cdf_derivative (P : StandardizedLaw) (n : ℕ) (t y : ℝ) :
    HasDerivWithinAt
      (fun e => cdf (iidSumLaw (contaminatedMeasure P y e) (n + 1)) t)
      ((n + 1 : ℝ) * (cdf (iidSumLaw P.measure n) (t - y) -
        cdf (iidSumLaw P.measure (n + 1)) t)) (Icc 0 1) 0 := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hbase := contaminationExpectation_eq_integral P y (n + 1) (cdfTest_boundedMeasurable t) hz
  have hshift := contaminationExpectation_eq_integral P y n
    (boundedMeasurableTest_shift (cdfTest_boundedMeasurable t) y) hz
  rw [contaminatedMeasure_zero, integral_cdfTest] at hbase
  rw [contaminatedMeasure_zero, integral_shift_cdfTest] at hshift
  have hd := (contaminationExpectation_derivative P.measure y n (cdfTest t)).hasDerivWithinAt
    (s := Icc 0 1)
  rw [hbase, hshift] at hd
  apply hd.congr_of_mem _ hz
  intro e he
  letI := contaminatedMeasure_probability P y he
  rw [contaminationExpectation_eq_integral P y (n + 1) (cdfTest_boundedMeasurable t) he,
    integral_cdfTest]

end BerryEsseen
