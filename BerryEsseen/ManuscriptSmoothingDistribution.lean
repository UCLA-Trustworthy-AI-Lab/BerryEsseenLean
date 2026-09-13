import BerryEsseen.ManuscriptSmoothingInversion
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The distributional derivative of a CDF difference.

The first identity below is integration by parts against arbitrary C¹ test
functions with bounded derivative and integrable values. It is proved by the
fundamental theorem of calculus, not by computing a step function's Fourier
transform. Compactly supported C¹ tests give the usual distributional
derivative. Finite first moments also justify the larger test class, which
contains the Fourier exponentials. The Fourier derivative rule then gives the
CDF Fourier quotient. No earlier Fourier quotient is used. -/
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace BerryEsseen

/-- The usual weak/distributional identity `d' = μ - η`, tested against
compactly supported C¹ complex-valued functions. -/
def ManuscriptHasDistributionDerivative (d : ℝ → ℝ) (μ η : Measure ℝ) : Prop :=
  Integrable d ∧ ∀ (φ ψ : ℝ → ℂ), HasCompactSupport φ →
    (∀ x, HasDerivAt φ (ψ x) x) → Continuous ψ →
    (∫ x, (d x : ℂ) * ψ x) = (∫ x, φ x ∂η) - ∫ x, φ x ∂μ

/-- The extension of the same integration-by-parts identity to C¹ tests whose
derivative is bounded and whose values are integrable for both finite measures.
This extension is valid here because the CDF difference is L¹. -/
def ManuscriptHasBoundedTestDerivative (d : ℝ → ℝ) (μ η : Measure ℝ) : Prop :=
  Integrable d ∧ ∀ (φ ψ : ℝ → ℂ), (∀ x, HasDerivAt φ (ψ x) x) → Continuous ψ →
    (∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C) → Integrable φ μ → Integrable φ η →
    (∫ x, (d x : ℂ) * ψ x) = (∫ x, φ x ∂η) - ∫ x, φ x ∂μ

theorem manuscript_distribution_of_bounded_tests (d : ℝ → ℝ) (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : ManuscriptHasBoundedTestDerivative d μ η) :
    ManuscriptHasDistributionDerivative d μ η := by
  refine ⟨h.1, ?_⟩
  intro φ ψ hφ hd hψ
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have he : ψ = deriv φ := by funext x; exact (hd x).deriv.symm
  have hψs : HasCompactSupport ψ := by rw [he]; exact hφ.deriv
  exact h.2 φ ψ hd hψ (hψ.bounded_above_of_compact_support hψs)
    (hφc.integrable_of_hasCompactSupport hφ) (hφc.integrable_of_hasCompactSupport hφ)

/-- A point CDF is a weak primitive of the Dirac mass: this is the
fundamental theorem of calculus for a general test function. -/
theorem manuscript_step_test_derivative (φ ψ : ℝ → ℂ)
    (hd : ∀ x, HasDerivAt φ (ψ x) x) (hψ : Continuous ψ) (z : ℝ) :
    (∫ x, (manuscriptStepDifference z x : ℂ) * ψ x) = φ 0 - φ z := by
  rw [manuscriptStepDifference_integral_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hψ.intervalIntegrable 0 z)]
  ring

theorem manuscript_step_test_product_integrable (μ : Measure ℝ) [SFinite μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => (manuscriptStepDifference p.1 p.2 : ℂ) * ψ p.2)
      (μ.prod volume) := by
  have hi := (manuscriptStepDifference_prod_integrable μ hm).norm.mul_const C
  apply hi.mono' ?_ ?_
  · exact (manuscriptStepDifference_measurable.complex_ofReal.mul
      (hψ.measurable.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [] with p
    simp only [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hC p.2) (norm_nonneg _)

/-- Integration by parts for the CDF-to-Dirac primitive of a finite measure,
against general bounded-derivative C¹ tests. All Fubini integrals are L¹. -/
theorem manuscript_primitive_test_derivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) (φ ψ : ℝ → ℂ)
    (hd : ∀ x, HasDerivAt φ (ψ x) x) (hψ : Continuous ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (hφ : Integrable φ μ) :
    (∫ x, ((∫ z, manuscriptStepDifference z x ∂μ : ℝ) : ℂ) * ψ x) =
      (μ.real univ : ℂ) * φ 0 - ∫ z, φ z ∂μ := by
  calc
    _ = ∫ x, ∫ z, (manuscriptStepDifference z x : ℂ) * ψ x ∂μ := by
      congr 1
      funext x
      rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ z, (∫ x, (manuscriptStepDifference z x : ℂ) * ψ x) ∂μ :=
      (integral_integral_swap (manuscript_step_test_product_integrable μ hm ψ hψ C hC)).symm
    _ = ∫ z, φ 0 - φ z ∂μ := by
      congr 1
      funext z
      exact manuscript_step_test_derivative φ ψ hd hψ z
    _ = _ := by
      rw [integral_sub (integrable_const _) hφ, integral_const]
      simp only [Complex.real_smul]

theorem manuscript_cdf_difference_bounded_test_derivative (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hη : Integrable (fun z : ℝ => |z|) η) (hmass : μ.real univ = η.real univ) :
    ManuscriptHasBoundedTestDerivative (fun x => μ.real (Iic x) - η.real (Iic x)) μ η := by
  refine ⟨manuscript_cdf_difference_integrable μ η hμ hη hmass, ?_⟩
  intro φ ψ hd hψ hbound hφμ hφη
  obtain ⟨C, hC⟩ := hbound
  have hμi := (manuscript_step_test_product_integrable μ hμ ψ hψ C hC).integral_prod_right
  have hηi := (manuscript_step_test_product_integrable η hη ψ hψ C hC).integral_prod_right
  have hμi' : Integrable (fun x => ((∫ z, manuscriptStepDifference z x ∂μ : ℝ) : ℂ) * ψ x) := by
    convert hμi using 1
    funext x
    simp only [integral_mul_const, integral_complex_ofReal]
  have hηi' : Integrable (fun x => ((∫ z, manuscriptStepDifference z x ∂η : ℝ) : ℂ) * ψ x) := by
    convert hηi using 1
    funext x
    simp only [integral_mul_const, integral_complex_ofReal]
  have he : (fun x => ((μ.real (Iic x) - η.real (Iic x) : ℝ) : ℂ) * ψ x) =
      fun x => ((∫ z, manuscriptStepDifference z x ∂μ : ℝ) : ℂ) * ψ x -
        ((∫ z, manuscriptStepDifference z x ∂η : ℝ) : ℂ) * ψ x := by
    funext x
    simp only [manuscript_primitive_difference_eq, hmass, Complex.ofReal_sub,
      Complex.ofReal_mul]
    ring
  rw [he, integral_sub hμi' hηi',
    manuscript_primitive_test_derivative μ hμ φ ψ hd hψ C hC hφμ,
    manuscript_primitive_test_derivative η hη φ ψ hd hψ C hC hφη, hmass]
  ring

theorem manuscript_cdf_difference_distribution_derivative (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hη : Integrable (fun z : ℝ => |z|) η) (hmass : μ.real univ = η.real univ) :
    ManuscriptHasDistributionDerivative (fun x => μ.real (Iic x) - η.real (Iic x)) μ η :=
  manuscript_distribution_of_bounded_tests _ μ η
    (manuscript_cdf_difference_bounded_test_derivative μ η hμ hη hmass)

/-- The Fourier derivative rule for the positive-exponent convention. The
integration-by-parts identity, rather than a step Fourier calculation, is its input. -/
theorem manuscript_fourier_from_bounded_test_derivative (d : ℝ → ℝ) (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hweak : ManuscriptHasBoundedTestDerivative d μ η) (t : ℝ) :
    ((t : ℂ) * Complex.I) * densityFourier d t = charFun η t - charFun μ t := by
  let ψ : ℝ → ℂ := fun x => ((t : ℂ) * Complex.I) * realPhase t x
  have hd : ∀ x, HasDerivAt (realPhase t) (ψ x) x := by
    intro x
    have h := realPhase_hasDerivAt x t
    convert h using 1
    · funext y
      simp only [realPhase, mul_comm t y]
    · dsimp only [ψ]
      rw [show realPhase x t = realPhase t x by simp [realPhase, mul_comm]]
      ring
  have hψ : Continuous ψ := by unfold ψ realPhase; fun_prop
  have hb : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C := by
    refine ⟨|t|, ?_⟩
    intro x
    simp only [ψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      realPhase_norm, mul_one, le_refl]
  have hh := hweak.2 (realPhase t) ψ hd hψ hb
    (manuscript_phase_integrable_finite μ t) (manuscript_phase_integrable_finite η t)
  have he : (fun x => (d x : ℂ) * ψ x) =
      fun x => ((t : ℂ) * Complex.I) * ((d x : ℂ) * realPhase t x) := by
    funext x
    dsimp only [ψ]
    ring
  rw [he, integral_const_mul, ← charFun_eq_integral_realPhase,
    ← charFun_eq_integral_realPhase] at hh
  exact hh

theorem manuscript_cdf_difference_fourier_from_weak_derivative (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hη : Integrable (fun z : ℝ => |z|) η) (hmass : μ.real univ = η.real univ)
    (t : ℝ) (ht : t ≠ 0) :
    densityFourier (fun x => μ.real (Iic x) - η.real (Iic x)) t =
      (charFun η t - charFun μ t) / ((t : ℂ) * Complex.I) := by
  have hh := manuscript_fourier_from_bounded_test_derivative _ μ η
    (manuscript_cdf_difference_bounded_test_derivative μ η hμ hη hmass) t
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero)).mpr
  simpa only [mul_comm] using hh

/-- The signed-measure distributional derivative `d' = μ - s`, represented by
the difference of the finite measures `μ+s⁻` and `s⁺`. -/
theorem manuscript_signed_cdf_difference_distribution_derivative
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) :
    ManuscriptHasDistributionDerivative (fun x => μ.real (Iic x) - s (Iic x))
      (μ + s.toJordanDecomposition.negPart) s.toJordanDecomposition.posPart := by
  have hp := hs1.left_of_add_measure
  have hn := hs1.right_of_add_measure
  have hm : (μ + s.toJordanDecomposition.negPart).real univ = s.toJordanDecomposition.posPart.real univ := by
    rw [measureReal_add_apply, probReal_univ]
    rw [signedMeasure_jordan_apply s univ MeasurableSet.univ] at hs
    linarith
  have he : (fun x => μ.real (Iic x) - s (Iic x)) =
      fun x => (μ + s.toJordanDecomposition.negPart).real (Iic x) -
        s.toJordanDecomposition.posPart.real (Iic x) := by
    funext x
    rw [measureReal_add_apply, signedMeasure_jordan_apply s (Iic x) measurableSet_Iic]
    ring
  rw [he]
  exact manuscript_cdf_difference_distribution_derivative _ _ (hμ.add_measure hn) hp hm

/-- The manuscript's Fourier quotient, now obtained from the weak derivative
and the derivative of exp(itx). The sign is for the positive-exponent Fourier convention. -/
theorem manuscript_signed_cdf_difference_fourier_from_weak_derivative
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (t : ℝ) (ht : t ≠ 0) :
    densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t =
      (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I) := by
  have hp := hs1.left_of_add_measure
  have hn := hs1.right_of_add_measure
  have hm : (μ + s.toJordanDecomposition.negPart).real univ = s.toJordanDecomposition.posPart.real univ := by
    rw [measureReal_add_apply, probReal_univ]
    rw [signedMeasure_jordan_apply s univ MeasurableSet.univ] at hs
    linarith
  have he : (fun x => μ.real (Iic x) - s (Iic x)) =
      fun x => (μ + s.toJordanDecomposition.negPart).real (Iic x) -
        s.toJordanDecomposition.posPart.real (Iic x) := by
    funext x
    rw [measureReal_add_apply, signedMeasure_jordan_apply s (Iic x) measurableSet_Iic]
    ring
  rw [he, manuscript_cdf_difference_fourier_from_weak_derivative _ _ (hμ.add_measure hn) hp hm t ht]
  have hchar : charFun (μ + s.toJordanDecomposition.negPart) t =
      charFun μ t + charFun s.toJordanDecomposition.negPart t := by
    rw [charFun_eq_integral_realPhase, charFun_eq_integral_realPhase, charFun_eq_integral_realPhase,
      integral_add_measure (manuscript_phase_integrable_finite μ t)
        (manuscript_phase_integrable_finite s.toJordanDecomposition.negPart t)]
  rw [hchar, signedFourier]
  ring

end BerryEsseen
