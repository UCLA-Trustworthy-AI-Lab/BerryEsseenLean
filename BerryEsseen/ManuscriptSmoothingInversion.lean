import BerryEsseen.GeneralSignedSmoothing
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! CDF difference, first-moment and Fourier bridges for the manuscript's
sinc-kernel proof. No published smoothing inequality is invoked. -/
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology FourierTransform
namespace BerryEsseen

/-- The difference between the CDF of a point mass at z and that at zero. -/
def manuscriptStepDifference (z x : ℝ) : ℝ :=
  (if z ≤ x then 1 else 0) - (if 0 ≤ x then 1 else 0)

theorem manuscriptStepDifference_nonneg_parameter (z : ℝ) (hz : 0 ≤ z) :
    manuscriptStepDifference z = fun x => -(Ico 0 z).indicator (fun _ => (1 : ℝ)) x := by
  funext x
  simp only [manuscriptStepDifference, indicator_apply, mem_Ico]
  split_ifs <;> grind

theorem manuscriptStepDifference_nonpos_parameter (z : ℝ) (hz : z ≤ 0) :
    manuscriptStepDifference z = (Ico z 0).indicator (fun _ => (1 : ℝ)) := by
  funext x
  simp only [manuscriptStepDifference, indicator_apply, mem_Ico]
  split_ifs <;> grind

theorem manuscriptStepDifference_integrable (z : ℝ) :
    Integrable (manuscriptStepDifference z) := by
  rcases le_total 0 z with hz | hz
  · rw [manuscriptStepDifference_nonneg_parameter z hz]
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico 0 z) :=
      (continuous_const.integrableOn_Icc).mono_set Ico_subset_Icc_self
    have hi : Integrable ((Ico 0 z).indicator (fun _ => (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_Ico).mpr hc
    exact hi.neg
  · rw [manuscriptStepDifference_nonpos_parameter z hz]
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ico z 0) :=
      (continuous_const.integrableOn_Icc).mono_set Ico_subset_Icc_self
    exact (integrable_indicator_iff measurableSet_Ico).mpr hc

theorem manuscriptStepDifference_integral_norm (z : ℝ) :
    (∫ x, ‖manuscriptStepDifference z x‖) = |z| := by
  rcases le_total 0 z with hz | hz
  · rw [manuscriptStepDifference_nonneg_parameter z hz]
    have hfun : (fun x => ‖-(Ico 0 z).indicator (fun _ => (1 : ℝ)) x‖) =
        (Ico 0 z).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Ico 0 z <;> simp [hx]
    rw [hfun]
    have he : (∫ x, (Ico 0 z).indicator (fun _ => (1 : ℝ)) x) = volume.real (Ico 0 z) :=
      integral_indicator_one measurableSet_Ico
    rw [he]
    simp [Real.volume_real_Ico, hz, abs_of_nonneg hz]
  · rw [manuscriptStepDifference_nonpos_parameter z hz]
    have hfun : (fun x => ‖(Ico z 0).indicator (fun _ => (1 : ℝ)) x‖) =
        (Ico z 0).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Ico z 0 <;> simp [hx]
    rw [hfun]
    have he : (∫ x, (Ico z 0).indicator (fun _ => (1 : ℝ)) x) = volume.real (Ico z 0) :=
      integral_indicator_one measurableSet_Ico
    rw [he]
    simp [Real.volume_real_Ico, hz, abs_of_nonpos hz]

theorem manuscriptStepDifference_measurable :
    Measurable (fun p : ℝ × ℝ => manuscriptStepDifference p.1 p.2) := by
  unfold manuscriptStepDifference
  exact ((measurable_const.ite (measurableSet_le measurable_fst measurable_snd) measurable_const)).sub
    (measurable_const.ite (measurableSet_le measurable_const measurable_snd) measurable_const)

theorem manuscriptStepDifference_prod_integrable (μ : Measure ℝ) [SFinite μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) :
    Integrable (fun p : ℝ × ℝ => manuscriptStepDifference p.1 p.2) (μ.prod volume) := by
  apply (integrable_prod_iff manuscriptStepDifference_measurable.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ manuscriptStepDifference_integrable
  · simpa only [manuscriptStepDifference_integral_norm] using hm

/-- Finite first moment makes the CDF-to-Dirac difference genuinely L1. -/
theorem manuscript_primitive_difference_integrable (μ : Measure ℝ) [SFinite μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) :
    Integrable (fun x : ℝ => ∫ z, manuscriptStepDifference z x ∂μ) :=
  (manuscriptStepDifference_prod_integrable μ hm).integral_prod_right


theorem manuscript_primitive_difference_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    (∫ z, manuscriptStepDifference z x ∂μ) =
      μ.real (Iic x) - μ.real univ * (if 0 ≤ x then 1 else 0) := by
  have hfun : (fun z => manuscriptStepDifference z x) =
      (fun z => (Iic x).indicator (fun _ => (1 : ℝ)) z - (if 0 ≤ x then 1 else 0)) := by
    funext z
    simp only [manuscriptStepDifference, indicator_apply, mem_Iic]
  rw [hfun, integral_sub ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
      (integrable_const (if 0 ≤ x then 1 else 0))]
  have hi : (∫ z, (Iic x).indicator (fun _ => (1 : ℝ)) z ∂μ) = μ.real (Iic x) :=
    integral_indicator_one measurableSet_Iic
  rw [hi, integral_const]
  rfl

/-- This form also covers a signed comparison through its Jordan components. -/
theorem manuscript_cdf_difference_integrable (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hη : Integrable (fun z : ℝ => |z|) η) (hmass : μ.real univ = η.real univ) :
    Integrable (fun x => μ.real (Iic x) - η.real (Iic x)) := by
  have hi := (manuscript_primitive_difference_integrable μ hμ).sub
    (manuscript_primitive_difference_integrable η hη)
  convert hi using 1
  funext x
  simp only [Pi.sub_apply, manuscript_primitive_difference_eq, hmass]
  ring

theorem manuscriptStepDifference_integral_mul (f : ℝ → ℂ) (z : ℝ) :
    (∫ x, (manuscriptStepDifference z x : ℂ) * f x) = -∫ x in (0 : ℝ)..z, f x := by
  rcases le_total 0 z with hz | hz
  · rw [manuscriptStepDifference_nonneg_parameter z hz]
    have he : (fun x => ((-(Ico 0 z).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) * f x) =
        fun x => -(Ico 0 z).indicator f x := by
      funext x
      by_cases hx : x ∈ Ico 0 z <;> simp [hx]
    rw [he, integral_neg, integral_indicator measurableSet_Ico, intervalIntegral.integral_of_le hz]
    rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  · rw [manuscriptStepDifference_nonpos_parameter z hz]
    have he : (fun x => (((Ico z 0).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) * f x) =
        (Ico z 0).indicator f := by
      funext x
      by_cases hx : x ∈ Ico z 0 <;> simp [hx]
    rw [he, integral_indicator measurableSet_Ico, intervalIntegral.integral_of_ge hz, neg_neg]
    rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

theorem manuscriptStepDifference_fourier (z t : ℝ) (ht : t ≠ 0) :
    densityFourier (manuscriptStepDifference z) t =
      (1 - realPhase t z) / ((t : ℂ) * Complex.I) := by
  rw [densityFourier, manuscriptStepDifference_integral_mul]
  have he : (fun x => realPhase t x) =
      (fun x : ℝ => Complex.exp (((t : ℂ) * Complex.I) * x)) := by
    funext x
    unfold realPhase
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hz : Complex.exp ((t : ℂ) * Complex.I * (z : ℂ)) = realPhase t z := by
    unfold realPhase
    congr 1
    push_cast
    ring
  rw [hz]
  ring


theorem manuscript_phase_integrable_finite (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (realPhase t) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold realPhase; fun_prop)
  filter_upwards [] with x
  exact (realPhase_norm t x).le

theorem manuscriptStepDifference_phase_prod_integrable (μ : Measure ℝ) [SFinite μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => (manuscriptStepDifference p.1 p.2 : ℂ) * realPhase t p.2)
      (μ.prod volume) := by
  have hb := manuscriptStepDifference_prod_integrable μ hm
  apply hb.norm.mono' ?_ ?_
  · have hphase : Measurable (fun p : ℝ × ℝ => realPhase t p.2) := by unfold realPhase; fun_prop
    exact (manuscriptStepDifference_measurable.complex_ofReal.mul hphase).aestronglyMeasurable
  · filter_upwards [] with p
    simp only [norm_mul, Complex.norm_real, realPhase_norm, mul_one, Real.norm_eq_abs]
    exact le_rfl

theorem manuscript_primitive_difference_fourier (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) (t : ℝ) (ht : t ≠ 0) :
    densityFourier (fun x => ∫ z, manuscriptStepDifference z x ∂μ) t =
      ((μ.real univ : ℂ) - charFun μ t) / ((t : ℂ) * Complex.I) := by
  unfold densityFourier
  calc
    _ = ∫ x, ∫ z, (manuscriptStepDifference z x : ℂ) * realPhase t x ∂μ := by
      congr 1
      funext x
      rw [integral_mul_const, integral_complex_ofReal]
    _ = ∫ z, (∫ x, (manuscriptStepDifference z x : ℂ) * realPhase t x) ∂μ :=
      (integral_integral_swap (manuscriptStepDifference_phase_prod_integrable μ hm t)).symm
    _ = ∫ z, (1 - realPhase t z) / ((t : ℂ) * Complex.I) ∂μ := by
      congr 1
      funext z
      exact manuscriptStepDifference_fourier z t ht
    _ = _ := by
      rw [integral_div, integral_sub (integrable_const (1 : ℂ)) (manuscript_phase_integrable_finite μ t),
        integral_const, ← charFun_eq_integral_realPhase]
      simp only [Complex.real_smul, mul_one]

theorem manuscript_densityFourier_sub (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    densityFourier (fun x => f x - g x) t = densityFourier f t - densityFourier g t := by
  have hprod (h : ℝ → ℝ) (hh : Integrable h) :
      Integrable (fun x => (h x : ℂ) * realPhase t x) := by
    apply hh.norm.mono' (hh.ofReal.aestronglyMeasurable.mul (by unfold realPhase; fun_prop))
    filter_upwards [] with x
    simp only [norm_mul, Complex.norm_real, realPhase_norm, mul_one]
    exact le_rfl
  unfold densityFourier
  simp only [Complex.ofReal_sub, sub_mul]
  exact integral_sub (hprod f hf) (hprod g hg)

/-- Angular Fourier transform of the CDF difference; its sign and 1/t factor
are derived from the genuine point-mass primitives. -/
theorem manuscript_cdf_difference_fourier (μ η : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hη : Integrable (fun z : ℝ => |z|) η) (hmass : μ.real univ = η.real univ)
    (t : ℝ) (ht : t ≠ 0) :
    densityFourier (fun x => μ.real (Iic x) - η.real (Iic x)) t =
      (charFun η t - charFun μ t) / ((t : ℂ) * Complex.I) := by
  have he : (fun x => μ.real (Iic x) - η.real (Iic x)) =
      fun x => (∫ z, manuscriptStepDifference z x ∂μ) - (∫ z, manuscriptStepDifference z x ∂η) := by
    funext x
    simp only [manuscript_primitive_difference_eq, hmass]
    ring
  rw [he, manuscript_densityFourier_sub _ _
    (manuscript_primitive_difference_integrable μ hμ) (manuscript_primitive_difference_integrable η hη),
    manuscript_primitive_difference_fourier μ hμ t ht,
    manuscript_primitive_difference_fourier η hη t ht, hmass]
  ring


/-- For a fixed x all point-mass CDF differences have the same sign. -/
theorem manuscriptStepDifference_norm_integral (μ : Measure ℝ) (x : ℝ) :
    ‖∫ z, manuscriptStepDifference z x ∂μ‖ = ∫ z, ‖manuscriptStepDifference z x‖ ∂μ := by
  by_cases hx : 0 ≤ x
  · have hs (z : ℝ) : manuscriptStepDifference z x ≤ 0 := by
      simp only [manuscriptStepDifference, hx, ↓reduceIte]
      split_ifs <;> norm_num
    have hi : (∫ z, manuscriptStepDifference z x ∂μ) ≤ 0 := integral_nonpos hs
    have he : (fun z => ‖manuscriptStepDifference z x‖) =
        fun z => -manuscriptStepDifference z x := by
      funext z
      exact abs_of_nonpos (hs z)
    rw [Real.norm_eq_abs, abs_of_nonpos hi, he, integral_neg]
  · have hs (z : ℝ) : 0 ≤ manuscriptStepDifference z x := by
      simp only [manuscriptStepDifference, hx, ↓reduceIte, sub_zero]
      split_ifs <;> norm_num
    have hi : 0 ≤ ∫ z, manuscriptStepDifference z x ∂μ := integral_nonneg hs
    have he : (fun z => ‖manuscriptStepDifference z x‖) =
        fun z => manuscriptStepDifference z x := by
      funext z
      exact abs_of_nonneg (hs z)
    rw [Real.norm_eq_abs, abs_of_nonneg hi, he]

/-- The manuscript's exact L1 distance-to-Dirac identity, rather than merely
an integrability assertion. -/
theorem manuscript_cdf_dirac_L1_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : Integrable (fun z : ℝ => |z|) μ) :
    (∫ x : ℝ, |μ.real (Iic x) - (if 0 ≤ x then 1 else 0)|) = ∫ z, |z| ∂μ := by
  have hh : (∫ x : ℝ, ‖∫ z, manuscriptStepDifference z x ∂μ‖) = ∫ z, |z| ∂μ := by
    calc
      _ = ∫ x : ℝ, ∫ z, ‖manuscriptStepDifference z x‖ ∂μ := by
        simp_rw [manuscriptStepDifference_norm_integral]
      _ = ∫ z, (∫ x : ℝ, ‖manuscriptStepDifference z x‖) ∂μ :=
        (integral_integral_swap (manuscriptStepDifference_prod_integrable μ hm).norm).symm
      _ = _ := by simp_rw [manuscriptStepDifference_integral_norm]
  simpa only [manuscript_primitive_difference_eq, probReal_univ, one_mul, Real.norm_eq_abs] using hh


/-- A finite measure integrates every fixed point-mass CDF difference. -/
theorem manuscriptStepDifference_section_integrable (μ : Measure ℝ)
    [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun z => manuscriptStepDifference z x) μ := by
  have he : (fun z => manuscriptStepDifference z x) =
      fun z => (Iic x).indicator (fun _ => (1 : ℝ)) z - (if 0 ≤ x then 1 else 0) := by
    funext z
    simp only [manuscriptStepDifference, indicator_apply, mem_Iic]
  rw [he]
  exact ((integrable_const (1 : ℝ)).indicator measurableSet_Iic).sub (integrable_const _)

/-- Jordan decomposition represents the signed primitive relative to the
point mass at zero; the unit-mass hypothesis cancels its constant term. -/
theorem manuscript_signed_primitive_eq (s : SignedMeasure ℝ) (hs : s univ = 1) (x : ℝ) :
    s (Iic x) - (if 0 ≤ x then 1 else 0) =
      (∫ z, manuscriptStepDifference z x ∂s.toJordanDecomposition.posPart) -
        ∫ z, manuscriptStepDifference z x ∂s.toJordanDecomposition.negPart := by
  rw [manuscript_primitive_difference_eq, manuscript_primitive_difference_eq,
    signedMeasure_jordan_apply s (Iic x) measurableSet_Iic]
  rw [signedMeasure_jordan_apply s univ MeasurableSet.univ] at hs
  split_ifs <;> simp_all <;> linarith

/-- The pointwise signed primitive is controlled by integrating the absolute
point-mass primitives against total variation. -/
theorem manuscript_signed_primitive_norm_le (s : SignedMeasure ℝ) (hs : s univ = 1)
    (x : ℝ) :
    |s (Iic x) - (if 0 ≤ x then 1 else 0)| ≤
      ∫ z, ‖manuscriptStepDifference z x‖ ∂s.totalVariation := by
  rw [manuscript_signed_primitive_eq s hs]
  change ‖(∫ z, manuscriptStepDifference z x ∂s.toJordanDecomposition.posPart) -
      ∫ z, manuscriptStepDifference z x ∂s.toJordanDecomposition.negPart‖ ≤ _
  calc
    _ ≤ ‖∫ z, manuscriptStepDifference z x ∂s.toJordanDecomposition.posPart‖ +
        ‖∫ z, manuscriptStepDifference z x ∂s.toJordanDecomposition.negPart‖ :=
      norm_sub_le _ _
    _ ≤ (∫ z, ‖manuscriptStepDifference z x‖ ∂s.toJordanDecomposition.posPart) +
        ∫ z, ‖manuscriptStepDifference z x‖ ∂s.toJordanDecomposition.negPart :=
      add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ = _ := by
      exact (integral_add_measure
        (manuscriptStepDifference_section_integrable s.toJordanDecomposition.posPart x).norm
        (manuscriptStepDifference_section_integrable s.toJordanDecomposition.negPart x).norm).symm

/-- The manuscript's signed distance-to-Dirac estimate, including the L1
assertion. The dominating function is the total-variation integral of the
absolute step primitive; Fubini and its exact norm integral give the first
absolute moment, without assuming that the signed measure is positive. -/
theorem manuscript_signed_primitive_L1_bound (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) :
    Integrable (fun x : ℝ => s (Iic x) - (if 0 ≤ x then 1 else 0)) ∧
      (∫ x : ℝ, |s (Iic x) - (if 0 ≤ x then 1 else 0)|) ≤
        ∫ z, |z| ∂s.totalVariation := by
  letI : IsFiniteMeasure s.totalVariation := by
    change IsFiniteMeasure (s.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart)
    infer_instance
  have hp : Integrable (fun z : ℝ => |z|) s.toJordanDecomposition.posPart :=
    hs1.left_of_add_measure
  have hn : Integrable (fun z : ℝ => |z|) s.toJordanDecomposition.negPart :=
    hs1.right_of_add_measure
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => s (Iic x) - (if 0 ≤ x then 1 else 0)) volume := by
    simp_rw [manuscript_signed_primitive_eq s hs]
    exact (manuscriptStepDifference_prod_integrable _ hp).integral_prod_right.aestronglyMeasurable.sub
      (manuscriptStepDifference_prod_integrable _ hn).integral_prod_right.aestronglyMeasurable
  have hprod := (manuscriptStepDifference_prod_integrable s.totalVariation hs1).norm
  have hmajorant := hprod.integral_prod_right
  have hi : Integrable (fun x : ℝ => s (Iic x) - (if 0 ≤ x then 1 else 0)) := by
    apply hmajorant.mono' hmeas
    exact ae_of_all _ (manuscript_signed_primitive_norm_le s hs)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x : ℝ, ∫ z, ‖manuscriptStepDifference z x‖ ∂s.totalVariation :=
      integral_mono hi.norm hmajorant (manuscript_signed_primitive_norm_le s hs)
    _ = ∫ z, (∫ x : ℝ, ‖manuscriptStepDifference z x‖) ∂s.totalVariation :=
      (integral_integral_swap hprod).symm
    _ = _ := by simp_rw [manuscriptStepDifference_integral_norm]

/-- The two first-moment statements used consecutively in the manuscript:
the probability primitive has exact L1 norm, and the signed primitive has
L1 norm at most the first moment of total variation. -/
theorem manuscript_probability_primitive_L1 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun z : ℝ => |z|) μ) :
    Integrable (fun x : ℝ => μ.real (Iic x) - (if 0 ≤ x then 1 else 0)) ∧
      (∫ x : ℝ, |μ.real (Iic x) - (if 0 ≤ x then 1 else 0)|) = ∫ z, |z| ∂μ := by
  refine ⟨?_, manuscript_cdf_dirac_L1_identity μ hμ⟩
  simpa only [manuscript_primitive_difference_eq, probReal_univ, one_mul] using
    manuscript_primitive_difference_integrable μ hμ

theorem manuscript_signed_cdf_difference_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) :
    Integrable (fun x => μ.real (Iic x) - s (Iic x)) := by
  have hi := (manuscript_probability_primitive_L1 μ hμ).1.sub
    (manuscript_signed_primitive_L1_bound s hs hs1).1
  convert hi using 1
  funext x
  simp only [Pi.sub_apply]
  ring

theorem manuscript_signed_cdf_difference_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (t : ℝ) (ht : t ≠ 0) :
    densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t =
      (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I) := by
  have hp : Integrable (fun z : ℝ => |z|) s.toJordanDecomposition.posPart := hs1.left_of_add_measure
  have hn : Integrable (fun z : ℝ => |z|) s.toJordanDecomposition.negPart := hs1.right_of_add_measure
  have hm : (μ + s.toJordanDecomposition.negPart).real univ = s.toJordanDecomposition.posPart.real univ := by
    rw [measureReal_add_apply, probReal_univ]
    rw [signedMeasure_jordan_apply s univ MeasurableSet.univ] at hs
    linarith
  have he : (fun x => μ.real (Iic x) - s (Iic x)) =
      fun x => (μ + s.toJordanDecomposition.negPart).real (Iic x) - s.toJordanDecomposition.posPart.real (Iic x) := by
    funext x
    rw [measureReal_add_apply, signedMeasure_jordan_apply s (Iic x) measurableSet_Iic]
    ring
  rw [he, manuscript_cdf_difference_fourier _ _ (hμ.add_measure hn) hp hm t ht]
  have hchar : charFun (μ + s.toJordanDecomposition.negPart) t =
      charFun μ t + charFun s.toJordanDecomposition.negPart t := by
    rw [charFun_eq_integral_realPhase, charFun_eq_integral_realPhase, charFun_eq_integral_realPhase,
      integral_add_measure (manuscript_phase_integrable_finite μ t)
        (manuscript_phase_integrable_finite s.toJordanDecomposition.negPart t)]
  rw [hchar, signedFourier]
  ring

theorem manuscript_signed_cdf_difference_fourier_norm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (t : ℝ) (ht : t ≠ 0) :
    ‖densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t‖ =
      ‖charFun μ t - signedFourier s t‖ / |t| := by
  rw [manuscript_signed_cdf_difference_fourier μ s hs hμ hs1 t ht]
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    norm_sub_rev]

theorem manuscript_phase_convolution_identity (t x z : ℝ) :
    realPhase (-t) (x - z) = realPhase t z * realPhase (-t) x := by
  unfold realPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Substitution of actual kernel inversion followed by justified Fubini.
The inversion identity is a local hypothesis that will be discharged for K_L. -/
theorem manuscript_convolution_fourier_of_kernel_inversion
    (d : ℝ → ℝ) (hd : Integrable d) (A : ℝ → ℂ) (L c : ℝ)
    (hA : IntegrableOn A (Icc (-L) L)) (k : ℝ → ℝ)
    (hki : ∀ y, (k y : ℂ) = (c : ℂ) * ∫ t in Icc (-L) L, A t * realPhase (-t) y)
    (x : ℝ) :
    ((∫ z, d z * k (x - z) : ℝ) : ℂ) =
      (c : ℂ) * ∫ t in Icc (-L) L, densityFourier d t * A t * realPhase (-t) x := by
  have hbase := hd.ofReal.mul_prod hA
  have hprod : Integrable (fun p : ℝ × ℝ =>
      ((d p.1 : ℂ) * A p.2) * realPhase (-p.2) (x - p.1))
      (volume.prod (volume.restrict (Icc (-L) L))) := by
    apply hbase.norm.mono' ?_ ?_
    · exact hbase.aestronglyMeasurable.mul (by unfold realPhase; fun_prop)
    · filter_upwards [] with p
      simp only [norm_mul, realPhase_norm, mul_one]
      exact le_rfl
  calc
    _ = ∫ z, (d z : ℂ) * (k (x - z) : ℂ) := by
      simp only [← Complex.ofReal_mul, integral_complex_ofReal]
    _ = (c : ℂ) * ∫ z, ∫ t in Icc (-L) L, ((d z : ℂ) * A t) * realPhase (-t) (x - z) := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [hki]
      have hi : (∫ t in Icc (-L) L, ((d z : ℂ) * A t) * realPhase (-t) (x - z)) =
          (d z : ℂ) * ∫ t in Icc (-L) L, A t * realPhase (-t) (x - z) := by
        simp_rw [mul_assoc]
        exact integral_const_mul _ _
      rw [hi]
      ring
    _ = (c : ℂ) * ∫ t in Icc (-L) L, ∫ z, ((d z : ℂ) * A t) * realPhase (-t) (x - z) := by
      rw [integral_integral_swap hprod]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp_rw [manuscript_phase_convolution_identity]
      have he : (fun z => ((d z : ℂ) * A t) * (realPhase t z * realPhase (-t) x)) =
          (fun z => ((d z : ℂ) * realPhase t z) * (A t * realPhase (-t) x)) := by
        funext z
        ring
      rw [he, integral_mul_const]
      unfold densityFourier
      ring


/-- The precise truncated Fourier bound following the manuscript's inversion step.
All CDF and Fourier objects are the actual measure-theoretic ones. -/
theorem manuscript_signed_convolution_bound_of_kernel_inversion
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation)
    (A : ℝ → ℂ) (L c : ℝ) (hc : 0 ≤ c) (hA : IntegrableOn A (Icc (-L) L))
    (hAnorm : ∀ t ∈ Icc (-L) L, ‖A t‖ ≤ 1) (k : ℝ → ℝ)
    (hki : ∀ y, (k y : ℂ) = (c : ℂ) * ∫ t in Icc (-L) L, A t * realPhase (-t) y)
    (x : ℝ) :
    |∫ z, (μ.real (Iic z) - s (Iic z)) * k (x - z)| ≤
      c * ∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t| := by
  let d : ℝ → ℝ := fun z => μ.real (Iic z) - s (Iic z)
  let B : ℝ → ℂ := fun t => ((signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I)) *
    A t * realPhase (-t) x
  have hd : Integrable d := manuscript_signed_cdf_difference_integrable μ s hs hμ hs1
  have hid := manuscript_convolution_fourier_of_kernel_inversion d hd A L c hA k hki x
  have hquot := signedSmoothing_fourier_integrable μ s hs hμ hs1 L
  have hBmeas : AEStronglyMeasurable B (volume.restrict (Icc (-L) L)) := by
    have hf : Measurable (fun t : ℝ => (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I)) := by
      unfold signedFourier
      exact ((measurable_charFun.sub measurable_charFun).sub measurable_charFun).div
        (measurable_id.complex_ofReal.mul_const _)
    exact (hf.aestronglyMeasurable.mul hA.aestronglyMeasurable).mul (by unfold realPhase; fun_prop)
  have hnorm : ∀ t ∈ Icc (-L) L, ‖B t‖ ≤ ‖charFun μ t - signedFourier s t‖ / |t| := by
    intro t ht
    dsimp only [B]
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      realPhase_norm, mul_one, norm_sub_rev]
    exact mul_le_of_le_one_right (by positivity) (hAnorm t ht)
  have hBi : IntegrableOn B (Icc (-L) L) := by
    apply hquot.mono' hBmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hnorm t ht
  have hae : ∀ᵐ t ∂(volume.restrict (Icc (-L) L)), t ≠ (0 : ℝ) := by
    exact ae_restrict_of_ae (volume.ae_ne (0 : ℝ))
  have hi : (∫ t in Icc (-L) L, densityFourier d t * A t * realPhase (-t) x) =
      ∫ t in Icc (-L) L, B t := by
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    rw [show densityFourier d t = (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I) from
      manuscript_signed_cdf_difference_fourier μ s hs hμ hs1 t ht]
  rw [hi] at hid
  have hn := congrArg norm hid
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, abs_of_nonneg hc] at hn
  change |∫ z, d z * k (x - z)| ≤ _
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hBi.norm hquot (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hnorm t ht))


/-- The rescaled kernel's exact inverse Fourier formula, with support [-L,L]. -/
theorem manuscript_scaled_kernel_inversion (K : ℝ → ℝ) (A : ℝ → ℂ) (c L : ℝ)
    (hL : 0 < L)
    (hinv : ∀ y, (K y : ℂ) = (c : ℂ) * ∫ t : ℝ, A t * realPhase (-t) y)
    (hsupport : ∀ t : ℝ, 1 < |t| → A t = 0) (y : ℝ) :
    ((L * K (L * y) : ℝ) : ℂ) = (c : ℂ) *
      ∫ t in Icc (-L) L, A (t / L) * realPhase (-t) y := by
  let f : ℝ → ℂ := fun t => A (t / L) * realPhase (-t) y
  have hchange := Measure.integral_comp_mul_left f L
  have he : (fun t => f (L * t)) = fun t => A t * realPhase (-t) (L * y) := by
    funext t
    dsimp only [f]
    rw [mul_div_cancel_left₀ t hL.ne']
    congr 1
    unfold realPhase
    congr 1
    push_cast
    ring
  rw [he, abs_of_pos (inv_pos.mpr hL), Complex.real_smul] at hchange
  have htrunc : (∫ t in Icc (-L) L, f t) = ∫ t, f t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hlarge : L < |t| := by
      by_contra h
      exact ht (abs_le.mp (le_of_not_gt h))
    have hdiv : 1 < |t / L| := by
      rw [abs_div, abs_of_pos hL]
      exact (one_lt_div hL).mpr hlarge
    simp only [f, hsupport _ hdiv, zero_mul]
  rw [Complex.ofReal_mul, hinv, hchange]
  change (L : ℂ) * ((c : ℂ) * (((L⁻¹ : ℝ) : ℂ) * (∫ t, f t))) =
    (c : ℂ) * ∫ t in Icc (-L) L, f t
  rw [htrunc]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp



end BerryEsseen
