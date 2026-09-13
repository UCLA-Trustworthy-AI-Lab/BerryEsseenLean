import BerryEsseen.ManuscriptSmoothingInversion
import BerryEsseen.ManuscriptSmoothingFourierKernel
import Mathlib.Analysis.Convolution

/-! The Fourier transform and direct inversion of the actual CDF convolution.
The convolution is first proved integrable and continuous.  Its own Fourier
transform is the product of the two transforms, and is integrable with compact
support.  Fourier inversion is then applied to the convolution itself. -/
noncomputable section
open MeasureTheory Set
open scoped Convolution FourierTransform
namespace BerryEsseen

theorem manuscript_realPhase_argument_add (t x y : ℝ) :
    realPhase t (x + y) = realPhase t x * realPhase t y := by
  unfold realPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The L1 convolution theorem does not require continuity of the CDF difference. -/
theorem manuscript_angular_fourier_convolution (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    manuscriptAngularFourier (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) t =
      manuscriptAngularFourier f t * manuscriptAngularFourier g t := by
  have hb := hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hp : Integrable (fun p : ℝ × ℝ =>
      (f p.2 * g (p.1 - p.2)) * realPhase t p.1) (volume.prod volume) := by
    apply hb.norm.mono' (hb.aestronglyMeasurable.mul (by unfold realPhase; fun_prop))
    filter_upwards [] with p
    change ‖(f p.2 * g (p.1 - p.2)) * realPhase t p.1‖ ≤ ‖f p.2 * g (p.1 - p.2)‖
    simp only [norm_mul, realPhase_norm, mul_one]
    exact le_rfl
  have hshift (z : ℝ) :
      (∫ x : ℝ, g (x - z) * realPhase t x) =
        manuscriptAngularFourier g t * realPhase t z := by
    have he := integral_sub_right_eq_self (fun y : ℝ => g y * realPhase t (y + z)) z (μ := volume)
    simp only [sub_add_cancel] at he
    rw [he]
    simp_rw [manuscript_realPhase_argument_add, ← mul_assoc]
    exact integral_mul_const _ _
  calc
    _ = ∫ x : ℝ, ∫ z : ℝ, (f z * g (x - z)) * realPhase t x := by
      unfold manuscriptAngularFourier
      simp only [convolution_def, ContinuousLinearMap.mul_apply', integral_mul_const]
    _ = ∫ z : ℝ, ∫ x : ℝ, (f z * g (x - z)) * realPhase t x :=
      integral_integral_swap hp
    _ = ∫ z : ℝ, (f z * realPhase t z) * manuscriptAngularFourier g t := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp_rw [mul_assoc]
      rw [integral_const_mul, hshift]
      ring
    _ = _ := integral_mul_const _ _

theorem manuscript_densityFourier_convolution (d k : ℝ → ℝ)
    (hd : Integrable d) (hk : Integrable k) (t : ℝ) :
    densityFourier (fun x => ∫ z, d z * k (x - z)) t =
      densityFourier d t * densityFourier k t := by
  have h := manuscript_angular_fourier_convolution
    (fun x => (d x : ℂ)) (fun x => (k x : ℂ)) hd.ofReal hk.ofReal t
  have he : ((fun x => (d x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun x => (k x : ℂ))) = fun x => ((∫ z, d z * k (x - z) : ℝ) : ℂ) := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.mul_apply', ← Complex.ofReal_mul,
      integral_complex_ofReal]
  rw [he] at h
  exact h

theorem manuscript_densityFourier_continuous (d : ℝ → ℝ) (hd : Integrable d) :
    Continuous (densityFourier d) := by
  unfold densityFourier
  apply continuous_of_dominated
  · intro t
    exact (densityFourier_integrable d hd t).aestronglyMeasurable
  · intro t
    filter_upwards [] with x
    simp only [norm_mul, realPhase_norm, mul_one, Complex.norm_real]
    exact le_rfl
  · exact hd.norm
  · filter_upwards [] with x
    unfold realPhase
    fun_prop

def manuscriptScaledSmoothingKernel (L x : ℝ) : ℝ :=
  L * manuscriptSmoothingKernel (L * x)

theorem manuscriptScaledSmoothingKernel_integrable (L : ℝ) (hL : 0 < L) :
    Integrable (manuscriptScaledSmoothingKernel L) :=
  (manuscriptSmoothingKernel_integrable.comp_mul_left' hL.ne').const_mul L

theorem manuscriptScaledSmoothingKernel_continuous (L : ℝ) :
    Continuous (manuscriptScaledSmoothingKernel L) := by
  unfold manuscriptScaledSmoothingKernel
  exact continuous_const.mul (manuscriptSmoothingKernel_continuous.comp
    (continuous_const.mul continuous_id))

theorem manuscriptScaledSmoothingKernel_bounded (L : ℝ) (hL : 0 < L) :
    BddAbove (range (fun x => ‖manuscriptScaledSmoothingKernel L x‖)) := by
  refine ⟨L * (3 / (8 * Real.pi)), ?_⟩
  rintro _ ⟨x, rfl⟩
  change ‖manuscriptScaledSmoothingKernel L x‖ ≤ _
  rw [Real.norm_eq_abs, manuscriptScaledSmoothingKernel,
    abs_of_nonneg (mul_nonneg hL.le (manuscriptSmoothingKernel_nonneg _))]
  exact mul_le_mul_of_nonneg_left (manuscriptSmoothingKernel_le_constant _) hL.le

theorem manuscriptScaledSmoothingKernel_fourier (L : ℝ) (hL : 0 < L) (t : ℝ) :
    densityFourier (manuscriptScaledSmoothingKernel L) t =
      densityFourier manuscriptSmoothingKernel (t / L) := by
  let F : ℝ → ℂ := fun y => (manuscriptSmoothingKernel y : ℂ) * realPhase (t / L) y
  have hs := Measure.integral_comp_mul_left F L
  have he : (fun x => F (L * x)) =
      fun x => (manuscriptSmoothingKernel (L * x) : ℂ) * realPhase t x := by
    funext x
    dsimp [F]
    congr 1
    unfold realPhase
    congr 2
    field_simp
  rw [he, abs_of_pos (inv_pos.mpr hL), Complex.real_smul] at hs
  unfold densityFourier manuscriptScaledSmoothingKernel
  simp only [Complex.ofReal_mul, mul_assoc, integral_const_mul]
  rw [hs]
  change (L : ℂ) * (((L⁻¹ : ℝ) : ℂ) * ∫ y, F y) = ∫ y, F y
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hL.ne', Complex.ofReal_one, one_mul]

def manuscriptCDFConvolution (μ : Measure ℝ) (s : SignedMeasure ℝ) (L x : ℝ) : ℝ :=
  ∫ z, (μ.real (Iic z) - s (Iic z)) * manuscriptScaledSmoothingKernel L (x - z)

theorem manuscriptCDFConvolution_integrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L) :
    Integrable (manuscriptCDFConvolution μ s L) :=
  (manuscript_signed_cdf_difference_integrable μ s hs hμ hs1).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (manuscriptScaledSmoothingKernel_integrable L hL)

theorem manuscriptCDFConvolution_continuous
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L) :
    Continuous (manuscriptCDFConvolution μ s L) :=
  (manuscriptScaledSmoothingKernel_bounded L hL).continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) (manuscript_signed_cdf_difference_integrable μ s hs hμ hs1)
    (manuscriptScaledSmoothingKernel_continuous L)

theorem manuscriptCDFConvolution_fourier_product
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L) (t : ℝ) :
    densityFourier (manuscriptCDFConvolution μ s L) t =
      densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t *
        densityFourier manuscriptSmoothingKernel (t / L) := by
  unfold manuscriptCDFConvolution
  rw [manuscript_densityFourier_convolution _ _
    (manuscript_signed_cdf_difference_integrable μ s hs hμ hs1)
    (manuscriptScaledSmoothingKernel_integrable L hL), manuscriptScaledSmoothingKernel_fourier L hL]

theorem manuscriptCDFConvolution_fourier_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L) :
    Function.support (densityFourier (manuscriptCDFConvolution μ s L)) ⊆ Icc (-L) L := by
  intro t ht
  by_contra hnot
  have hlarge : L < |t| := lt_of_not_ge (fun he => hnot (abs_le.mp he))
  have hdiv : 1 < |t / L| := by
    rw [abs_div, abs_of_pos hL]
    exact (one_lt_div hL).mpr hlarge
  exact ht (by rw [manuscriptCDFConvolution_fourier_product μ s hs hμ hs1 L hL,
    manuscriptSmoothingKernel_fourier_zero _ hdiv, mul_zero])

/-- The mass-zero, first-moment Fourier quotient gives an L1 transform after cutoff.
The quotient identity is supplied by the manuscript's weak derivative theorem. -/
theorem manuscriptCDFConvolution_fourier_integrable_of_quotient
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L)
    (hquotient : ∀ t : ℝ, t ≠ 0 →
      densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t =
        (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I)) :
    Integrable (densityFourier (manuscriptCDFConvolution μ s L)) := by
  have hq := signedSmoothing_fourier_integrable μ s hs hμ hs1 L
  have hi := hq.integrable_indicator measurableSet_Icc
  have hc := manuscript_densityFourier_continuous _
    (manuscriptCDFConvolution_integrable μ s hs hμ hs1 L hL)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  by_cases hin : t ∈ Icc (-L) L
  · rw [indicator_of_mem hin, manuscriptCDFConvolution_fourier_product μ s hs hμ hs1 L hL,
      hquotient t ht]
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, norm_sub_rev]
    exact mul_le_of_le_one_right (by positivity) (manuscriptSmoothingKernel_fourier_norm _)
  · rw [indicator_of_notMem hin]
    have hz : densityFourier (manuscriptCDFConvolution μ s L) t = 0 := by
      by_contra hne
      exact hin (manuscriptCDFConvolution_fourier_support μ s hs hμ hs1 L hL hne)
    rw [hz, norm_zero]

/-- Direct Fourier inversion of d*K_L, after establishing its own L1 transform
and continuity.  This theorem does not invert K_L and substitute its formula. -/
theorem manuscriptCDFConvolution_direct_inversion_of_quotient
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L)
    (hquotient : ∀ t : ℝ, t ≠ 0 →
      densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t =
        (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I)) (x : ℝ) :
    (manuscriptCDFConvolution μ s L x : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t in Icc (-L) L, densityFourier (manuscriptCDFConvolution μ s L) t *
        realPhase (-t) x := by
  have hinv := manuscript_densityFourier_inversion (manuscriptCDFConvolution μ s L)
    (manuscriptCDFConvolution_integrable μ s hs hμ hs1 L hL)
    (manuscriptCDFConvolution_continuous μ s hs hμ hs1 L hL)
    (manuscriptCDFConvolution_fourier_integrable_of_quotient μ s hs hμ hs1 L hL hquotient) x
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero] at hinv
  · exact hinv
  · intro t ht
    have hz : densityFourier (manuscriptCDFConvolution μ s L) t = 0 := by
      by_contra hne
      exact ht (manuscriptCDFConvolution_fourier_support μ s hs hμ hs1 L hL hne)
    rw [hz, zero_mul]

theorem manuscriptCDFConvolution_bound_of_direct_inversion
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation) (L : ℝ) (hL : 0 < L)
    (hquotient : ∀ t : ℝ, t ≠ 0 →
      densityFourier (fun x => μ.real (Iic x) - s (Iic x)) t =
        (signedFourier s t - charFun μ t) / ((t : ℂ) * Complex.I)) (x : ℝ) :
    |manuscriptCDFConvolution μ s L x| ≤ (1 / (2 * Real.pi)) *
      ∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t| := by
  have hinv := manuscriptCDFConvolution_direct_inversion_of_quotient μ s hs hμ hs1 L hL hquotient x
  have hf := manuscriptCDFConvolution_fourier_integrable_of_quotient μ s hs hμ hs1 L hL hquotient
  have hp : IntegrableOn (fun t => densityFourier (manuscriptCDFConvolution μ s L) t *
      realPhase (-t) x) (Icc (-L) L) := by
    have hphase : AEStronglyMeasurable (fun t : ℝ => realPhase (-t) x) volume := by
      unfold realPhase
      fun_prop
    apply hf.norm.integrableOn.mono'
      ((hf.aestronglyMeasurable.mul hphase).mono_measure Measure.restrict_le_self)
    filter_upwards [] with t
    change ‖densityFourier (manuscriptCDFConvolution μ s L) t * realPhase (-t) x‖ ≤
      ‖densityFourier (manuscriptCDFConvolution μ s L) t‖
    simp only [norm_mul, realPhase_norm, mul_one, le_refl]
  have hq := signedSmoothing_fourier_integrable μ s hs hμ hs1 L
  have hn := congrArg norm hinv
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
    abs_of_pos (by positivity : 0 < (1 : ℝ) / (2 * Real.pi))] at hn
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae hp.norm hq
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht
  rw [manuscriptCDFConvolution_fourier_product μ s hs hμ hs1 L hL, hquotient t ht]
  simp only [norm_mul, norm_div, realPhase_norm, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, norm_sub_rev]
  exact mul_le_of_le_one_right (by positivity) (manuscriptSmoothingKernel_fourier_norm _)

end BerryEsseen
