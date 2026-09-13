import BerryEsseen.ManuscriptSmoothingCDFBounds
import BerryEsseen.ManuscriptSmoothingConvolutionBound

/-! Lemma 2.1 with the appendix constants, along the manuscript's own proof.

The actual density is `3/(8*pi) * sinc(x/4)^4`. Its normalization, Fourier
support, inversion formula, first moment, and tail bounds are theorems. The
two convolution inequalities are proved by integration and combined by taking
the actual suprema of the two signs. No published smoothing premise is used.
-/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped NNReal
namespace BerryEsseen

instance manuscriptSmoothingMeasure_probability :
    IsProbabilityMeasure manuscriptSmoothingMeasure := by
  rw [isProbabilityMeasure_iff_real,
    manuscriptSmoothingMeasure_real univ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using manuscriptSmoothingKernel_integral

theorem manuscriptSmoothingMeasure_loss_lt_eighteen :
    (∫ z, max (16 - z) 0 ∂manuscriptSmoothingMeasure) < 18 := by
  rw [manuscriptSmoothingMeasure_integral]
  have hb := manuscriptSmoothingKernel_loss_bound
  rw [manuscriptSmoothingKernel_integral] at hb
  have hpi : 6 / Real.pi < 2 := by
    rw [div_lt_iff₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  have he : (∫ z : ℝ, manuscriptSmoothingKernel z * max (16 - z) 0) =
      ∫ z : ℝ, max (16 - z) 0 * manuscriptSmoothingKernel z := by
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [he]
  linarith

/-- The manuscript's signed smoothing lemma, including the appendix's
explicit constants `C₁ = 1/4` and `C₂ = 24`. -/
theorem manuscript_signed_smoothing_sup
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x)))
    (L : ℝ) (hL : 0 < L) :
    sSup (range (fun x => |μ.real (Iic x) - s (Iic x)|)) ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t|) +
        24 * (M : ℝ) / L := by
  let d : ℝ → ℝ := fun x => μ.real (Iic x) - s (Iic x)
  let I : ℝ := ∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t|
  have hd := manuscript_signed_cdf_difference_bounded μ s
  have hdm : Measurable d := manuscript_signed_cdf_difference_measurable μ s M hM
  have hg : ∀ x y, x ≤ y → d x - (M : ℝ) * (y - x) ≤ d y :=
    manuscript_signed_cdf_difference_growth μ s M hM
  have hR : ∀ y, |∫ z, d (y - z / L) ∂manuscriptSmoothingMeasure| ≤
      (1 / (2 * Real.pi)) * I := by
    intro y
    rw [manuscriptSmoothingMeasure_average_eq_convolution d L hL y]
    exact manuscript_signed_smoothing_convolution_bound μ s hs hμ hs1 L hL y
  have hε : manuscriptSmoothingMeasure.real (Ioi 16) < 1 := by
    linarith [manuscriptSmoothingMeasure_tail]
  have hb := manuscript_smoothing_average_bound manuscriptSmoothingMeasure d hdm
    (1 + s.toJordanDecomposition.posPart.real univ + s.toJordanDecomposition.negPart.real univ)
    M 16 L ((1 / (2 * Real.pi)) * I) hd M.coe_nonneg hL hg
    manuscriptSmoothingMeasure_loss_integrable manuscriptSmoothingMeasure_loss_plus_integrable
    manuscriptSmoothingMeasure_tail_symmetry manuscriptSmoothingMeasure_loss_symmetry hε hR
  have hI : 0 ≤ I := integral_nonneg (fun t => div_nonneg (norm_nonneg _) (abs_nonneg _))
  exact manuscript_smoothing_final_constants _ I M L
    (manuscriptSmoothingMeasure.real (Ioi 16))
    (∫ z, max (16 - z) 0 ∂manuscriptSmoothingMeasure)
    hI M.coe_nonneg hL ENNReal.toReal_nonneg manuscriptSmoothingMeasure_tail
    manuscriptSmoothingMeasure_loss_lt_eighteen hb

/-- Pointwise form of the same lemma, suitable for all later manuscript bounds. -/
theorem manuscript_signed_smoothing
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x)))
    (L : ℝ) (hL : 0 < L) (x : ℝ) :
    |μ.real (Iic x) - s (Iic x)| ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t|) +
        24 * (M : ℝ) / L := by
  have hb : BddAbove (range (fun x => |μ.real (Iic x) - s (Iic x)|)) := by
    refine ⟨1 + s.toJordanDecomposition.posPart.real univ +
      s.toJordanDecomposition.negPart.real univ, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact manuscript_signed_cdf_difference_bounded μ s y
  exact (le_csSup hb (mem_range_self x)).trans
    (manuscript_signed_smoothing_sup μ s hs hμ hs1 M hM L hL)

end BerryEsseen
