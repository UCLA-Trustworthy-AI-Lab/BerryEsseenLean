import BerryEsseen.ManuscriptDirectConvolution
import BerryEsseen.ManuscriptSmoothingDistribution

/-! The actual scaled sinc-fourth kernel has the manuscript's precise
truncated Fourier bound. The Fourier quotient follows from the weak derivative
of the CDF difference; Fourier inversion is applied to the actual convolution.
All kernel properties are proved internally. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace BerryEsseen

theorem manuscript_signed_smoothing_convolution_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun z : ℝ => |z|) μ)
    (hs1 : Integrable (fun z : ℝ => |z|) s.totalVariation)
    (L : ℝ) (hL : 0 < L) (x : ℝ) :
    |∫ z, (μ.real (Iic z) - s (Iic z)) *
        (L * manuscriptSmoothingKernel (L * (x - z)))| ≤
      (1 / (2 * Real.pi)) *
        ∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t| := by
  simpa only [manuscriptCDFConvolution, manuscriptScaledSmoothingKernel] using
    manuscriptCDFConvolution_bound_of_direct_inversion μ s hs hμ hs1 L hL
      (fun t ht =>
        manuscript_signed_cdf_difference_fourier_from_weak_derivative μ s hs hμ hs1 t ht) x

end BerryEsseen
