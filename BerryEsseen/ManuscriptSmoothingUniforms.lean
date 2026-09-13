import BerryEsseen.ManuscriptUniformConvolution

/-! The triangular density used in the Fourier calculation is exactly the
law of two uniforms on [-1/4,1/4]; two such laws are exactly four uniforms.
The first density identity is computed from interval overlap, before taking
Fourier transforms. The four-uniform density is the genuine convolution. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BerryEsseen

def manuscriptTriangleMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (manuscriptTriangle x))

instance : IsFiniteMeasure manuscriptTriangleMeasure :=
  isFiniteMeasure_withDensity_ofReal manuscriptTriangle_integrable.hasFiniteIntegral

/-- The triangle is the density of the sum of two actual independent uniforms. -/
theorem manuscriptTriangleMeasure_eq_two_uniforms :
    manuscriptTriangleMeasure = iidSumLaw (uniformJitter (1 / 2)) 2 :=
  manuscript_two_uniforms_density.symm

theorem manuscriptTriangleMeasure_charFun (t : ℝ) :
    charFun manuscriptTriangleMeasure t = (Real.sinc (t / 4) : ℂ) ^ 2 := by
  letI := uniformJitter_probability (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [manuscriptTriangleMeasure_eq_two_uniforms, charFun_iidSumLaw,
    charFun_uniformJitter (1 / 2) (by norm_num)]
  congr 3
  ring

instance manuscriptTriangleMeasure_probability : IsProbabilityMeasure manuscriptTriangleMeasure := by
  rw [manuscriptTriangleMeasure_eq_two_uniforms]
  letI := uniformJitter_probability (show (0 : ℝ) < 1 / 2 by norm_num)
  infer_instance

/-- Thus the convolution of two triangular density laws is precisely the
four-uniform convolution invoked in the manuscript. -/
theorem manuscriptTwoTriangles_eq_four_uniforms :
    manuscriptTriangleMeasure ∗ manuscriptTriangleMeasure = iidSumLaw (uniformJitter (1 / 2)) 4 := by
  letI := uniformJitter_probability (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [manuscriptTriangleMeasure_eq_two_uniforms]
  change (uniformJitter (1/2) ∗ (uniformJitter (1/2) ∗ Measure.dirac 0)) ∗
      (uniformJitter (1/2) ∗ (uniformJitter (1/2) ∗ Measure.dirac 0)) =
    uniformJitter (1/2) ∗ (uniformJitter (1/2) ∗
      (uniformJitter (1/2) ∗ (uniformJitter (1/2) ∗ Measure.dirac 0)))
  simp only [Measure.conv_dirac_zero]
  rw [Measure.conv_assoc]

/-- The characteristic function of four uniforms is the sinc-fourth term
appearing in K's definition, with the exact 1/4 spatial scale. -/
theorem manuscript_four_uniforms_charFun (t : ℝ) :
    charFun (iidSumLaw (uniformJitter (1 / 2)) 4) t = (Real.sinc (t / 4) : ℂ) ^ 4 := by
  letI := uniformJitter_probability (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [charFun_iidSumLaw, charFun_uniformJitter (1 / 2) (by norm_num),
    show (1 / 2 : ℝ) * t / 2 = t / 4 by ring]

/-- The continuous density used for inversion is exactly that of four
independent uniforms, not merely a function with a matching name. -/
theorem manuscript_four_uniforms_density :
    iidSumLaw (uniformJitter (1/2)) 4 =
      volume.withDensity (fun x => ENNReal.ofReal (manuscriptFourUniformDensity x)) := by
  rw [← manuscriptTwoTriangles_eq_four_uniforms]
  exact manuscript_two_triangle_density

theorem manuscriptFourUniformDensity_continuous : Continuous manuscriptFourUniformDensity := by
  have he : manuscriptFourUniformDensity = fun x => (manuscriptDoubleTriangle x).re := by
    funext x
    rw [manuscriptDoubleTriangle_ofReal, Complex.ofReal_re]
  rw [he]
  exact Complex.continuous_re.comp manuscriptDoubleTriangle_continuous

/-- First transform the four genuine uniforms using their characteristic
function. This identity is subsequently inverted to obtain the kernel's
Fourier support, in the order used in the manuscript. -/
theorem manuscript_four_uniform_density_angular (t : ℝ) :
    manuscriptAngularFourier manuscriptDoubleTriangle t = (Real.sinc (t/4):ℂ)^4 := by
  have he : manuscriptAngularFourier manuscriptDoubleTriangle t =
      charFun (iidSumLaw (uniformJitter (1/2)) 4) t := by
    rw [manuscript_four_uniforms_density, charFun_eq_integral_realPhase,
      integral_withDensity_eq_integral_toReal_smul
        manuscriptFourUniformDensity_continuous.measurable.ennreal_ofReal (by simp)]
    simp only [ENNReal.toReal_ofReal (manuscriptFourUniformDensity_nonneg _), Complex.real_smul]
    unfold manuscriptAngularFourier
    apply integral_congr_ae
    filter_upwards with x
    rw [manuscriptDoubleTriangle_ofReal]
  rw [he, manuscript_four_uniforms_charFun]

end BerryEsseen
