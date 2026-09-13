import BerryEsseen.ManuscriptSmoothingDouble
import BerryEsseen.JitterCharacteristic
import BerryEsseen.ManuscriptAngularInversion

/-! The actual uniform densities behind the manuscript's sinc-fourth kernel.
The two-uniform density is computed by interval overlap, without a Fourier
calculation for the triangular density. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Convolution
namespace BerryEsseen

def manuscriptUniformWeight : ℝ → ℝ≥0∞ :=
  (Icc (-(1/4 : ℝ)) (1/4)).indicator (fun _ => 2)

theorem manuscriptUniformWeight_measurable : Measurable manuscriptUniformWeight :=
  measurable_const.indicator measurableSet_Icc

theorem manuscriptUniform_withDensity :
    uniformJitter (1/2) = volume.withDensity manuscriptUniformWeight := by
  rw [manuscriptUniformWeight, withDensity_indicator measurableSet_Icc, withDensity_const]
  norm_num [uniformJitter]

theorem manuscript_uniform_overlap (x : ℝ) :
    4 * max (min (1/4) (x+1/4) - max (-(1/4)) (x-1/4)) 0 = manuscriptTriangle x := by
  unfold manuscriptTriangle
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, min_eq_left (show (1/4:ℝ) ≤ x+1/4 by linarith),
      max_eq_right (show -(1/4:ℝ) ≤ x-1/4 by linarith),
      mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4), mul_zero]
    congr 1
    ring
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonpos hx', min_eq_right (show x+1/4 ≤ (1/4:ℝ) by linarith),
      max_eq_left (show x-1/4 ≤ -(1/4:ℝ) by linarith),
      mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4), mul_zero]
    congr 1
    ring

/-- Integrating the product of the two uniform densities gives the overlap
length of two intervals, hence the triangular density. -/
theorem manuscriptUniformWeight_lconvolution (x : ℝ) :
    (manuscriptUniformWeight ⋆ₗ[volume] manuscriptUniformWeight) x =
      ENNReal.ofReal (manuscriptTriangle x) := by
  rw [lconvolution_def]
  have hp : (fun y : ℝ => manuscriptUniformWeight y * manuscriptUniformWeight (-y+x)) =
      (Icc (max (-(1/4:ℝ)) (x-1/4)) (min (1/4) (x+1/4))).indicator (fun _ => (4:ℝ≥0∞)) := by
    funext y
    have he : (y ∈ Icc (-(1/4:ℝ)) (1/4) ∧ -y+x ∈ Icc (-(1/4:ℝ)) (1/4)) ↔
        y ∈ Icc (max (-(1/4:ℝ)) (x-1/4)) (min (1/4) (x+1/4)) := by
      simp only [mem_Icc, max_le_iff, le_min_iff]
      constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;>
        constructor <;> constructor <;> linarith
    by_cases hy : y ∈ Icc (-(1/4:ℝ)) (1/4)
    · by_cases hz : -y+x ∈ Icc (-(1/4:ℝ)) (1/4)
      · simp only [manuscriptUniformWeight, indicator_of_mem hy, indicator_of_mem hz,
          indicator_of_mem (he.mp ⟨hy,hz⟩)]
        norm_num
      · have hn := mt he.mpr (show ¬(y ∈ Icc (-(1/4:ℝ)) (1/4) ∧
            -y+x ∈ Icc (-(1/4:ℝ)) (1/4)) from fun h => hz h.2)
        simp only [manuscriptUniformWeight, indicator_of_mem hy, indicator_of_notMem hz,
          indicator_of_notMem hn, mul_zero]
    · have hn := mt he.mpr (show ¬(y ∈ Icc (-(1/4:ℝ)) (1/4) ∧
          -y+x ∈ Icc (-(1/4:ℝ)) (1/4)) from fun h => hy h.1)
      simp only [manuscriptUniformWeight, indicator_of_notMem hy, indicator_of_notMem hn, zero_mul]
  rw [hp, lintegral_indicator measurableSet_Icc]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
  have hh := manuscript_uniform_overlap x
  rw [← hh]
  by_cases hg : 0 ≤ min (1/4:ℝ) (x+1/4) - max (-(1/4:ℝ)) (x-1/4)
  · rw [max_eq_left hg]
  · rw [max_eq_right (le_of_lt (lt_of_not_ge hg))]
    rw [mul_zero, ENNReal.ofReal_zero]
    exact ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (le_of_lt (lt_of_not_ge hg)))

theorem manuscript_two_uniforms_density :
    iidSumLaw (uniformJitter (1/2)) 2 =
      volume.withDensity (fun x => ENNReal.ofReal (manuscriptTriangle x)) := by
  letI := uniformJitter_probability (show (0:ℝ) < 1/2 by norm_num)
  have hi : iidSumLaw (uniformJitter (1/2)) 2 =
      uniformJitter (1/2) ∗ uniformJitter (1/2) := by
    change uniformJitter (1/2) ∗ (uniformJitter (1/2) ∗ Measure.dirac 0) = _
    rw [Measure.conv_dirac_zero]
  rw [hi, manuscriptUniform_withDensity,
    conv_withDensity_eq_lconvolution manuscriptUniformWeight_measurable manuscriptUniformWeight_measurable]
  congr 1
  exact funext manuscriptUniformWeight_lconvolution

def manuscriptFourUniformDensity (x : ℝ) : ℝ :=
  ∫ y : ℝ, manuscriptTriangle y * manuscriptTriangle (x-y)

theorem manuscriptFourUniformDensity_nonneg (x : ℝ) : 0 ≤ manuscriptFourUniformDensity x :=
  integral_nonneg (fun y => mul_nonneg (manuscriptTriangle_nonneg y) (manuscriptTriangle_nonneg (x-y)))

theorem manuscriptDoubleTriangle_ofReal (x : ℝ) :
    manuscriptDoubleTriangle x = (manuscriptFourUniformDensity x : ℂ) := by
  change (∫ y : ℝ, (manuscriptTriangle y : ℂ) * (manuscriptTriangle (x-y) : ℂ)) = _
  simp_rw [← Complex.ofReal_mul]
  exact integral_complex_ofReal

theorem manuscript_triangle_product_integrable (x : ℝ) :
    Integrable (fun y : ℝ => manuscriptTriangle y * manuscriptTriangle (x-y)) := by
  have hc : Continuous (fun y : ℝ => manuscriptTriangle y * manuscriptTriangle (x-y)) :=
    manuscriptTriangle_continuous.mul
      (manuscriptTriangle_continuous.comp (continuous_const.sub continuous_id))
  exact hc.integrable_of_hasCompactSupport manuscriptTriangle_compact.mul_right

theorem manuscript_two_triangle_density :
    (volume.withDensity (fun x => ENNReal.ofReal (manuscriptTriangle x))) ∗
      (volume.withDensity (fun x => ENNReal.ofReal (manuscriptTriangle x))) =
      volume.withDensity (fun x => ENNReal.ofReal (manuscriptFourUniformDensity x)) := by
  rw [conv_withDensity_eq_lconvolution manuscriptTriangle_continuous.measurable.ennreal_ofReal
    manuscriptTriangle_continuous.measurable.ennreal_ofReal]
  congr 1
  funext x
  rw [lconvolution_def, manuscriptFourUniformDensity,
    ofReal_integral_eq_lintegral_ofReal (manuscript_triangle_product_integrable x)
      (Filter.Eventually.of_forall (fun y =>
        mul_nonneg (manuscriptTriangle_nonneg y) (manuscriptTriangle_nonneg (x-y))))]
  apply lintegral_congr
  intro y
  rw [ENNReal.ofReal_mul (manuscriptTriangle_nonneg y)]
  rw [show -y+x = x-y by ring]

end BerryEsseen
