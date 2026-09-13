import BerryEsseen.ManuscriptSignedSmoothing

/-! Density specialization of the proved original signed smoothing lemma. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory Filter
open scoped NNReal
namespace BerryEsseen

theorem manuscript_density_signed_first_moment (g : ℝ → ℝ)
    (hgm : Measurable g) (hg : Integrable g)
    (hxg : Integrable (fun x : ℝ => x * g x)) :
    Integrable (fun x : ℝ => |x|) (SignedMeasure.totalVariation (volume.withDensityᵥ g)) := by
  have hj := signedMeasure_density_jordan (volume.withDensityᵥ g) g hgm hg rfl
  change Integrable (fun x : ℝ => |x|)
    ((SignedMeasure.toJordanDecomposition (volume.withDensityᵥ g)).posPart +
      (SignedMeasure.toJordanDecomposition (volume.withDensityᵥ g)).negPart)
  rw [hj.1, hj.2]
  apply Integrable.add_measure
  · rw [integrable_withDensity_iff_integrable_smul' hgm.ennreal_ofReal (by simp)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    apply hxg.norm.mono' (by fun_prop)
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (le_max_right (g x) 0)]
    exact (mul_le_mul_of_nonneg_right
      (max_le (le_abs_self (g x)) (abs_nonneg (g x))) (abs_nonneg x)).trans_eq (mul_comm _ _)
  · rw [integrable_withDensity_iff_integrable_smul' hgm.neg.ennreal_ofReal (by simp)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    apply hxg.norm.mono' (by fun_prop)
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (le_max_right (-g x) 0)]
    exact (mul_le_mul_of_nonneg_right
      (max_le (neg_le_abs (g x)) (abs_nonneg (g x))) (abs_nonneg x)).trans_eq (mul_comm _ _)

theorem manuscript_density_primitive_lipschitz (g : ℝ → ℝ) (hg : Integrable g)
    (M : ℝ≥0) (hM : ∀ᵐ x : ℝ, |g x| ≤ (M : ℝ)) :
    LipschitzWith M (fun x => (volume.withDensityᵥ g) (Iic x)) := by
  have hordered (x y : ℝ) (hxy : x ≤ y) :
      |(volume.withDensityᵥ g) (Iic y) - (volume.withDensityᵥ g) (Iic x)| ≤
        (M : ℝ) * |y - x| := by
    rw [← signedMeasure_Ioc _ x y hxy, withDensityᵥ_apply hg measurableSet_Ioc]
    have hb := norm_setIntegral_le_of_norm_le_const_ae
      (μ := (volume : Measure ℝ)) (s := Ioc x y) (f := g) measure_Ioc_lt_top
      (by simpa only [Real.norm_eq_abs] using ae_restrict_of_ae hM)
    simpa only [Real.norm_eq_abs, Real.volume_real_Ioc, abs_of_nonneg (sub_nonneg.mpr hxy),
      max_eq_left (sub_nonneg.mpr hxy)] using hb
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · simpa only [abs_sub_comm] using hordered x y hxy
  · exact hordered y x hyx

theorem manuscript_density_smoothing_measurable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (hxg : Integrable (fun x : ℝ => x * g x)) (hmass : (∫ x, g x) = 1)
    (M L : ℝ) (hM : 0 < M) (hL : 0 < L)
    (hbound : ∀ᵐ x : ℝ, |g x| ≤ M) (x : ℝ) :
    |μ.real (Iic x) - ∫ y in Iic x, g y| ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - densityFourier g t‖ / |t|) +
        24 * M / L := by
  let s : SignedMeasure ℝ := volume.withDensityᵥ g
  have hs : s univ = 1 := by
    dsimp only [s]
    rw [withDensityᵥ_apply hg MeasurableSet.univ, Measure.restrict_univ]
    exact hmass
  have hμabs : Integrable (fun x : ℝ => |x|) μ := by
    simpa only [Real.norm_eq_abs] using hμ.norm
  have hs1 : Integrable (fun x : ℝ => |x|) s.totalVariation :=
    manuscript_density_signed_first_moment g hgm hg hxg
  let m : ℝ≥0 := ⟨M, hM.le⟩
  have hmlip : LipschitzWith m (fun x => s (Iic x)) :=
    manuscript_density_primitive_lipschitz g hg m hbound
  have hf : ∀ t, signedFourier s t = densityFourier g t :=
    signedFourier_eq_densityFourier s g hgm hg rfl
  have hb := manuscript_signed_smoothing μ s hs hμabs hs1 m hmlip L hL x
  simp_rw [hf] at hb
  rw [show s (Iic x) = ∫ y in Iic x, g y from withDensityᵥ_apply hg measurableSet_Iic] at hb
  exact hb

theorem manuscript_density_smoothing
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hxg : Integrable (fun x : ℝ => x * g x)) (hmass : (∫ x, g x) = 1)
    (M L : ℝ) (hM : 0 < M) (hL : 0 < L)
    (hbound : ∀ x : ℝ, |g x| ≤ M) (x : ℝ) :
    |μ.real (Iic x) - ∫ y in Iic x, g y| ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - densityFourier g t‖ / |t|) +
        24 * M / L := by
  let f := hg.aestronglyMeasurable.mk g
  have hgf : g =ᵐ[volume] f := hg.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable f := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hf : Integrable f := hg.congr hgf
  have hxf : Integrable (fun x : ℝ => x * f x) := hxg.congr (by
    filter_upwards [hgf] with y hy
    rw [hy])
  have hfmass : (∫ y, f y) = 1 := (integral_congr_ae hgf).symm.trans hmass
  have hfbound : ∀ᵐ y : ℝ, |f y| ≤ M := by
    filter_upwards [hgf] with y hy
    rw [← hy]
    exact hbound y
  have hb := manuscript_density_smoothing_measurable μ hμ f hfm hf hxf hfmass M L hM hL hfbound x
  have hset : (∫ y in Iic x, g y) = ∫ y in Iic x, f y :=
    integral_congr_ae (ae_restrict_of_ae hgf)
  have hFourier : ∀ t, densityFourier g t = densityFourier f t := by
    intro t
    apply integral_congr_ae
    filter_upwards [hgf] with y hy
    rw [hy]
  simp_rw [← hFourier] at hb
  rwa [← hset] at hb

/-- A proved inhabitant of the historical smoothing interface. This is not
an external premise: all its fields follow from the manuscript's sinc⁴ proof. -/
theorem manuscriptSignedSmoothing : PublishedSignedSmoothing := by
  constructor
  intro μ hprob hμ g hg hxg hmass M L hM hL hbound _hint x
  letI := hprob
  exact manuscript_density_smoothing μ hμ g hg hxg hmass M L hM hL hbound x

end BerryEsseen
