import BerryEsseen.FiniteRetention

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem realPhase_spatial_difference (u x y : ℝ) :
    ‖realPhase u x - realPhase u y‖ ≤ |u| * |x - y| := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (realPhase_hasDerivAt v u).hasDerivWithinAt)
    (fun v _ => show ‖Complex.I * (u : ℂ) * realPhase v u‖ ≤ |u| by
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        realPhase_norm, one_mul, mul_one, le_refl])
    (mem_univ y) (mem_univ x)
  simpa only [realPhase, mul_comm x u, mul_comm y u, Real.norm_eq_abs] using h

theorem charFun_map_difference_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : Integrable (fun x => |x - g x|) μ) (u : ℝ) :
    ‖charFun μ u - charFun (μ.map g) u‖ ≤ |u| * (∫ x, |x - g x| ∂μ) := by
  have hphase : Integrable (fun x => realPhase u (g x)) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold realPhase; fun_prop)
    exact ae_of_all _ (fun x => (realPhase_norm u (g x)).le)
  rw [charFun_eq_integral_realPhase, charFun_eq_integral_realPhase,
    integral_map hg.aemeasurable (by unfold realPhase; fun_prop),
    ← integral_sub (realPhase_integrable μ u) hphase]
  calc
    _ ≤ ∫ x, ‖realPhase u x - realPhase u (g x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |u| * |x - g x| ∂μ := integral_mono_ae
      ((realPhase_integrable μ u).sub hphase).norm (hi.const_mul |u|)
      (ae_of_all _ (fun x => realPhase_spatial_difference u x (g x)))
    _ = _ := integral_const_mul _ _

theorem charFun_conditioning_norm_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Set ℝ) (hs : MeasurableSet s) (hnz : μ s ≠ 0) (u : ℝ) :
    ‖charFun μ u‖ ≤ (1 - μ.real sᶜ) * ‖charFun (ProbabilityTheory.cond μ s) u‖ + μ.real sᶜ := by
  have hmass : μ.real s ≠ 0 := (ENNReal.toReal_pos hnz (measure_ne_top _ _)).ne'
  have hcond : μ.real s • charFun (ProbabilityTheory.cond μ s) u = ∫ x in s, realPhase u x ∂μ := by
    rw [charFun_eq_integral_realPhase, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv, smul_smul]
    change (μ.real s * (μ.real s)⁻¹) • (∫ x in s, realPhase u x ∂μ) = _
    rw [mul_inv_cancel₀ hmass, one_smul]
  have hsplit := integral_add_compl hs (realPhase_integrable μ u)
  rw [← charFun_eq_integral_realPhase μ u, ← hcond] at hsplit
  have htail : ‖∫ x in sᶜ, realPhase u x ∂μ‖ ≤ μ.real sᶜ := by
    have h := norm_integral_le_of_norm_le_const (μ := μ.restrict sᶜ) (f := realPhase u)
      (ae_of_all _ (fun x => (realPhase_norm u x).le))
    simpa only [one_mul, measureReal_restrict_apply_univ] using h
  rw [← hsplit]
  have htri := norm_add_le (μ.real s • charFun (ProbabilityTheory.cond μ s) u)
    (∫ x in sᶜ, realPhase u x ∂μ)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] at htri
  have hcomp := probReal_compl_eq_one_sub hs (μ := μ)
  rw [hcomp] at htail ⊢
  nlinarith only [htri, htail]

theorem charFun_rounding_retention_bound (P : StandardizedLaw) (a h τ u : ℝ)
    (hh : 0 < h) (hτ : 0 ≤ τ) (hsupp : P.measure.support ⊆ Icc (-6) 6)
    (hsmall : ((latticeRoundingPoints a h).card : ℝ) * τ < 1) :
    let μ := latticeRoundedMeasure P a h
    let s : Set ℝ := (retainedAtoms μ (latticeRoundingPoints a h) τ : Set ℝ)
    ‖charFun P.measure u‖ ≤ (1 - μ.real sᶜ) *
      ‖charFun (retainedMeasure μ (latticeRoundingPoints a h) τ) u‖ + μ.real sᶜ +
      |u| * (∫ x, |x - latticeRound a h x| ∂P.measure) := by
  dsimp only
  let μ := latticeRoundedMeasure P a h
  let F := latticeRoundingPoints a h
  letI : IsProbabilityMeasure μ := latticeRoundedMeasure_probability P a h
  have hF : ∀ᵐ x ∂μ, x ∈ F := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact latticeRoundedMeasure_support P a h hh hsupp hx
  have hnz := retained_mass_nonzero μ F τ hτ hF hsmall
  have hcond := charFun_conditioning_norm_bound μ (retainedAtoms μ F τ : Set ℝ)
    (retainedAtoms μ F τ).finite_toSet.measurableSet hnz u
  have hmap := charFun_map_difference_bound P.measure (latticeRound a h)
    (latticeRound_measurable a h) (latticeRound_error_integrable P.measure a h hh).1 u
  have ht := norm_sub_norm_le (charFun P.measure u) (charFun μ u)
  change ‖charFun P.measure u - charFun μ u‖ ≤ _ at hmap
  change ‖charFun P.measure u‖ ≤ _
  change ‖charFun μ u‖ ≤ (1 - μ.real (retainedAtoms μ F τ : Set ℝ)ᶜ) *
    ‖charFun (retainedMeasure μ F τ) u‖ + μ.real (retainedAtoms μ F τ : Set ℝ)ᶜ at hcond
  linarith only [hmap, ht, hcond]

end BerryEsseen
