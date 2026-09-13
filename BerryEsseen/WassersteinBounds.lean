import BerryEsseen.PublishedWasserstein
import BerryEsseen.LatticeParameter

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem standardized_first_absolute_moment_le_one (P : StandardizedLaw) :
    (∫ x, |x| ∂P.measure) ≤ 1 := by
  have h := integral_mono_ae (P.first_integrable.abs.const_mul 2)
    (P.second_integrable.add (integrable_const 1)) (by
      filter_upwards [] with x
      change 2 * |x| ≤ x ^ 2 + 1
      nlinarith [sq_nonneg (|x| - 1), sq_abs x])
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add P.second_integrable (integrable_const 1), P.second_one] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

theorem wassersteinOne_map_le (K : PublishedWassersteinDuality)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (hμ : Integrable (fun x : ℝ => x) μ) (hgi : Integrable g μ) :
    wassersteinOne (μ.map g) μ ≤ ∫ x, |g x - x| ∂μ := by
  letI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hν : Integrable (fun x : ℝ => x) (μ.map g) :=
    (integrable_map_measure (by fun_prop) hg.aemeasurable).mpr hgi
  apply wassersteinOne_le_of_lipschitz K (μ.map g) μ hν hμ
  intro f hf
  have hfi := lipschitz_one_integrable μ hμ f hf
  have hfν := lipschitz_one_integrable (μ.map g) hν f hf
  have hcomp : Integrable (fun x => f (g x)) μ :=
    (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable hg.aemeasurable).mp hfν
  rw [integral_map hg.aemeasurable hf.continuous.measurable.aestronglyMeasurable,
    ← integral_sub hcomp hfi]
  apply integral_mono_ae (hcomp.sub hfi) (hgi.sub hμ).abs
  filter_upwards [] with x
  exact (le_abs_self _).trans (lipschitz_one_pointwise f hf (g x) x)

theorem wassersteinOne_affine_standardized (K : PublishedWassersteinDuality)
    (μ : Measure ℝ) (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hmap : Z.measure = standardizedMeasure μ m σ) :
    wassersteinOne μ Z.measure ≤ |m| + |σ - 1| := by
  have hinv := inverse_standardized_representation μ Z m σ hσ hmap
  rw [hinv]
  have h := wassersteinOne_map_le K Z.measure (fun x => σ * x + m) (by fun_prop)
    Z.first_integrable ((Z.first_integrable.const_mul σ).add (integrable_const m))
  apply h.trans
  have hi := integral_mono_ae (((Z.first_integrable.const_mul σ).add (integrable_const m)).sub Z.first_integrable).abs
    ((Z.first_integrable.abs.const_mul |σ - 1|).add (integrable_const |m|)) (by
      filter_upwards [] with x
      change |σ * x + m - x| ≤ |σ - 1| * |x| + |m|
      rw [show σ * x + m - x = (σ - 1) * x + m by ring]
      simpa only [abs_mul] using abs_add_le ((σ - 1) * x) m)
  simp only [Pi.add_apply, Pi.sub_apply] at hi
  rw [integral_add (Z.first_integrable.abs.const_mul _) (integrable_const _), integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hm := mul_le_mul_of_nonneg_left (standardized_first_absolute_moment_le_one Z) (abs_nonneg (σ - 1))
  linarith

theorem wassersteinOne_conditioning (K : PublishedWassersteinDuality)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ) (hs : MeasurableSet s) (hnz : μ s ≠ 0)
    (hμ : Integrable (fun x : ℝ => x) μ) (R R' : ℝ)
    (hx : ∀ᵐ x ∂μ, |x| ≤ R) (hy : ∀ᵐ x ∂ProbabilityTheory.cond μ s, |x| ≤ R') :
    wassersteinOne μ (ProbabilityTheory.cond μ s) ≤ (R + R') * μ.real sᶜ := by
  let ν := ProbabilityTheory.cond μ s
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  have hν : Integrable (fun x : ℝ => x) ν := conditional_integrable_real μ s hnz _ hμ
  have hmass : 0 < μ.real s := ENNReal.toReal_pos hnz (measure_ne_top _ _)
  apply wassersteinOne_le_of_lipschitz K μ ν hμ hν
  intro f hf
  have hfi := lipschitz_one_integrable μ hμ f hf
  let c := ∫ x, f x ∂ν
  have hc : |c - f 0| ≤ R' := by
    apply (lipschitz_one_integral_center ν hν f hf).trans
    have h := integral_mono_ae hν.abs (integrable_const R') hy
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hid : (∫ x, f x ∂μ) - c = ∫ x in sᶜ, f x - c ∂μ := by
    rw [integral_sub hfi.restrict (integrable_const _)]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    have hi := integral_add_compl hs hfi
    have hcond : c * μ.real s = ∫ x in s, f x ∂μ := by
      dsimp only [c, ν]
      rw [conditional_integral_real, div_mul_cancel₀ _ hmass.ne']
    have hcomp := probReal_compl_eq_one_sub hs (μ := μ)
    rw [hcomp]
    nlinarith only [hi, hcond]
  have hpoint : ∀ᵐ x ∂μ.restrict sᶜ, ‖f x - c‖ ≤ R + R' := by
    filter_upwards [ae_restrict_of_ae hx] with x hx
    rw [Real.norm_eq_abs]
    have h := lipschitz_one_pointwise f hf x 0
    simp only [sub_zero] at h
    have htri := abs_sub_le (f x) (f 0) c
    rw [abs_sub_comm (f 0) c] at htri
    linarith
  change (∫ x, f x ∂μ) - c ≤ _
  rw [hid]
  have h := norm_integral_le_of_norm_le_const hpoint
  simp only [Real.norm_eq_abs, measureReal_restrict_apply_univ] at h
  exact (le_abs_self _).trans h

theorem wassersteinOne_reflected (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    wassersteinOne (μ.map (fun x => -x)) (ν.map (fun x => -x)) = wassersteinOne μ ν := by
  have hle (ρ η : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure η]
      (hρ : Integrable (fun x : ℝ => x) ρ) (hη : Integrable (fun x : ℝ => x) η) :
      wassersteinOne (ρ.map (fun x => -x)) (η.map (fun x => -x)) ≤ wassersteinOne ρ η := by
    letI : IsProbabilityMeasure (ρ.map (fun x => -x)) := Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (η.map (fun x => -x)) := Measure.isProbabilityMeasure_map (by fun_prop)
    have hiρ : Integrable (fun x : ℝ => x) (ρ.map (fun x => -x)) :=
      (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hρ.neg
    have hiη : Integrable (fun x : ℝ => x) (η.map (fun x => -x)) :=
      (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hη.neg
    apply wassersteinOne_le_of_lipschitz K _ _ hiρ hiη
    intro f hf
    have hcomp : LipschitzWith 1 (fun x => f (-x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [NNReal.coe_one, one_mul, dist_neg_neg] using hf.dist_le_mul (-x) (-y)
    rw [integral_map (by fun_prop) hf.continuous.measurable.aestronglyMeasurable,
      integral_map (by fun_prop) hf.continuous.measurable.aestronglyMeasurable]
    exact lipschitz_integral_le_wassersteinOne K ρ η hρ hη _ hcomp
  apply le_antisymm (hle μ ν hμ hν)
  letI : IsProbabilityMeasure (μ.map (fun x => -x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (ν.map (fun x => -x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  have hiμ : Integrable (fun x : ℝ => x) (μ.map (fun x => -x)) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hμ.neg
  have hiν : Integrable (fun x : ℝ => x) (ν.map (fun x => -x)) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hν.neg
  simpa only [reflected_measure_twice] using hle _ _ hiμ hiν

end BerryEsseen
