import BerryEsseen.ManuscriptSmoothingSqueeze
import BerryEsseen.ManuscriptSmoothingMeasure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Assembly of the original probabilistic convolution sandwich.
The bound R refers to the actual averaging integral, rather than an abstract substitute. -/
noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem manuscriptSmoothingMeasure_average_eq_convolution (d : ℝ → ℝ)
    (L : ℝ) (hL : 0 < L) (x : ℝ) :
    (∫ z, d (x - z / L) ∂manuscriptSmoothingMeasure) =
      ∫ z, d z * (L * manuscriptSmoothingKernel (L * (x - z))) := by
  rw [manuscriptSmoothingMeasure_integral]
  let f : ℝ → ℝ := fun z => manuscriptSmoothingKernel z * d (x - z / L)
  have hpoint : (fun z => d z * (L * manuscriptSmoothingKernel (L * (x - z)))) =
      (fun z => L * f (L * (x - z))) := by
    funext z
    dsimp [f]
    have he : x - L * (x - z) / L = z := by field_simp; ring
    rw [he]
    ring
  rw [hpoint, integral_const_mul]
  have hsub : (∫ z, f (L * (x - z))) = ∫ z, f (L * z) := by
    exact integral_sub_left_eq_self (fun z => f (L * z)) volume x
  rw [hsub, Measure.integral_comp_mul_left f L, smul_eq_mul,
    abs_of_pos (inv_pos.mpr hL)]
  change (∫ z, f z) = L * (L⁻¹ * ∫ z, f z)
  field_simp

theorem manuscript_integrable_bounded_composition (κ : Measure ℝ) [IsFiniteMeasure κ]
    (d q : ℝ → ℝ) (hdm : Measurable d) (hqm : Measurable q)
    (D : ℝ) (hd : ∀ x, |d x| ≤ D) : Integrable (fun z => d (q z)) κ := by
  apply (integrable_const D).mono' (hdm.comp hqm).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs] using hd (q z)

theorem manuscript_smoothing_average_bound
    (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (d : ℝ → ℝ) (hdm : Measurable d) (D M a L R : ℝ)
    (hd : ∀ x, |d x| ≤ D) (hM : 0 ≤ M) (hL : 0 < L)
    (hg : ∀ x y, x ≤ y → d x - M * (y - x) ≤ d y)
    (hmminus : Integrable (fun z : ℝ => max (a - z) 0) κ)
    (hmplus : Integrable (fun z : ℝ => max (a + z) 0) κ)
    (htail : κ.real (Iio (-a)) = κ.real (Ioi a))
    (hmoment : (∫ z, max (a + z) 0 ∂κ) = ∫ z, max (a - z) 0 ∂κ)
    (hε : κ.real (Ioi a) < 1)
    (hR : ∀ y, |∫ z, d (y - z / L) ∂κ| ≤ R) :
    (1 - 2 * κ.real (Ioi a)) * sSup (range (fun x => |d x|)) ≤
      R + (M / L) * (∫ z, max (a - z) 0 ∂κ) := by
  have hbpos : BddAbove (range d) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (hd x)⟩
  have hbneg : BddAbove (range (fun y => -d y)) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact (neg_le_abs _).trans (hd x)⟩
  apply manuscript_smoothing_take_sup d D (κ.real (Ioi a)) R
    ((M / L) * (∫ z, max (a - z) 0 ∂κ)) hd hε
  · intro x
    have hdm_lower : ∀ y, -sSup (range (fun z => -d z)) ≤ d y := by
      intro y
      have hh := le_csSup hbneg (mem_range_self y)
      linarith
    have hi : Integrable (fun z => d (x + (a - z) / L)) κ :=
      manuscript_integrable_bounded_composition κ d _ hdm (by fun_prop) D hd
    have hh := manuscript_smoothing_lower_integral κ d M
      (sSup (range (fun z => -d z))) a L x hM hL hdm_lower hg hi hmminus
    have heq : (∫ z, d (x + (a - z) / L) ∂κ) =
        ∫ z, d ((x + a / L) - z / L) ∂κ := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1
      ring
    rw [heq] at hh
    have hr := (abs_le.mp (hR (x + a / L))).2
    linarith
  · intro x
    have hdp : ∀ y, d y ≤ sSup (range d) := fun y => le_csSup hbpos (mem_range_self y)
    have hi : Integrable (fun z => d (x - (a + z) / L)) κ :=
      manuscript_integrable_bounded_composition κ d _ hdm (by fun_prop) D hd
    have hh := manuscript_smoothing_upper_integral κ d M
      (sSup (range d)) a L x hM hL hdp hg hi hmplus
    have heq : (∫ z, d (x - (a + z) / L) ∂κ) =
        ∫ z, d ((x - a / L) - z / L) ∂κ := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1
      ring
    rw [heq, htail, hmoment] at hh
    have hr := (abs_le.mp (hR (x - a / L))).1
    linarith
  · exact ENNReal.toReal_nonneg

end BerryEsseen
