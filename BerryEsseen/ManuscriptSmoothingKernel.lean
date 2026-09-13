import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The actual sinc-fourth-power kernel in the manuscript's Lemma 2.1.
No smoothing inequality or kernel property is an external premise here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def manuscriptSmoothingKernel (x : ℝ) : ℝ :=
  (3 / (8 * Real.pi)) * Real.sinc (x / 4) ^ 4

theorem manuscriptSmoothingKernel_nonneg (x : ℝ) :
    0 ≤ manuscriptSmoothingKernel x := by
  unfold manuscriptSmoothingKernel
  positivity

theorem manuscriptSmoothingKernel_even (x : ℝ) :
    manuscriptSmoothingKernel (-x) = manuscriptSmoothingKernel x := by
  simp [manuscriptSmoothingKernel, neg_div]

theorem manuscriptSmoothingKernel_continuous : Continuous manuscriptSmoothingKernel := by
  unfold manuscriptSmoothingKernel
  fun_prop

theorem manuscriptSmoothingKernel_le_constant (x : ℝ) :
    manuscriptSmoothingKernel x ≤ 3 / (8 * Real.pi) := by
  have h := pow_le_pow_left₀ (abs_nonneg (Real.sinc (x / 4)))
    (Real.abs_sinc_le_one (x / 4)) 4
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ Real.sinc (x / 4) ^ 4)] at h
  norm_num at h
  unfold manuscriptSmoothingKernel
  exact mul_le_of_le_one_right (by positivity) h

theorem manuscriptSmoothingKernel_le_inverse_fourth (x : ℝ) (hx : x ≠ 0) :
    manuscriptSmoothingKernel x ≤ (3 / (8 * Real.pi)) * (256 / x ^ 4) := by
  have hsin : |Real.sinc (x / 4)| ≤ 4 / |x| := by
    rw [Real.sinc_of_ne_zero (div_ne_zero hx (by norm_num)), abs_div, abs_div]
    norm_num
    calc
      |Real.sin (x / 4)| / (|x| / 4) ≤ 1 / (|x| / 4) :=
        div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
      _ = 4 / |x| := by ring
  have hpow := pow_le_pow_left₀ (abs_nonneg (Real.sinc (x / 4))) hsin 4
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ Real.sinc (x / 4) ^ 4)] at hpow
  have hr : (4 / |x|) ^ 4 = 256 / x ^ 4 := by
    rw [div_pow, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]
    norm_num
  rw [hr] at hpow
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem manuscriptSmoothingKernel_envelope (x : ℝ) (hx : x ≠ 0) :
    manuscriptSmoothingKernel x ≤
      (3 / (8 * Real.pi)) * min 1 (256 / x ^ 4) := by
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ (3 : ℝ) / (8 * Real.pi)), mul_one]
  exact le_min (manuscriptSmoothingKernel_le_constant x)
    (manuscriptSmoothingKernel_le_inverse_fourth x hx)

theorem manuscript_inverse_power_integrable (m : ℕ) (hm : 1 < m)
    (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x ^ m)⁻¹) (Ioi a) := by
  have hmreal : (1 : ℝ) < m := by exact_mod_cast hm
  have h := integrableOn_Ioi_rpow_of_lt
    (show -(m : ℝ) < -1 by linarith) ha
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  simp [Real.rpow_neg (le_of_lt (ha.trans hx)), Real.rpow_natCast]

theorem manuscriptSmoothingKernel_integrableOn_tail (a : ℝ) (ha : 0 < a) :
    IntegrableOn manuscriptSmoothingKernel (Ioi a) := by
  apply ((manuscript_inverse_power_integrable 4 (by norm_num) a ha).const_mul
    ((3 / (8 * Real.pi)) * 256)).mono'
    manuscriptSmoothingKernel_continuous.measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (manuscriptSmoothingKernel_nonneg x)]
  simpa [div_eq_mul_inv, mul_assoc] using
    manuscriptSmoothingKernel_le_inverse_fourth x (ne_of_gt (ha.trans hx))

theorem manuscript_integrable_of_even (f : ℝ → ℝ) (he : ∀ x, f (-x) = f x)
    (hi : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hleft : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hi

theorem manuscriptSmoothingKernel_integrable : Integrable manuscriptSmoothingKernel := by
  apply manuscript_integrable_of_even manuscriptSmoothingKernel manuscriptSmoothingKernel_even
  have hcompact : IntegrableOn manuscriptSmoothingKernel (Ioc 0 4) :=
    (manuscriptSmoothingKernel_continuous.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 4 by norm_num)] using
    hcompact.union (manuscriptSmoothingKernel_integrableOn_tail 4 (by norm_num))

theorem manuscriptSmoothingKernel_first_moment_tail (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => |x| * manuscriptSmoothingKernel x) (Ioi a) := by
  apply ((manuscript_inverse_power_integrable 3 (by norm_num) a ha).const_mul
    ((3 / (8 * Real.pi)) * 256)).mono'
    (continuous_abs.mul manuscriptSmoothingKernel_continuous).measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := ha.trans hx
  change ‖|x| * manuscriptSmoothingKernel x‖ ≤
    (3 / (8 * Real.pi) * 256) * (x ^ 3)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg x) (manuscriptSmoothingKernel_nonneg x)), abs_of_pos hx0]
  have h := mul_le_mul_of_nonneg_left
    (manuscriptSmoothingKernel_le_inverse_fourth x hx0.ne') hx0.le
  calc
    x * manuscriptSmoothingKernel x ≤ x * ((3 / (8 * Real.pi)) * (256 / x ^ 4)) := h
    _ = (3 / (8 * Real.pi) * 256) * (x ^ 3)⁻¹ := by field_simp

theorem manuscriptSmoothingKernel_first_moment_integrable :
    Integrable (fun x : ℝ => |x| * manuscriptSmoothingKernel x) := by
  apply manuscript_integrable_of_even (fun x : ℝ => |x| * manuscriptSmoothingKernel x)
    (by intro x; simp [manuscriptSmoothingKernel_even])
  have hcompact : IntegrableOn (fun x : ℝ => |x| * manuscriptSmoothingKernel x) (Ioc 0 4) :=
    ((continuous_abs.mul manuscriptSmoothingKernel_continuous).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  simpa only [Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 4 by norm_num)] using
    hcompact.union (manuscriptSmoothingKernel_first_moment_tail 4 (by norm_num))

end BerryEsseen
