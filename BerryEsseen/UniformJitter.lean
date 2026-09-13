import BerryEsseen.ConvolutionContact
import BerryEsseen.JitterOrder
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The genuine uniform-jitter convolution, its exact averaging formula,
and the interval-mass inequality used in support separation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

def uniformJitter (h : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / h) • volume.restrict (Icc (-h / 2) (h / 2))

theorem uniformJitter_probability {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (uniformJitter h) := by
  constructor
  simp only [uniformJitter, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, smul_eq_mul]
  rw [show h / 2 - -h / 2 = h by ring, ← ENNReal.ofReal_mul (by positivity)]
  simp [ne_of_gt hh]

theorem uniformJitter_integral (h : ℝ) (f : ℝ → ℝ) (hh : 0 < h) :
    (∫ x, f x ∂uniformJitter h) = (∫ x in (-h / 2)..(h / 2), f x) / h := by
  rw [uniformJitter, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / h), smul_eq_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -h / 2 ≤ h / 2)]
  ring

theorem uniformJitter_cdf_average (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (u : ℝ) :
    cdf (μ ∗ uniformJitter h) (u + h / 2) =
      (∫ s in (0 : ℝ)..h, cdf μ (u + s)) / h := by
  letI := uniformJitter_probability hh
  rw [Measure.conv_comm, cdf_convolution_integral, uniformJitter_integral h _ hh]
  congr 1
  have he : (fun x : ℝ => cdf μ (u + h / 2 - x)) =
      (fun x => (fun s => cdf μ (u + s)) (h / 2 - x)) := by
    funext x
    congr 1
    ring
  rw [he]
  simpa only [sub_self, show h / 2 - -h / 2 = h by ring] using
    (intervalIntegral.integral_comp_sub_left (fun s => cdf μ (u + s))
      (a := -h / 2) (b := h / 2) (h / 2))

theorem uniformJitter_cdf_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (u : ℝ) :
    cdf (μ ∗ uniformJitter h) (u + h / 2) - cdf μ u =
      (∫ s in (0 : ℝ)..h, cdf μ (u + s) - cdf μ u) / h := by
  rw [uniformJitter_cdf_average μ hh u]
  have hm : Monotone (fun s => cdf μ (u + s)) :=
    (monotone_cdf μ).comp (monotone_const.add monotone_id)
  rw [intervalIntegral.integral_sub hm.intervalIntegrable intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem uniformJitter_controls_cdf_increment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (u d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) :
    (h - d) / h * (cdf μ (u + d) - cdf μ u) ≤
      cdf (μ ∗ uniformJitter h) (u + h / 2) - cdf μ u := by
  rw [uniformJitter_cdf_gap μ hh u]
  exact jitter_average_controls_increment (cdf μ) (monotone_cdf μ) u h d hh hd hdh

theorem cdf_interval_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) : cdf μ b - cdf μ a = μ.real (Ioc a b) := by
  rw [cdf_eq_real, cdf_eq_real]
  have h := measureReal_diff (Iic_subset_Iic.mpr hab) measurableSet_Iic (μ := μ)
  rw [Iic_diff_Iic] at h
  exact h.symm

theorem uniformJitter_controls_open_interval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) (u d : ℝ) (hd : 0 ≤ d) (hdh : d ≤ h) :
    (h - d) / h * μ.real (Ioo u (u + d)) ≤
      cdf (μ ∗ uniformJitter h) (u + h / 2) - cdf μ u := by
  have h1 := uniformJitter_controls_cdf_increment μ hh u d hd hdh
  rw [cdf_interval_mass μ (by linarith)] at h1
  exact (mul_le_mul_of_nonneg_left (measureReal_mono Ioo_subset_Ioc_self)
    (div_nonneg (sub_nonneg.mpr hdh) hh.le)).trans h1

end BerryEsseen
