import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! Order and integral estimates underlying the smoothing envelopes and
the flat-contact argument. These do not assert the Edgeworth expansion. -/
open MeasureTheory Filter Set
open scoped Topology
namespace BerryEsseen

/-- The exact CDF sandwich for bounded additive jitter, before taking real values. -/
theorem bounded_jitter_sandwich (μ : Measure (ℝ × ℝ)) (a b t : ℝ)
    (hU : ∀ᵐ z ∂μ, a ≤ z.2 ∧ z.2 ≤ b) :
    μ {z | z.1 + z.2 ≤ t + a} ≤ μ {z | z.1 ≤ t} ∧
    μ {z | z.1 ≤ t} ≤ μ {z | z.1 + z.2 ≤ t + b} := by
  constructor
  · apply measure_mono_ae
    filter_upwards [hU] with z hz
    change z.1 + z.2 ≤ t + a → z.1 ≤ t
    intro h; linarith [hz.1]
  · apply measure_mono_ae
    filter_upwards [hU] with z hz
    change z.1 ≤ t → z.1 + z.2 ≤ t + b
    intro h; linarith [hz.2]

/-- Monotonicity converts a small averaged CDF increment into a small
increment on each interval shorter than h, as used in support separation. -/
theorem jitter_average_controls_increment (G : ℝ → ℝ) (hG : Monotone G)
    (u h d : ℝ) (hh : 0 < h) (hd : 0 ≤ d) (hdh : d ≤ h) :
    (h - d) / h * (G (u + d) - G u) ≤
      (∫ s in (0 : ℝ)..h, G (u + s) - G u) / h := by
  let f : ℝ → ℝ := fun s => G (u + s) - G u
  have hf : Monotone f := by
    intro x y hxy
    exact sub_le_sub_right (hG (add_le_add_right hxy u)) _
  have hfirst : 0 ≤ ∫ s in (0 : ℝ)..d, f s := by
    apply intervalIntegral.integral_nonneg hd
    intro s hs
    dsimp [f]
    exact sub_nonneg.2 (hG (by linarith [hs.1]))
  have hlast : (h - d) * f d ≤ ∫ s in d..h, f s := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hdh
      (intervalIntegrable_const (c := f d)) hf.intervalIntegrable
      (fun s hs => hf hs.1)
    simpa using hi
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := d) (c := h) (μ := volume)
    hf.intervalIntegrable hf.intervalIntegrable
  have hb : (h - d) * f d ≤ ∫ s in (0 : ℝ)..h, f s := by linarith
  have hout := div_le_div_of_nonneg_right hb hh.le
  simpa [f, div_mul_eq_mul_div] using hout

/-- A positive lower bound on the surviving fraction is sufficient for flatness. -/
theorem flat_increment_of_average (increment average : ℕ → ℝ) (q : ℝ)
    (hq : 0 < q)
    (hinc : ∀ j, 0 ≤ increment j)
    (hcontrol : ∀ᶠ j in atTop, q * increment j ≤ average j)
    (haverage : Tendsto average atTop (𝓝 0)) :
    Tendsto increment atTop (𝓝 0) := by
  have hu : ∀ᶠ j in atTop, increment j ≤ average j / q := by
    filter_upwards [hcontrol] with j hj
    apply (le_div_iff₀ hq).2
    simpa [mul_comm] using hj
  have ht : Tendsto (fun j => average j / q) atTop (𝓝 0) := by
    simpa using haverage.div_const q
  exact squeeze_zero' (Eventually.of_forall hinc) hu ht

end BerryEsseen
