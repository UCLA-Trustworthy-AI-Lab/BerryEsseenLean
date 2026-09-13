import BerryEsseen.ManuscriptLocalMass
import BerryEsseen.EffectiveJitterGap

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_edgeworth_shift_two (n : ℕ) (hn : 1 ≤ n) (κ b x : ℝ)
    (hκ : |κ| ≤ 2) (hb : |b| ≤ 5 / 2) :
    |Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + b / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope b κ x| ≤ 2 / Real.sqrt (n : ℝ) := by
  have hb2 : b ^ 2 ≤ 25 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    norm_num [sq_abs] at h
    exact h
  have hm := mul_le_mul hκ hb (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 2)
  have hc : b ^ 2 / 32 + 5 * |κ| * |b| / 48 ≤ 2 := by nlinarith only [hb2, hm]
  exact (manuscript_edgeworthCDF_shift_remainder n hn κ b x).trans
    (div_le_div_of_nonneg_right hc (Real.sqrt_nonneg _))

theorem manuscript_jitter_gap_edgeworth_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (m σ κ E D x : ℝ) (hσ : 0 < σ) (hσlo : 0.48 ≤ σ) (hκ : |κ| ≤ 2)
    (hJ : ∀ y : ℝ, Real.sqrt (n : ℝ) * |cdf (μ ∗ uniformJitter 1) y -
      edgeworthCDF n κ ((y - m) / (σ * Real.sqrt (n : ℝ)))| ≤ E)
    (hplus : D / Real.sqrt (n : ℝ) ≤ cdf (μ ∗ uniformJitter 1) (x + 1 / 2) - cdf μ x)
    (hminus : D / Real.sqrt (n : ℝ) ≤ cdf μ x - cdf (μ ∗ uniformJitter 1) (x - 1 / 2)) :
    Real.sqrt (n : ℝ) * |cdf μ x - normalCDF ((x - m) / (σ * Real.sqrt (n : ℝ)))| ≤
      phi0 * (1 / (2 * σ) + |κ| / 6) - D + E + 2 / Real.sqrt (n : ℝ) := by
  let r := Real.sqrt (n : ℝ)
  let z := (x - m) / (σ * r)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hJU := hJ (x + 1 / 2)
  have hJL := hJ (x - 1 / 2)
  have huarg : ((x + 1 / 2) - m) / (σ * Real.sqrt (n : ℝ)) = z + σ⁻¹ / (2 * r) := by dsimp [z, r]; field_simp; ring
  have hlarg : ((x - 1 / 2) - m) / (σ * Real.sqrt (n : ℝ)) = z + (-σ⁻¹) / (2 * r) := by dsimp [z, r]; field_simp; ring
  rw [huarg] at hJU
  rw [hlarg] at hJL
  have habs : ∀ a : ℝ, r * |a| ≤ E → |r * a| ≤ E := by intro a ha; simpa only [abs_mul, abs_of_pos hr] using ha
  have hju := abs_le.mp (habs _ hJU)
  have hjl := abs_le.mp (habs _ hJL)
  have hh : |σ⁻¹| ≤ 5 / 2 := by
    rw [abs_of_pos (inv_pos.mpr hσ), inv_eq_one_div]
    apply (div_le_iff₀ hσ).mpr
    linarith only [hσlo]
  have hu := abs_le.mp (manuscript_edgeworth_shift_two n hn κ σ⁻¹ z hκ hh)
  have hl := abs_le.mp (manuscript_edgeworth_shift_two n hn κ (-σ⁻¹) z hκ (by simpa only [abs_neg] using hh))
  have henU := (abs_le.mp (edgeworthEnvelope_abs_bound σ⁻¹ κ z)).2
  have henL := (abs_le.mp (edgeworthEnvelope_abs_bound (-σ⁻¹) κ z)).1
  rw [abs_of_pos (inv_pos.mpr hσ)] at henU
  rw [abs_neg, abs_of_pos (inv_pos.mpr hσ)] at henL
  have hp := mul_le_mul_of_nonneg_left hplus hr.le
  have hm := mul_le_mul_of_nonneg_left hminus hr.le
  change r * (D / r) ≤ _ at hp hm
  rw [mul_div_cancel₀ _ hr.ne'] at hp hm
  have hid : phi0 * (1 / (2 * σ) + |κ| / 6) = (σ⁻¹ / 2 + |κ| / 6) * phi0 := by ring
  rw [hid]
  change r * |cdf μ x - normalCDF z| ≤ _
  rw [← abs_of_pos hr, ← abs_mul, abs_le]
  constructor <;> change _ ≤ _ <;>
    nlinarith only [hju.1, hju.2, hjl.1, hjl.2, hu.1, hu.2, hl.1, hl.2, henU, henL, hp, hm]

end BerryEsseen
