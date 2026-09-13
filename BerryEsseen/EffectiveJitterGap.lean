import BerryEsseen.EffectiveLocalMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem uniformJitter_backward_half_gap (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (1 / 2 : ℝ) * μ.real (Ioo (x - 1 / 2) x) ≤
      cdf μ x - cdf (μ ∗ uniformJitter 1) (x - 1 / 2) := by
  let G := fun t : ℝ => -cdf μ (-t)
  have hG : Monotone G := by
    intro a b hab
    exact neg_le_neg (monotone_cdf μ (neg_le_neg hab))
  have h := jitter_average_controls_increment G hG (-x) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hid : (fun s : ℝ => G (-x + s) - G (-x)) = (fun s => cdf μ x - cdf μ (x - s)) := by
    funext s
    dsimp only [G]
    rw [neg_neg, show -(-x + s) = x - s by ring]
    ring
  rw [hid] at h
  have hh : G (-x + 1 / 2) - G (-x) = cdf μ x - cdf μ (x - 1 / 2) := by
    dsimp only [G]
    rw [neg_neg, show -(-x + 1 / 2) = x - 1 / 2 by ring]
    ring
  rw [hh] at h
  norm_num at h
  have hanti : Antitone (fun s : ℝ => cdf μ (x - s)) := by
    intro a b hab
    exact monotone_cdf μ (by linarith)
  have havg := uniformJitter_cdf_backward_average μ 1 (by norm_num) x
  simp only [div_one] at havg
  have hi : (∫ s in (0 : ℝ)..1, cdf μ x - cdf μ (x - s)) =
      cdf μ x - cdf (μ ∗ uniformJitter 1) (x - 1 / 2) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hanti.intervalIntegrable,
      intervalIntegral.integral_const, ← havg]
    simp
  rw [hi] at h
  have hmass := measureReal_mono (μ := μ) (show Ioo (x - 1 / 2) x ⊆ Ioc (x - 1 / 2) x from Ioo_subset_Ioc_self)
  rw [← cdf_interval_mass μ (by linarith : x - 1 / 2 ≤ x)] at hmass
  linarith

theorem edgeworthShiftConstant_le_four (h : ℝ) (hh : |h| ≤ 5 / 2) :
    edgeworthShiftConstant h ≤ 4 := by
  have hh0 := abs_nonneg h
  have hh2 : h ^ 2 ≤ 25 / 4 := by
    have h2 := pow_le_pow_left₀ hh0 hh 2
    norm_num [sq_abs] at h2 ⊢
    exact h2
  unfold edgeworthShiftConstant
  have hpoly : 0 ≤ 3 * h ^ 2 / 8 + 3 * |h| := by positivity
  have hmul := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le hpoly
  nlinarith

theorem jitter_gap_edgeworth_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (m σ κ E D x : ℝ) (hσ : 0 < σ) (hκ : |κ| ≤ 2)
    (hJ : ∀ y : ℝ, Real.sqrt (n : ℝ) * |cdf (μ ∗ uniformJitter 1) y -
      edgeworthCDF n κ ((y - m) / (σ * Real.sqrt (n : ℝ)))| ≤ E)
    (hplus : D / Real.sqrt (n : ℝ) ≤ cdf (μ ∗ uniformJitter 1) (x + 1 / 2) - cdf μ x)
    (hminus : D / Real.sqrt (n : ℝ) ≤ cdf μ x - cdf (μ ∗ uniformJitter 1) (x - 1 / 2)) :
    Real.sqrt (n : ℝ) * |cdf μ x - normalCDF ((x - m) / (σ * Real.sqrt (n : ℝ)))| ≤
      phi0 * (1 / (2 * σ) + |κ| / 6) - D + E + edgeworthShiftConstant σ⁻¹ / Real.sqrt (n : ℝ) := by
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
  have hu := abs_le.mp (edgeworthCDF_shift_remainder n hn κ σ⁻¹ z hκ)
  have hl := edgeworthCDF_shift_remainder n hn κ (-σ⁻¹) z hκ
  rw [edgeworthShiftConstant_neg] at hl
  have hl := abs_le.mp hl
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
