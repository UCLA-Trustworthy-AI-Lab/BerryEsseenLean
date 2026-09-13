import BerryEsseen.BoundedJitterExpansion

/-! Uniform Taylor estimates for the upper and lower jitter envelopes. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def edgeworthEnvelope (h κ x : ℝ) : ℝ :=
  (h / 2 + κ / 6 * (1 - x ^ 2)) * standardNormalDensity x

def edgeworthShiftConstant (h : ℝ) : ℝ := phi0 * (3 * h ^ 2 / 8 + 3 * |h|)

theorem gaussianCDF_first_remainder (x a : ℝ) :
    |normalCDF (x + a) - normalCDF x - a * standardNormalDensity x| ≤ 3 * phi0 / 2 * a ^ 2 := by
  have hb : ∀ u, |-u * standardNormalDensity u| ≤ 3 * phi0 := by
    intro u
    simpa only [neg_mul, abs_neg] using gaussian_first_monomial_bound u
  simpa only [sq_abs] using taylor_second_global normalCDF standardNormalDensity
    (fun u => -u * standardNormalDensity u) (3 * phi0) normalCDF_hasDerivAt
    standardNormalDensity_hasDerivAt hb x a

theorem gaussian_second_polynomial_lipschitz (x y : ℝ) :
    |(1 - y ^ 2) * standardNormalDensity y - (1 - x ^ 2) * standardNormalDensity x| ≤
      18 * phi0 * |y - x| := by
  have hb : ∀ t, ‖(t ^ 3 - 3 * t) * standardNormalDensity t‖ ≤ 18 * phi0 := by
    intro t
    rw [Real.norm_eq_abs, show t ^ 3 - 3 * t = -(3 * t - t ^ 3) by ring, neg_mul, abs_neg]
    exact gaussian_third_derivative_bound t
  simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (gaussian_x_density_second_hasDerivAt t).hasDerivWithinAt)
    (fun t _ => hb t) (mem_univ x) (mem_univ y)

theorem edgeworthCDF_shift_remainder (n : ℕ) (hn : 1 ≤ n) (κ b x : ℝ) (hκ : |κ| ≤ 2) :
    |Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + b / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope b κ x| ≤ edgeworthShiftConstant b / Real.sqrt (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  let a := b / (2 * s)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  let A := normalCDF (x + a) - normalCDF x - a * standardNormalDensity x
  let B := (1 - (x + a) ^ 2) * standardNormalDensity (x + a) - (1 - x ^ 2) * standardNormalDensity x
  have hA : |A| ≤ 3 * phi0 / 2 * a ^ 2 := gaussianCDF_first_remainder x a
  have hB : |B| ≤ 18 * phi0 * |a| := by
    simpa only [add_sub_cancel_left] using gaussian_second_polynomial_lipschitz x (x + a)
  have hcoef : |κ / (6 * s)| ≤ 2 / (6 * s) := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
    exact div_le_div_of_nonneg_right hκ (by positivity)
  have he : s * (edgeworthCDF n κ (x + a) - normalCDF x) - edgeworthEnvelope b κ x =
      s * (A + κ / (6 * s) * B) := by
    dsimp [A, B, edgeworthCDF, edgeworthEnvelope, a, s]
    field_simp [hs.ne']
    <;> ring
  change |s * (edgeworthCDF n κ (x + a) - normalCDF x) - edgeworthEnvelope b κ x| ≤ _
  rw [he, abs_mul, abs_of_pos hs]
  have hbnd : |A + κ / (6 * s) * B| ≤ 3 * phi0 / 2 * a ^ 2 + 2 / (6 * s) * (18 * phi0 * |a|) := by
    calc
      _ ≤ |A| + |κ / (6 * s)| * |B| := by simpa only [abs_mul] using abs_add_le A (κ / (6 * s) * B)
      _ ≤ _ := add_le_add hA (mul_le_mul hcoef hB (abs_nonneg _) (by positivity))
  calc
    _ ≤ s * (3 * phi0 / 2 * a ^ 2 + 2 / (6 * s) * (18 * phi0 * |a|)) := mul_le_mul_of_nonneg_left hbnd hs.le
    _ = _ := by
      change _ = edgeworthShiftConstant b / s
      dsimp [a, edgeworthShiftConstant]
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      field_simp [hs.ne']
      <;> ring

theorem edgeworthShiftConstant_neg (h : ℝ) : edgeworthShiftConstant (-h) = edgeworthShiftConstant h := by
  simp only [edgeworthShiftConstant, neg_sq, abs_neg]

theorem edgeworthShiftConstant_scaled_tendsto_zero (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (h : ℝ) :
    Tendsto (fun j => edgeworthShiftConstant h / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))

end BerryEsseen
