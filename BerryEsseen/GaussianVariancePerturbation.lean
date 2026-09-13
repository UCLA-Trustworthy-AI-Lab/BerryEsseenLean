import BerryEsseen.GaussianScale

noncomputable section
open Set
namespace BerryEsseen

theorem gaussianScaleFirst_nonpositive_bound (u ell : ℝ) (hell : ell ≤ 0) :
    |gaussianScaleFirst u ell| ≤ 3 * phi0 / 2 := by
  have hd : 0 < 2 * (1 - ell) := by linarith
  rw [gaussianScaleFirst, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  have h := gaussian_first_monomial_bound (gaussianScaleArgument u ell)
  have hp := phi0_pos
  nlinarith

theorem gaussian_variance_ratio_bound (z r : ℝ) (hr : 0 ≤ r) :
    |normalCDF (z / Real.sqrt (1 + r)) - normalCDF z| ≤ 3 * phi0 / 2 * r := by
  have hd (ell : ℝ) (hell : ell ∈ Icc (-r) 0) :
      HasDerivWithinAt (fun v => normalCDF (gaussianScaleArgument z v))
        (gaussianScaleFirst z ell) (Icc (-r) 0) ell :=
    (gaussianScale_hasDerivAt z ell (by linarith [hell.2])).hasDerivWithinAt
  have hb (ell : ℝ) (hell : ell ∈ Icc (-r) 0) : ‖gaussianScaleFirst z ell‖ ≤ 3 * phi0 / 2 := by
    rw [Real.norm_eq_abs]
    exact gaussianScaleFirst_nonpositive_bound z ell hell.2
  have h := (convex_Icc (-r) 0).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (show (0 : ℝ) ∈ Icc (-r) 0 by constructor <;> linarith)
    (show -r ∈ Icc (-r) 0 by constructor <;> linarith)
  simpa only [gaussianScaleArgument, sub_zero, sub_neg_eq_add, Real.sqrt_one, div_one,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg hr] using h

theorem gaussian_variance_perturbation_bound (z v s : ℝ) (hv : 0 < v) (hs : 0 ≤ s) :
    |normalCDF (z / Real.sqrt (v + s)) - normalCDF (z / Real.sqrt v)| ≤ 3 * phi0 * s / (2 * v) := by
  have h := gaussian_variance_ratio_bound (z / Real.sqrt v) (s / v) (div_nonneg hs hv.le)
  have he : (z / Real.sqrt v) / Real.sqrt (1 + s / v) = z / Real.sqrt (v + s) := by
    rw [div_div, ← Real.sqrt_mul hv.le]
    congr 2
    field_simp
  rw [he] at h
  convert h using 1 <;> ring

end BerryEsseen
