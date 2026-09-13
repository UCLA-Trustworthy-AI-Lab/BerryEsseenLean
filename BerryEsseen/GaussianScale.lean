import BerryEsseen.GaussianBounds

/-! Uniform second-order error for the Gaussian scale perturbation. -/
noncomputable section
open Set
namespace BerryEsseen

def gaussianScaleArgument (u ell : ℝ) : ℝ := u / Real.sqrt (1 - ell)

def gaussianScaleFirst (u ell : ℝ) : ℝ :=
  gaussianScaleArgument u ell * standardNormalDensity (gaussianScaleArgument u ell) / (2 * (1 - ell))

def gaussianScaleSecond (u ell : ℝ) : ℝ :=
  (3 * gaussianScaleArgument u ell - gaussianScaleArgument u ell ^ 3) *
    standardNormalDensity (gaussianScaleArgument u ell) / (4 * (1 - ell) ^ 2)

theorem gaussianScaleArgument_hasDerivAt (u ell : ℝ) (hell : ell < 1) :
    HasDerivAt (gaussianScaleArgument u) (gaussianScaleArgument u ell / (2 * (1 - ell))) ell := by
  have ha : 0 < 1 - ell := sub_pos.2 hell
  have hs : Real.sqrt (1 - ell) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hs2 : Real.sqrt (1 - ell) ^ 2 = 1 - ell := Real.sq_sqrt ha.le
  have hd := ((hasDerivAt_const ell 1).sub (hasDerivAt_id ell)).sqrt ha.ne'
  convert (hasDerivAt_const ell u).div hd hs using 1
  dsimp [gaussianScaleArgument]
  field_simp
  rw [hs2]
  ring

theorem gaussianScale_hasDerivAt (u ell : ℝ) (hell : ell < 1) :
    HasDerivAt (fun t => normalCDF (gaussianScaleArgument u t)) (gaussianScaleFirst u ell) ell := by
  convert (normalCDF_hasDerivAt _).comp ell (gaussianScaleArgument_hasDerivAt u ell hell) using 1
  unfold gaussianScaleFirst
  ring

theorem gaussianScaleFirst_hasDerivAt (u ell : ℝ) (hell : ell < 1) :
    HasDerivAt (gaussianScaleFirst u) (gaussianScaleSecond u ell) ell := by
  have ha : 0 < 1 - ell := sub_pos.2 hell
  have hd := (gaussian_x_density_hasDerivAt (gaussianScaleArgument u ell)).comp ell
    (gaussianScaleArgument_hasDerivAt u ell hell)
  have hden := (((hasDerivAt_const ell 1).sub (hasDerivAt_id ell)).const_mul 2)
  convert hd.div hden (by dsimp; positivity) using 1
  dsimp [gaussianScaleFirst, gaussianScaleSecond]
  field_simp
  ring

theorem gaussianScaleSecond_bound (u ell : ℝ) (hell : ell ∈ Icc 0 (1 / 2)) :
    |gaussianScaleSecond u ell| ≤ 18 * phi0 := by
  have ha : 0 < 1 - ell := by linarith [hell.2]
  have hb : 1 ≤ 4 * (1 - ell) ^ 2 := by nlinarith [hell.2]
  rw [gaussianScaleSecond, abs_div, abs_of_pos (by positivity : 0 < 4 * (1 - ell) ^ 2)]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (1 - ell) ^ 2)).2
  have h := gaussian_third_derivative_bound (gaussianScaleArgument u ell)
  have hp := phi0_pos
  nlinarith

theorem gaussian_scale_remainder (u d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    |normalCDF (u / Real.sqrt (1 - d)) - normalCDF u -
      d * u * standardNormalDensity u / 2| ≤ 9 * phi0 * d ^ 2 := by
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : d * t ∈ Icc 0 (1 / 2) :=
    ⟨mul_nonneg hd.1 ht.1, (mul_le_mul_of_nonneg_left ht.2 hd.1).trans (by simpa using hd.2)⟩
  have hlt (t : ℝ) (ht : t ∈ Icc 0 1) : d * t < 1 := by linarith [(hmem t ht).2]
  have h₁ (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun v => normalCDF (gaussianScaleArgument u (d * v)))
        (d * gaussianScaleFirst u (d * t)) t := by
    convert (gaussianScale_hasDerivAt u (d * t) (hlt t ht)).comp t
      ((hasDerivAt_id t).const_mul d) using 1 <;> (dsimp; ring)
  have h₂ (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun v => d * gaussianScaleFirst u (d * v))
        (d ^ 2 * gaussianScaleSecond u (d * t)) t := by
    convert ((gaussianScaleFirst_hasDerivAt u (d * t) (hlt t ht)).comp t
      ((hasDerivAt_id t).const_mul d)).const_mul d using 1 <;> (dsimp; ring)
  have hb (t : ℝ) (ht : t ∈ Icc 0 1) :
      |d ^ 2 * gaussianScaleSecond u (d * t)| ≤ d ^ 2 * (18 * phi0) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
    exact mul_le_mul_of_nonneg_left (gaussianScaleSecond_bound u (d * t) (hmem t ht)) (sq_nonneg d)
  have h := taylor_second_abs _ _ _ (d ^ 2 * (18 * phi0)) h₁ h₂ hb
  simp only [mul_one, mul_zero, gaussianScaleArgument, sub_zero, Real.sqrt_one, div_one,
    gaussianScaleFirst] at h
  convert h using 1
  · congr 1; ring
  · ring

end BerryEsseen
