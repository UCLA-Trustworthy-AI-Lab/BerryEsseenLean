import BerryEsseen.GaussianVariancePerturbation
import BerryEsseen.PublishedBernoulli
import BerryEsseen.ClusterStandardization

noncomputable section
open Set
namespace BerryEsseen

theorem sqrt_cube_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.sqrt y ^ 3) (3 / 2 * Real.sqrt x) x := by
  have h := ((hasDerivAt_id x).sqrt hx.ne').pow 3
  convert h using 1
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
  field_simp [(Real.sqrt_pos.2 hx).ne']

theorem sqrt_cube_increment_bound (v s : ℝ) (hv : 0 < v) (hs : 0 ≤ s) (hsv : s ≤ v) :
    |Real.sqrt (v + s) ^ 3 - Real.sqrt v ^ 3| ≤ 3 * Real.sqrt v * s := by
  have hd (x : ℝ) (hx : x ∈ Icc v (v + s)) :
      HasDerivWithinAt (fun y : ℝ => Real.sqrt y ^ 3) (3 / 2 * Real.sqrt x) (Icc v (v + s)) x :=
    (sqrt_cube_hasDerivAt x (hv.trans_le hx.1)).hasDerivWithinAt
  have hb (x : ℝ) (hx : x ∈ Icc v (v + s)) : ‖3 / 2 * Real.sqrt x‖ ≤ 3 * Real.sqrt v := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 3 / 2 * Real.sqrt x)]
    have hxsq := Real.sq_sqrt (hv.trans_le hx.1).le
    have hvsq := Real.sq_sqrt hv.le
    have hroot : Real.sqrt x ≤ 2 * Real.sqrt v := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg v, hx.2]
    linarith
  have h := (convex_Icc v (v + s)).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (show v ∈ Icc v (v + s) by constructor <;> linarith)
    (show v + s ∈ Icc v (v + s) by constructor <;> linarith)
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hs] using h

theorem perturbation_denominator_bounds (v s τ ρ : ℝ) (hv : 0 < v)
    (hτ : τ ∈ Icc (1 / 2) 1) (hs : s ≤ v / 16) (hρ : |ρ - v * τ| ≤ 4 * s) :
    v / 4 ≤ ρ ∧ v / 2 ≤ v * τ := by
  have hr := abs_le.1 hρ
  have ht := mul_le_mul_of_nonneg_left hτ.1 hv.le
  constructor <;> nlinarith

theorem perturbed_prefactor_bound (v s τ ρ : ℝ) (hv : v ∈ Ioc 0 1)
    (hτ : τ ∈ Icc (1 / 2) 1) (hs : s ∈ Icc 0 (v / 16)) (hρ : |ρ - v * τ| ≤ 4 * s) :
    0 ≤ Real.sqrt (v + s) ^ 3 / ρ ∧ Real.sqrt (v + s) ^ 3 / ρ ≤ 32 := by
  have hr := (perturbation_denominator_bounds v s τ ρ hv.1 hτ hs.2 hρ).1
  have hr0 : 0 < ρ := by linarith [hv.1]
  have hvs : 0 ≤ v + s := by linarith [hv.1, hs.1]
  have hvss : v + s ≤ 2 := by linarith [hv.2, hs.2]
  have hroot : Real.sqrt (v + s) ≤ 2 := by nlinarith [Real.sq_sqrt hvs, Real.sqrt_nonneg (v + s)]
  have hcube : Real.sqrt (v + s) ^ 3 ≤ 4 * v := by
    have h := mul_le_mul_of_nonneg_left hroot hvs
    rw [pow_succ, Real.sq_sqrt hvs]
    nlinarith [hs.2]
  constructor
  · positivity
  · apply (div_le_iff₀ hr0).2
    nlinarith

theorem prefactor_perturbation_bound (v s τ ρ : ℝ) (hv : v ∈ Ioc 0 1)
    (hτ : τ ∈ Icc (1 / 2) 1) (hs : s ∈ Icc 0 (v / 16)) (hρ : |ρ - v * τ| ≤ 4 * s) :
    |Real.sqrt (v + s) ^ 3 / ρ - Real.sqrt v ^ 3 / (v * τ)| ≤ 56 * s / Real.sqrt v := by
  have hv0 := hv.1
  have hs0 := hs.1
  have hτ0 : 0 < τ := by linarith [hτ.1]
  have hr := perturbation_denominator_bounds v s τ ρ hv.1 hτ hs.2 hρ
  have hr0 : 0 < ρ := by linarith [hv.1]
  have hr00 : 0 < v * τ := by linarith [hv.1]
  have hroot := Real.sqrt_pos.2 hv.1
  have hrootsq := Real.sq_sqrt hv.1.le
  have hτv : v * τ ≤ v := by nlinarith [mul_le_mul_of_nonneg_left hτ.2 hv.1.le]
  have hcube := sqrt_cube_increment_bound v s hv.1 hs.1 (by linarith [hs.2, hv.1])
  have hN : |Real.sqrt (v + s) ^ 3 * (v * τ) - Real.sqrt v ^ 3 * ρ| ≤ 7 * Real.sqrt v * v * s := by
    have he : Real.sqrt (v + s) ^ 3 * (v * τ) - Real.sqrt v ^ 3 * ρ =
        (v * τ) * (Real.sqrt (v + s) ^ 3 - Real.sqrt v ^ 3) + Real.sqrt v ^ 3 * (v * τ - ρ) := by ring
    rw [he]
    have h := abs_add_le ((v * τ) * (Real.sqrt (v + s) ^ 3 - Real.sqrt v ^ 3))
      (Real.sqrt v ^ 3 * (v * τ - ρ))
    rw [abs_mul (v * τ) _, abs_mul (Real.sqrt v ^ 3) _, abs_of_pos hr00, abs_of_nonneg (pow_nonneg hroot.le 3), abs_sub_comm (v * τ) ρ] at h
    have h1 := mul_le_mul_of_nonneg_left hcube hr00.le
    have h2 := mul_le_mul_of_nonneg_left hρ (pow_nonneg hroot.le 3)
    have h3 := mul_le_mul_of_nonneg_right hτv (by positivity : 0 ≤ 3 * Real.sqrt v * s)
    have he3 : Real.sqrt v ^ 3 = v * Real.sqrt v := by rw [pow_succ, hrootsq]
    rw [he3] at h1 h2
    conv at h => rhs; rw [he3]
    nlinarith only [h, h1, h2, h3]
  have hD : v ^ 2 / 8 ≤ ρ * (v * τ) := by
    have h := mul_le_mul hr.1 hr.2 (by linarith : 0 ≤ v / 2) hr0.le
    nlinarith only [h]
  have he : Real.sqrt (v + s) ^ 3 / ρ - Real.sqrt v ^ 3 / (v * τ) =
      (Real.sqrt (v + s) ^ 3 * (v * τ) - Real.sqrt v ^ 3 * ρ) / (ρ * (v * τ)) := by
    field_simp [hr0.ne', hv.1.ne', hτ0.ne']
    <;> ring
  rw [he, abs_div, abs_of_pos (mul_pos hr0 hr00)]
  have h := div_le_div₀ (by positivity : 0 ≤ 7 * Real.sqrt v * v * s) hN
    (by positivity : 0 < v ^ 2 / 8) hD
  apply h.trans_eq
  field_simp [hv.1.ne', hroot.ne']
  rw [hrootsq]
  ring

theorem normalized_branch_difference_bound (v s τ ρ : ℝ) (hv : v ∈ Ioc 0 1)
    (hτ : τ ∈ Icc (1 / 2) 1) (hs : s ∈ Icc 0 (v / 16)) (hρ : |ρ - v * τ| ≤ 4 * s)
    (n : ℕ) (hn : 1 ≤ n) (y F : ℝ)
    (hBE : |F - normalCDF (y / Real.sqrt v)| ≤ cE * τ / Real.sqrt ((n : ℝ) * v)) :
    |Real.sqrt (n : ℝ) * (Real.sqrt (v + s) ^ 3 / ρ) * (F - normalCDF (y / Real.sqrt (v + s))) -
      Real.sqrt (n : ℝ) * (Real.sqrt v ^ 3 / (v * τ)) * (F - normalCDF (y / Real.sqrt v))| ≤
      (56 * cE + 48 * phi0) / v * Real.sqrt (n : ℝ) * s := by
  have hv0 := hv.1
  have hs0 := hs.1
  have hτ0 : 0 < τ := by linarith [hτ.1]
  have hc := cE_pos
  have hphi := phi0_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (n : ℝ)]
  have hsv := Real.sqrt_pos.2 hv0
  have hA := perturbed_prefactor_bound v s τ ρ hv hτ hs hρ
  have hAp := prefactor_perturbation_bound v s τ ρ hv hτ hs hρ
  have hG := gaussian_variance_perturbation_bound y v s hv0 hs0
  have he : Real.sqrt (n : ℝ) * (Real.sqrt (v + s) ^ 3 / ρ) * (F - normalCDF (y / Real.sqrt (v + s))) -
      Real.sqrt (n : ℝ) * (Real.sqrt v ^ 3 / (v * τ)) * (F - normalCDF (y / Real.sqrt v)) =
      Real.sqrt (n : ℝ) * (Real.sqrt (v + s) ^ 3 / ρ - Real.sqrt v ^ 3 / (v * τ)) * (F - normalCDF (y / Real.sqrt v)) +
      Real.sqrt (n : ℝ) * (Real.sqrt (v + s) ^ 3 / ρ) * (normalCDF (y / Real.sqrt v) - normalCDF (y / Real.sqrt (v + s))) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hfirst : |Real.sqrt (n : ℝ) * (Real.sqrt (v + s) ^ 3 / ρ - Real.sqrt v ^ 3 / (v * τ)) * (F - normalCDF (y / Real.sqrt v))| ≤
      56 * cE * s / v := by
    simp only [abs_mul, abs_of_pos hsn]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hAp hsn.le) hBE (abs_nonneg _) (by positivity)
    have hh : Real.sqrt (n : ℝ) * (56 * s / Real.sqrt v) * (cE * τ / Real.sqrt ((n : ℝ) * v)) =
        56 * cE * s * τ / v := by
      rw [Real.sqrt_mul hn0.le]
      field_simp [hsn.ne', hsv.ne', hv0.ne']
      rw [Real.sq_sqrt hv0.le]
    apply h.trans
    rw [hh]
    apply div_le_div_of_nonneg_right _ hv0.le
    nlinarith [mul_le_mul_of_nonneg_left hτ.2 (by positivity : 0 ≤ 56 * cE * s)]
  have hsecond : |Real.sqrt (n : ℝ) * (Real.sqrt (v + s) ^ 3 / ρ) * (normalCDF (y / Real.sqrt v) - normalCDF (y / Real.sqrt (v + s)))| ≤
      48 * phi0 / v * Real.sqrt (n : ℝ) * s := by
    rw [abs_mul, abs_mul, abs_of_pos hsn, abs_of_nonneg hA.1, abs_sub_comm]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hA.2 hsn.le) hG (abs_nonneg _) (by positivity)
    convert h using 1 <;> ring
  have hfirst' : 56 * cE * s / v ≤ 56 * cE / v * Real.sqrt (n : ℝ) * s := by
    have h := mul_le_mul_of_nonneg_left hsn1 (by positivity : 0 ≤ 56 * cE * s / v)
    convert h using 1 <;> ring
  have h := add_le_add (hfirst.trans hfirst') hsecond
  convert h using 1 <;> ring

end BerryEsseen
