import BerryEsseen.GaussianBounds
import BerryEsseen.LowFrequencyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The Gaussian polynomial density and its actual indefinite integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def gaussianHermiteThree (x : ℝ) : ℝ := (x ^ 3 - 3 * x) * standardNormalDensity x

theorem gaussian_monomial_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * standardNormalDensity x) := by
  have hi := (gaussian_abs_pow_integrable k (1 / 2) (by norm_num)).const_mul phi0
  apply hi.mono' (((continuous_id.pow k).mul standardNormalDensity_continuous).aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    change ‖x ^ k * standardNormalDensity x‖ ≤ phi0 * (|x| ^ k * Real.exp (-(1 / 2) * x ^ 2))
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (standardNormalDensity_pos x), standardNormalDensity_formula]
    change |x| ^ k * (phi0 * Real.exp (-x ^ 2 / 2)) ≤ phi0 * (|x| ^ k * Real.exp (-(1 / 2) * x ^ 2))
    rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
    exact le_of_eq (by ring))

theorem gaussianHermiteThree_integrable : Integrable gaussianHermiteThree := by
  have hi := (gaussian_monomial_integrable 3).sub ((gaussian_monomial_integrable 1).const_mul 3)
  convert hi using 1
  funext x
  change (x ^ 3 - 3 * x) * standardNormalDensity x = x ^ 3 * standardNormalDensity x - 3 * (x ^ 1 * standardNormalDensity x)
  ring

theorem gaussian_second_primitive_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => -(t ^ 2 - 1) * standardNormalDensity t) (gaussianHermiteThree x) x := by
  convert (standardNormalDensity_third_hasDerivAt x).neg using 1
  · funext t
    change -(t ^ 2 - 1) * standardNormalDensity t = -((t ^ 2 - 1) * standardNormalDensity t)
    ring
  · dsimp [gaussianHermiteThree]
    ring

theorem gaussian_second_primitive_tendsto_atBot :
    Tendsto (fun t : ℝ => -(t ^ 2 - 1) * standardNormalDensity t) atBot (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => t ^ 2) atBot atTop := by
    have hh := (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_neg_atBot_atTop
    convert hh using 1
    funext t
    change t ^ 2 = (-t) ^ 2
    ring
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 2) (by norm_num)).comp hs
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)).comp hs
  simp only [Real.rpow_zero, one_mul, Function.comp_apply] at h0
  simp only [Real.rpow_one, Function.comp_apply] at h1
  have hh := (h0.sub h1).const_mul phi0
  simp only [sub_self, mul_zero] at hh
  convert hh using 1
  funext t
  change -(t ^ 2 - 1) * standardNormalDensity t =
    phi0 * (Real.exp (-(1 / 2) * t ^ 2) - t ^ 2 * Real.exp (-(1 / 2) * t ^ 2))
  rw [standardNormalDensity_formula, show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
  ring

theorem gaussianHermiteThree_cumulative (x : ℝ) :
    (∫ t in Iic x, gaussianHermiteThree t) = -(x ^ 2 - 1) * standardNormalDensity x := by
  simpa only [sub_zero] using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun t _ => gaussian_second_primitive_hasDerivAt t) gaussianHermiteThree_integrable.integrableOn
    gaussian_second_primitive_tendsto_atBot

def edgeworthDensity (n : ℕ) (κ x : ℝ) : ℝ :=
  standardNormalDensity x + κ / (6 * Real.sqrt (n : ℝ)) * gaussianHermiteThree x

def edgeworthCDF (n : ℕ) (κ x : ℝ) : ℝ :=
  normalCDF x + κ / (6 * Real.sqrt (n : ℝ)) * (1 - x ^ 2) * standardNormalDensity x

theorem edgeworthDensity_integrable (n : ℕ) (κ : ℝ) : Integrable (edgeworthDensity n κ) :=
  standardNormalDensity_integrable.add (gaussianHermiteThree_integrable.const_mul _)

theorem edgeworthCDF_cumulative (n : ℕ) (κ x : ℝ) :
    edgeworthCDF n κ x = ∫ t in Iic x, edgeworthDensity n κ t := by
  unfold edgeworthDensity
  rw [integral_add standardNormalDensity_integrable.integrableOn
    (gaussianHermiteThree_integrable.const_mul _).integrableOn,
    integral_const_mul, gaussianHermiteThree_cumulative, ← normalCDF_integral]
  unfold edgeworthCDF
  ring

theorem edgeworthDensity_uniform_bound (n : ℕ) (hn : 1 ≤ n) (κ B : ℝ) (hκ : |κ| ≤ B) (x : ℝ) :
    |edgeworthDensity n κ x| ≤ (1 + 3 * B) * phi0 := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnreal
  have hcoef : |κ / (6 * Real.sqrt (n : ℝ))| ≤ B / 6 := by
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
    exact (div_le_div_of_nonneg_right hκ (by positivity)).trans
      (div_le_div_of_nonneg_left ((abs_nonneg κ).trans hκ) (by norm_num) (by linarith))
  have hH : |gaussianHermiteThree x| ≤ 18 * phi0 := by
    have hh := gaussian_third_derivative_bound x
    simpa only [gaussianHermiteThree, show x ^ 3 - 3 * x = -(3 * x - x ^ 3) by ring,
      neg_mul, abs_neg] using hh
  calc
    _ ≤ |standardNormalDensity x| + |κ / (6 * Real.sqrt (n : ℝ))| * |gaussianHermiteThree x| := by
      simpa only [edgeworthDensity, abs_mul] using abs_add_le (standardNormalDensity x) (κ / (6 * Real.sqrt (n : ℝ)) * gaussianHermiteThree x)
    _ ≤ phi0 + (B / 6) * (18 * phi0) := by
      rw [abs_of_pos (standardNormalDensity_pos x)]
      exact add_le_add (standardNormalDensity_le_phi0 x)
        (mul_le_mul hcoef hH (abs_nonneg _) (div_nonneg ((abs_nonneg κ).trans hκ) (by norm_num)))
    _ = _ := by ring

end BerryEsseen
