import BerryEsseen.Statement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The CDF in the target statement has the ordinary Gaussian density as
its derivative. This connects measure-valued definitions to calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace BerryEsseen

def standardNormalDensity : ℝ → ℝ := gaussianPDFReal 0 1

theorem standardNormalDensity_formula (x : ℝ) :
    standardNormalDensity x = phi0 * Real.exp (-x ^ 2 / 2) := by
  simp [standardNormalDensity, gaussianPDFReal, phi0, one_div]

theorem standardNormalDensity_continuous : Continuous standardNormalDensity := by
  unfold standardNormalDensity gaussianPDFReal
  fun_prop

theorem standardNormalDensity_integrable : Integrable standardNormalDensity :=
  integrable_gaussianPDFReal 0 1

theorem normalCDF_integral (x : ℝ) :
    normalCDF x = ∫ t in Iic x, standardNormalDensity t := by
  rw [normalCDF, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun _ => gaussianPDFReal_nonneg _ _ _))

theorem normalCDF_eq_integral_from_zero (x : ℝ) :
    normalCDF x = normalCDF 0 + ∫ t in (0 : ℝ)..x, standardNormalDensity t := by
  rw [normalCDF_integral, normalCDF_integral]
  have h := intervalIntegral.integral_Iic_sub_Iic
    (standardNormalDensity_integrable.integrableOn (s := Iic 0))
    (standardNormalDensity_integrable.integrableOn (s := Iic x))
  linarith

theorem normalCDF_hasDerivAt (x : ℝ) :
    HasDerivAt normalCDF (standardNormalDensity x) x := by
  have he : normalCDF = (fun u => normalCDF 0 + ∫ t in (0 : ℝ)..u, standardNormalDensity t) :=
    funext normalCDF_eq_integral_from_zero
  rw [he]
  have h := intervalIntegral.integral_hasDerivAt_right
    (standardNormalDensity_continuous.intervalIntegrable 0 x)
    standardNormalDensity_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (standardNormalDensity_continuous.continuousAt (x := x))
  exact h.const_add _

theorem standardNormalDensity_hasDerivAt (x : ℝ) :
    HasDerivAt standardNormalDensity (-x * standardNormalDensity x) x := by
  have he : standardNormalDensity = (fun t => phi0 * Real.exp (-t ^ 2 / 2)) :=
    funext standardNormalDensity_formula
  rw [he]
  have h := (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul phi0
  convert h using 1
  dsimp
  ring

theorem standardNormalDensity_second_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => -t * standardNormalDensity t)
      ((x ^ 2 - 1) * standardNormalDensity x) x := by
  convert ((hasDerivAt_id x).neg).mul (standardNormalDensity_hasDerivAt x) using 1
  dsimp
  ring

theorem standardNormalDensity_third_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => (t ^ 2 - 1) * standardNormalDensity t)
      ((3 * x - x ^ 3) * standardNormalDensity x) x := by
  convert (((hasDerivAt_id x).pow 2).sub_const 1).mul
    (standardNormalDensity_hasDerivAt x) using 1
  dsimp
  ring

theorem standardNormalDensity_zero : standardNormalDensity 0 = phi0 := by
  simp [standardNormalDensity_formula]

end BerryEsseen
