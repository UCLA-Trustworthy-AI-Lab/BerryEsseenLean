import BerryEsseen.LowFrequencyIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Integrable Gaussian envelopes with a moving center. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def peakGaussian (s m u : ℝ) : ℝ := Real.exp (-(s * (u - m)) ^ 2 / 4)
def peakGaussianMass : ℝ := ∫ u : ℝ, Real.exp (-u ^ 2 / 4)
def peakGaussianFirst : ℝ := ∫ u : ℝ, |u| * Real.exp (-u ^ 2 / 4)

theorem peakGaussian_base_integrable : Integrable (fun u : ℝ => Real.exp (-u ^ 2 / 4)) := by
  convert gaussian_abs_pow_integrable 0 (1 / 4) (by norm_num) using 1
  funext u
  rw [pow_zero, one_mul]
  congr 1
  ring

theorem peakGaussian_first_integrable : Integrable (fun u : ℝ => |u| * Real.exp (-u ^ 2 / 4)) := by
  convert gaussian_abs_pow_integrable 1 (1 / 4) (by norm_num) using 1
  funext u
  rw [pow_one]
  congr 2
  ring

theorem peakGaussian_integrable (s m : ℝ) (hs : 0 < s) : Integrable (peakGaussian s m) :=
  (peakGaussian_base_integrable.comp_mul_left' hs.ne').comp_sub_right m

theorem peakGaussian_first_shift_integrable (s m : ℝ) (hs : 0 < s) :
    Integrable (fun u => |u - m| * peakGaussian s m u) := by
  have h := ((peakGaussian_first_integrable.comp_mul_left' hs.ne').comp_sub_right m).div_const s
  convert h using 1
  funext u
  dsimp [peakGaussian]
  rw [abs_mul, abs_of_pos hs]
  field_simp

theorem peakGaussian_integral (s m : ℝ) (hs : 0 < s) :
    (∫ u, peakGaussian s m u) = peakGaussianMass / s := by
  unfold peakGaussian
  rw [integral_sub_right_eq_self (fun u : ℝ => Real.exp (-(s * u) ^ 2 / 4)) m,
    Measure.integral_comp_mul_left (fun u : ℝ => Real.exp (-u ^ 2 / 4)) s,
    abs_of_pos (inv_pos.2 hs), smul_eq_mul]
  unfold peakGaussianMass
  ring

theorem peakGaussian_first_shift_integral (s m : ℝ) (hs : 0 < s) :
    (∫ u, |u - m| * peakGaussian s m u) = peakGaussianFirst / s ^ 2 := by
  have he : (fun u => |u - m| * peakGaussian s m u) =
      (fun u => (|s * (u - m)| * Real.exp (-(s * (u - m)) ^ 2 / 4)) / s) := by
    funext u
    dsimp [peakGaussian]
    rw [abs_mul, abs_of_pos hs]
    field_simp
  rw [he, integral_div,
    integral_sub_right_eq_self (fun u : ℝ => |s * u| * Real.exp (-(s * u) ^ 2 / 4)) m,
    Measure.integral_comp_mul_left (fun u : ℝ => |u| * Real.exp (-u ^ 2 / 4)) s,
    abs_of_pos (inv_pos.2 hs), smul_eq_mul]
  unfold peakGaussianFirst
  ring

theorem peakGaussian_constants_nonneg : 0 ≤ peakGaussianMass ∧ 0 ≤ peakGaussianFirst := by
  constructor <;> apply integral_nonneg <;> intro u <;> positivity

theorem moving_gaussian_envelope_integrable (s m r C : ℝ) (hs : 0 < s) :
    Integrable (fun u => C * (|u - m| + |m - r|) * peakGaussian s m u) := by
  convert ((peakGaussian_first_shift_integrable s m hs).add
    ((peakGaussian_integrable s m hs).const_mul |m - r|)).const_mul C using 1
  funext u
  change C * (|u - m| + |m - r|) * peakGaussian s m u =
    C * (|u - m| * peakGaussian s m u + |m - r| * peakGaussian s m u)
  ring

theorem moving_gaussian_envelope_integral (s m r C : ℝ) (hs : 0 < s) :
    (∫ u, C * (|u - m| + |m - r|) * peakGaussian s m u) =
      C * (peakGaussianFirst / s ^ 2 + |m - r| * peakGaussianMass / s) := by
  have he : (fun u => C * (|u - m| + |m - r|) * peakGaussian s m u) =
      (fun u => C * (|u - m| * peakGaussian s m u + |m - r| * peakGaussian s m u)) := by
    funext u
    ring
  rw [he, integral_const_mul,
    integral_add (peakGaussian_first_shift_integrable s m hs)
      ((peakGaussian_integrable s m hs).const_mul _),
    integral_const_mul, peakGaussian_integral s m hs, peakGaussian_first_shift_integral s m hs]
  ring

end BerryEsseen
