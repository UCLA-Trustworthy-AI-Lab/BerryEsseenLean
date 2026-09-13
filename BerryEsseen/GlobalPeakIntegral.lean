import BerryEsseen.EffectiveGlobalPeaks
import BerryEsseen.EffectivePeakIntegral
import BerryEsseen.ResonanceIntegrals

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def globalPeakGaussian (n : ℕ) (m u : ℝ) : ℝ := Real.exp (-(n : ℝ) * (u - m) ^ 2 / 4)

theorem globalPeakGaussian_integrable (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    Integrable (globalPeakGaussian n m) := by
  have h := (integrable_exp_neg_mul_sq (by positivity : 0 < (n : ℝ) / 4)).comp_sub_right m
  convert h using 1
  funext u
  unfold globalPeakGaussian
  congr 1
  ring

theorem globalPeakGaussian_first_integrable (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    Integrable (fun u => |u - m| * globalPeakGaussian n m u) := by
  have h := (gaussian_abs_pow_integrable 1 ((n : ℝ) / 4) (by positivity)).comp_sub_right m
  convert h using 1
  funext u
  simp only [pow_one, globalPeakGaussian]
  congr 2
  ring

theorem globalPeakGaussian_first_integral (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    (∫ u, |u - m| * globalPeakGaussian n m u) = 4 / (n : ℝ) := by
  have he : (fun u => |u - m| * globalPeakGaussian n m u) =
      (fun u => |u - m| * Real.exp (-((n : ℝ) / 4) * (u - m) ^ 2)) := by
    funext u
    unfold globalPeakGaussian
    congr 2
    ring
  rw [he, integral_sub_right_eq_self (fun x : ℝ => |x| * Real.exp (-((n : ℝ) / 4) * x ^ 2)) m, gaussian_abs_linear_integral _ (by positivity)]
  field_simp

theorem globalPeakGaussian_integral_le (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    (∫ u, globalPeakGaussian n m u) ≤ 4 / Real.sqrt (n : ℝ) := by
  have he : globalPeakGaussian n m =
      (fun u => Real.exp (-((n : ℝ) / 4) * (u - m) ^ 2)) := by
    funext u
    unfold globalPeakGaussian
    congr 1
    ring
  rw [he, integral_sub_right_eq_self (fun x : ℝ => Real.exp (-((n : ℝ) / 4) * x ^ 2)) m, integral_gaussian]
  rw [show Real.pi / ((n : ℝ) / 4) = (4 * Real.pi) / n by ring, Real.sqrt_div (by positivity)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith [Real.pi_lt_d2]

theorem global_resonance_frequency_lower (h : ℝ) (hh : h ∈ Ioc 0 5) :
    (6 / 5 : ℝ) ≤ 2 * Real.pi / h := by
  apply (le_div_iff₀ hh.1).mpr
  nlinarith [Real.pi_gt_three, hh.2]

theorem global_resonance_interval_abs_lower (h : ℝ) (hh : h ∈ Ioc 0 5)
    (j : ℤ) (hj : j ≠ 0) (u : ℝ) (hu : u ∈ globalResonanceCell h j) :
    |(j : ℝ)| ≤ |u| := by
  have hh0 := hh.1
  have hdist : |(j : ℝ) * (2 * Real.pi / h) - u| ≤ 1 / 1000 := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have htri := abs_sub_le ((j : ℝ) * (2 * Real.pi / h)) u 0
  simp only [sub_zero, abs_mul, abs_of_pos (show 0 < 2 * Real.pi / h by positivity)] at htri
  have hω := mul_le_mul_of_nonneg_left (global_resonance_frequency_lower h hh) (abs_nonneg (j : ℝ))
  linarith [int_cast_abs_ge_one j hj]

theorem globalJitter_peak_pointwise (P : StandardizedLaw) (h : ℝ) (hh : h ∈ Ioc 0 5)
    (n : ℕ) (j : ℤ) (hj : j ≠ 0) (m d : ℝ) (hd : 0 ≤ d)
    (hshift : |m - (j : ℝ) * (2 * Real.pi / h)| ≤ d)
    (u : ℝ) (hu : u ∈ globalResonanceCell h j)
    (hpeak : ‖charFun P.measure u‖ ^ n ≤ globalPeakGaussian n m u) :
    rawJitterFourierIntegrand P n h u ≤
      (3 / (2 * |(j : ℝ)|)) * (|u - m| + d) * globalPeakGaussian n m u := by
  have hh0 := hh.1
  have hjpos : 0 < |(j : ℝ)| := lt_of_lt_of_le (by norm_num) (int_cast_abs_ge_one j hj)
  have hH := spanJitter_multiplier_lipschitz h u ((j : ℝ) * (2 * Real.pi / h)) hh.1.le
  have hz : Real.sinc (h * ((j : ℝ) * (2 * Real.pi / h)) / 2) = 0 := by
    convert spanJitter_multiplier_resonance_zero h hh.1 j hj using 1 <;> congr 2 <;> ring
  rw [hz, sub_zero] at hH
  have htri := abs_sub_le u m ((j : ℝ) * (2 * Real.pi / h))
  have hmul := mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hshift))
    (show 0 ≤ h / 4 by positivity)
  have hH' : |Real.sinc (h * u / 2)| ≤ (3 / 2) * (|u - m| + d) := by
    have hcoef := mul_le_mul_of_nonneg_right (show h / 4 ≤ (3 / 2 : ℝ) by linarith [hh.2])
      (show 0 ≤ |u - m| + d by positivity)
    exact hH.trans (hmul.trans hcoef)
  have hnum := mul_le_mul hH' hpeak (pow_nonneg (norm_nonneg _) _) (by positivity)
  unfold rawJitterFourierIntegrand
  calc
    _ ≤ ((3 / 2) * (|u - m| + d) * globalPeakGaussian n m u) / |u| :=
      div_le_div_of_nonneg_right hnum (abs_nonneg u)
    _ ≤ ((3 / 2) * (|u - m| + d) * globalPeakGaussian n m u) / |(j : ℝ)| :=
      div_le_div_of_nonneg_left (by unfold globalPeakGaussian; positivity) hjpos
        (global_resonance_interval_abs_lower h hh j hj u hu)
    _ = _ := by ring

theorem globalJitter_peak_integral (P : StandardizedLaw) (h : ℝ) (hh : h ∈ Ioc 0 5)
    (n : ℕ) (hn : 1 ≤ n) (j : ℤ) (hj : j ≠ 0) (m d : ℝ) (hd : 0 ≤ d)
    (hshift : |m - (j : ℝ) * (2 * Real.pi / h)| ≤ d)
    (hpeak : ∀ u ∈ globalResonanceCell h j,
      ‖charFun P.measure u‖ ^ n ≤ globalPeakGaussian n m u) :
    IntegrableOn (rawJitterFourierIntegrand P n h) (globalResonanceCell h j) ∧
      (∫ u in globalResonanceCell h j, rawJitterFourierIntegrand P n h u) ≤
        (6 / |(j : ℝ)|) * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) := by
  let C := 3 / (2 * |(j : ℝ)|)
  let g := fun u => C * (|u - m| + d) * globalPeakGaussian n m u
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : Integrable g := by
    convert ((globalPeakGaussian_first_integrable n hn m).add
      ((globalPeakGaussian_integrable n hn m).const_mul d)).const_mul C using 1
    funext u
    dsimp only [g, Pi.add_apply]
    ring
  have hnonneg (u : ℝ) : 0 ≤ g u := by dsimp [g, globalPeakGaussian]; positivity
  have hle : ∀ᵐ u ∂volume.restrict (globalResonanceCell h j), rawJitterFourierIntegrand P n h u ≤ g u := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (globalResonanceCell h j) from measurableSet_Icc)] with u hu
    exact globalJitter_peak_pointwise P h hh n j hj m d hd hshift u hu (hpeak u hu)
  have hi : IntegrableOn (rawJitterFourierIntegrand P n h) (globalResonanceCell h j) := by
    apply hg.integrableOn.mono' (rawJitterFourierIntegrand_measurable P n h).aestronglyMeasurable
    filter_upwards [hle] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierIntegrand_nonneg P n h u)] using hu
  refine ⟨hi, ?_⟩
  have hfull : (∫ u, g u) = C * (4 / (n : ℝ) + d * (∫ u, globalPeakGaussian n m u)) := by
    have he : g = fun u => C * (|u - m| * globalPeakGaussian n m u + d * globalPeakGaussian n m u) := by
      funext u; dsimp [g]; ring
    rw [he, integral_const_mul, integral_add (globalPeakGaussian_first_integrable n hn m)
      ((globalPeakGaussian_integrable n hn m).const_mul d), integral_const_mul, globalPeakGaussian_first_integral n hn m]
  calc
    _ ≤ ∫ u in globalResonanceCell h j, g u := integral_mono_ae hi hg.integrableOn hle
    _ ≤ ∫ u, g u := setIntegral_le_integral hg (ae_of_all _ hnonneg)
    _ = C * (4 / (n : ℝ) + d * (∫ u, globalPeakGaussian n m u)) := hfull
    _ ≤ C * (4 / (n : ℝ) + d * (4 / Real.sqrt (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (globalPeakGaussian_integral_le n hn m) hd)) hC
    _ = _ := by dsimp [C]; ring

end BerryEsseen
