import BerryEsseen.GaussianOddIntegrals
import BerryEsseen.EffectiveLowFrequency

/-! Complete effective low-frequency smoothing integral, with constant 6/n. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def effectiveLowFrequencyMajorant (t : ℝ) : ℝ :=
  (0.61 : ℝ) * |t| ^ 3 * Real.exp (-(0.35 : ℝ) * t ^ 2) +
    (0.048 : ℝ) * |t| ^ 5 * Real.exp (-t ^ 2 / 2)

theorem effectiveLowFrequencyMajorant_nonneg (t : ℝ) : 0 ≤ effectiveLowFrequencyMajorant t := by
  unfold effectiveLowFrequencyMajorant
  positivity

theorem effectiveLowFrequencyMajorant_integrable : Integrable effectiveLowFrequencyMajorant := by
  have h3 := (gaussian_abs_pow_integrable 3 (0.35 : ℝ) (by norm_num)).const_mul (0.61 : ℝ)
  have h5 := (gaussian_abs_pow_integrable 5 (1 / 2) (by norm_num)).const_mul (0.048 : ℝ)
  convert h3.add h5 using 1
  funext t
  dsimp [effectiveLowFrequencyMajorant]
  rw [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
  ring

theorem effectiveLowFrequencyMajorant_integral : (∫ t, effectiveLowFrequencyMajorant t) < 6 := by
  have he : effectiveLowFrequencyMajorant = fun t : ℝ =>
      (0.61 : ℝ) * (|t| ^ 3 * Real.exp (-(0.35 : ℝ) * t ^ 2)) +
      (0.048 : ℝ) * (|t| ^ 5 * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
    funext t
    dsimp [effectiveLowFrequencyMajorant]
    rw [show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
    ring
  rw [he, integral_add ((gaussian_abs_pow_integrable 3 (0.35 : ℝ) (by norm_num)).const_mul _)
    ((gaussian_abs_pow_integrable 5 (1 / 2) (by norm_num)).const_mul _),
    integral_const_mul, integral_const_mul,
    gaussian_abs_cubic_integral (0.35 : ℝ) (by norm_num), gaussian_abs_quintic_integral (1 / 2) (by norm_num)]
  norm_num

def effectiveLowFrequencyRange (n : ℕ) : Set ℝ :=
  Icc (-(Real.sqrt (n : ℝ) / 2)) (Real.sqrt (n : ℝ) / 2)

theorem effective_fourierEdgeworthError_low_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : t ∈ effectiveLowFrequencyRange n) :
    fourierEdgeworthError P n t ≤ effectiveLowFrequencyMajorant t / (n : ℝ) := by
  by_cases hzero : t = 0
  · simp [hzero, fourierEdgeworthError, effectiveLowFrequencyMajorant]
  have h := effective_charFun_edgeworth_low_frequency P hβ hb n hn t (abs_le.2 ht)
  have hh := div_le_div_of_nonneg_right h (abs_nonneg t)
  change fourierEdgeworthError P n t ≤ _ at hh
  convert hh using 1
  unfold effectiveLowFrequencyMajorant
  field_simp [abs_ne_zero.mpr hzero]

theorem effectiveLowFrequencyIntegral_integrable (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) : IntegrableOn (fourierEdgeworthError P n) (effectiveLowFrequencyRange n) := by
  apply (effectiveLowFrequencyMajorant_integrable.div_const (n : ℝ)).integrableOn.mono'
    (fourierEdgeworthError_measurable P n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (show MeasurableSet (effectiveLowFrequencyRange n) from measurableSet_Icc)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (fourierEdgeworthError_nonneg P n t)]
  exact effective_fourierEdgeworthError_low_bound P hβ hb n hn t ht

theorem effectiveLowFrequencyIntegral_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) :
    (∫ t in effectiveLowFrequencyRange n, fourierEdgeworthError P n t) ≤ 6 / (n : ℝ) := by
  calc
    _ ≤ ∫ t in effectiveLowFrequencyRange n, effectiveLowFrequencyMajorant t / (n : ℝ) := by
      apply integral_mono_ae (effectiveLowFrequencyIntegral_integrable P hβ hb n hn)
        (effectiveLowFrequencyMajorant_integrable.div_const (n : ℝ)).integrableOn
      filter_upwards [ae_restrict_mem (show MeasurableSet (effectiveLowFrequencyRange n) from measurableSet_Icc)] with t ht
      exact effective_fourierEdgeworthError_low_bound P hβ hb n hn t ht
    _ ≤ ∫ t, effectiveLowFrequencyMajorant t / (n : ℝ) := by
      apply setIntegral_le_integral (effectiveLowFrequencyMajorant_integrable.div_const (n : ℝ))
      exact ae_of_all _ (fun t => div_nonneg (effectiveLowFrequencyMajorant_nonneg t) (Nat.cast_nonneg n))
    _ = (∫ t, effectiveLowFrequencyMajorant t) / (n : ℝ) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right effectiveLowFrequencyMajorant_integral.le (Nat.cast_nonneg n)

end BerryEsseen
