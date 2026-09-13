import BerryEsseen.EffectiveLowFrequencyIntegral
import BerryEsseen.JitterLowFrequency
import BerryEsseen.EffectivePeakIntegral

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def effectiveJitterLowFrequencyMajorant (h t : ℝ) : ℝ :=
  effectiveLowFrequencyMajorant t + h ^ 2 / 24 * |t| * Real.exp (-(0.35 : ℝ) * t ^ 2)

theorem effectiveJitterLowFrequencyMajorant_nonneg (h t : ℝ) : 0 ≤ effectiveJitterLowFrequencyMajorant h t := by
  unfold effectiveJitterLowFrequencyMajorant
  exact add_nonneg (effectiveLowFrequencyMajorant_nonneg t) (by positivity)

theorem effectiveJitterLowFrequencyMajorant_integrable (h : ℝ) : Integrable (effectiveJitterLowFrequencyMajorant h) := by
  have hi := (gaussian_abs_pow_integrable 1 (0.35 : ℝ) (by norm_num)).const_mul (h ^ 2 / 24)
  convert effectiveLowFrequencyMajorant_integrable.add hi using 1
  funext t
  dsimp [effectiveJitterLowFrequencyMajorant]
  ring

theorem effective_jitterFourierError_low_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h)
    (t : ℝ) (ht : t ∈ effectiveLowFrequencyRange n) :
    jitterFourierError P n h t ≤ effectiveJitterLowFrequencyMajorant h t / (n : ℝ) := by
  by_cases ht0 : t = 0
  · simp [ht0, jitterFourierError, effectiveJitterLowFrequencyMajorant, effectiveLowFrequencyMajorant]
  let s := Real.sqrt (n : ℝ)
  let u := t / s
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hu : |u| ≤ 1 / 2 := by
    rw [show |u| = |t| / s by simp [u, abs_div, abs_of_pos hs]]
    apply (div_le_iff₀ hs).2
    have h := abs_le.2 ht
    change |t| ≤ s / 2 at h
    linarith
  have hu2 : (n : ℝ) * u ^ 2 = t ^ 2 :=
    (normalized_cubic_scaling (n : ℝ) s t 0 hs hs2).1
  have hf : ‖charFun P.measure u ^ n‖ ≤ Real.exp (-(0.35 : ℝ) * t ^ 2) := by
    rw [norm_pow]
    have hpow := pow_le_pow_left₀ (norm_nonneg _) (effective_charFun_decay P hβ hb u hu) n
    rw [← Real.exp_nat_mul] at hpow
    convert hpow using 1
    congr 1
    nlinarith [hu2]
  have hH : |Real.sinc (h * u / 2) - 1| ≤ h ^ 2 * u ^ 2 / 24 := by
    convert sinc_quadratic_error (h * u / 2) using 1
    ring
  have hprod : ‖((Real.sinc (h * u / 2) : ℂ) - 1) * charFun P.measure u ^ n‖ ≤
      h ^ 2 * u ^ 2 / 24 * Real.exp (-(0.35 : ℝ) * t ^ 2) := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hH hf (norm_nonneg _) (by positivity)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n)
    (charFun P.measure u ^ n) (edgeworthChar n (signedThirdMoment P) t)
  rw [show (Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n - charFun P.measure u ^ n =
    ((Real.sinc (h * u / 2) : ℂ) - 1) * charFun P.measure u ^ n by ring] at htri
  have hraw := htri.trans (add_le_add hprod le_rfl)
  have hdiv := div_le_div_of_nonneg_right hraw (abs_nonneg t)
  have hJ : jitterFourierError P n h t =
      ‖(Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n -
        edgeworthChar n (signedThirdMoment P) t‖ / |t| := by
    rw [jitterFourierError, charFun_normalizedJitteredSumLaw P n h hh]
  rw [← hJ, add_div] at hdiv
  have he : h ^ 2 * u ^ 2 / 24 * Real.exp (-(0.35 : ℝ) * t ^ 2) / |t| =
      h ^ 2 / 24 * |t| * Real.exp (-(0.35 : ℝ) * t ^ 2) / (n : ℝ) := by
    have hue : u ^ 2 = t ^ 2 / (n : ℝ) := (eq_div_iff hn0.ne').2 (by nlinarith [hu2])
    rw [hue, ← sq_abs t]
    field_simp [abs_ne_zero.mpr ht0]
  rw [he] at hdiv
  have hbase := effective_fourierEdgeworthError_low_bound P hβ hb n hn t ht
  change fourierEdgeworthError P n t ≤ _ at hbase
  change jitterFourierError P n h t ≤ _ + fourierEdgeworthError P n t at hdiv
  calc
    _ ≤ h ^ 2 / 24 * |t| * Real.exp (-(0.35 : ℝ) * t ^ 2) / (n : ℝ) +
        effectiveLowFrequencyMajorant t / (n : ℝ) := hdiv.trans (add_le_add le_rfl hbase)
    _ = _ := by unfold effectiveJitterLowFrequencyMajorant; ring


theorem effectiveJitterLowFrequencyMajorant_integral (h : ℝ) (hh2 : h ^ 2 ≤ 25 / 6) :
    (∫ t, effectiveJitterLowFrequencyMajorant h t) < 7 := by
  have he : effectiveJitterLowFrequencyMajorant h = fun t =>
      effectiveLowFrequencyMajorant t + (h ^ 2 / 24) * (|t| * Real.exp (-(0.35 : ℝ) * t ^ 2)) := by
    funext t
    unfold effectiveJitterLowFrequencyMajorant
    ring
  have hi : Integrable (fun t : ℝ => |t| * Real.exp (-(0.35 : ℝ) * t ^ 2)) := by
    simpa only [pow_one] using gaussian_abs_pow_integrable 1 (0.35 : ℝ) (by norm_num)
  rw [he, integral_add effectiveLowFrequencyMajorant_integrable (hi.const_mul _),
    integral_const_mul, gaussian_abs_linear_integral _ (by norm_num)]
  nlinarith only [effectiveLowFrequencyMajorant_integral, hh2]

theorem effectiveJitterLowFrequencyIntegral_integrable (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) :
    IntegrableOn (jitterFourierError P n h) (effectiveLowFrequencyRange n) := by
  apply ((effectiveJitterLowFrequencyMajorant_integrable h).div_const (n : ℝ)).integrableOn.mono'
    (jitterFourierError_measurable P n h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (show MeasurableSet (effectiveLowFrequencyRange n) from measurableSet_Icc)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (jitterFourierError_nonneg P n h t)]
  exact effective_jitterFourierError_low_bound P hβ hb n hn h hh t ht

theorem effectiveJitterLowFrequencyIntegral_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) (hh2 : h ^ 2 ≤ 25 / 6) :
    (∫ t in effectiveLowFrequencyRange n, jitterFourierError P n h t) ≤ 7 / (n : ℝ) := by
  calc
    _ ≤ ∫ t in effectiveLowFrequencyRange n, effectiveJitterLowFrequencyMajorant h t / (n : ℝ) := by
      apply integral_mono_ae (effectiveJitterLowFrequencyIntegral_integrable P hβ hb n hn h hh)
        ((effectiveJitterLowFrequencyMajorant_integrable h).div_const (n : ℝ)).integrableOn
      filter_upwards [ae_restrict_mem (show MeasurableSet (effectiveLowFrequencyRange n) from measurableSet_Icc)] with t ht
      exact effective_jitterFourierError_low_bound P hβ hb n hn h hh t ht
    _ ≤ ∫ t, effectiveJitterLowFrequencyMajorant h t / (n : ℝ) := by
      apply setIntegral_le_integral ((effectiveJitterLowFrequencyMajorant_integrable h).div_const (n : ℝ))
      exact ae_of_all _ (fun t => div_nonneg (effectiveJitterLowFrequencyMajorant_nonneg h t) (Nat.cast_nonneg n))
    _ = (∫ t, effectiveJitterLowFrequencyMajorant h t) / (n : ℝ) := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right (effectiveJitterLowFrequencyMajorant_integral h hh2).le (Nat.cast_nonneg n)

end BerryEsseen
