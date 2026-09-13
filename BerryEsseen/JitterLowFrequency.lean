import BerryEsseen.LowFrequencyIntegral
import BerryEsseen.JitterCharacteristic

/-! Low-frequency smoothing errors for the actual jittered sum law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def normalizedJitteredSumLaw (P : StandardizedLaw) (n : ℕ) (h : ℝ) : Measure ℝ :=
  (iidSumLaw P.measure n ∗ spanJitter h).map (fun x => x / Real.sqrt (n : ℝ))

theorem normalizedJitteredSumLaw_probability (P : StandardizedLaw) (n : ℕ) (h : ℝ) :
    IsProbabilityMeasure (normalizedJitteredSumLaw P n h) := by
  letI := spanJitter_probability h
  unfold normalizedJitteredSumLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_normalizedJitteredSumLaw (P : StandardizedLaw) (n : ℕ)
    (h : ℝ) (hh : 0 ≤ h) (t : ℝ) :
    charFun (normalizedJitteredSumLaw P n h) t =
      (Real.sinc (h * (t / Real.sqrt (n : ℝ)) / 2) : ℂ) *
        charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n := by
  letI := spanJitter_probability h
  unfold normalizedJitteredSumLaw
  have he : (fun x : ℝ => x / Real.sqrt (n : ℝ)) = (fun x => (Real.sqrt (n : ℝ))⁻¹ * x) := by
    funext x
    ring
  rw [he, charFun_map_mul, charFun_jittered_iid_sum _ _ h hh]
  simp only [div_eq_mul_inv, mul_comm t]

def jitterFourierError (P : StandardizedLaw) (n : ℕ) (h t : ℝ) : ℝ :=
  ‖charFun (normalizedJitteredSumLaw P n h) t - edgeworthChar n (signedThirdMoment P) t‖ / |t|

def jitterLowFrequencyMajorant (h t : ℝ) : ℝ :=
  lowFrequencyMajorant t + h ^ 2 / 24 * |t| * Real.exp (-t ^ 2 / 4)

theorem jitterLowFrequencyMajorant_nonneg (h t : ℝ) : 0 ≤ jitterLowFrequencyMajorant h t := by
  unfold jitterLowFrequencyMajorant
  exact add_nonneg (lowFrequencyMajorant_nonneg t) (by positivity)

theorem jitterLowFrequencyMajorant_integrable (h : ℝ) : Integrable (jitterLowFrequencyMajorant h) := by
  have hi := (gaussian_abs_pow_integrable 1 (1 / 4) (by norm_num)).const_mul (h ^ 2 / 24)
  convert lowFrequencyMajorant_integrable.add hi using 1
  funext t
  dsimp [jitterLowFrequencyMajorant]
  rw [show -(1 / 4 : ℝ) * t ^ 2 = -t ^ 2 / 4 by ring]
  ring

theorem jitterFourierError_low_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h)
    (t : ℝ) (ht : t ∈ lowFrequencyRange n) :
    jitterFourierError P n h t ≤ jitterLowFrequencyMajorant h t / (n : ℝ) := by
  by_cases ht0 : t = 0
  · simp [ht0, jitterFourierError, jitterLowFrequencyMajorant, lowFrequencyMajorant]
  let s := Real.sqrt (n : ℝ)
  let u := t / s
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hu : |u| ≤ 1 / 100 := by
    rw [show |u| = |t| / s by simp [u, abs_div, abs_of_pos hs]]
    apply (div_le_iff₀ hs).2
    have h := abs_le.2 ht
    change |t| ≤ s / 100 at h
    linarith
  have hu2 : (n : ℝ) * u ^ 2 = t ^ 2 :=
    (normalized_cubic_scaling (n : ℝ) s t 0 hs hs2).1
  have hf : ‖charFun P.measure u ^ n‖ ≤ Real.exp (-t ^ 2 / 4) := by
    rw [norm_pow]
    have hpow := pow_le_pow_left₀ (norm_nonneg _) (charFun_low_frequency_decay P hβ hb u hu) n
    rw [← Real.exp_nat_mul] at hpow
    convert hpow using 1
    congr 1
    nlinarith [hu2]
  have hH : |Real.sinc (h * u / 2) - 1| ≤ h ^ 2 * u ^ 2 / 24 := by
    convert sinc_quadratic_error (h * u / 2) using 1
    ring
  have hprod : ‖((Real.sinc (h * u / 2) : ℂ) - 1) * charFun P.measure u ^ n‖ ≤
      h ^ 2 * u ^ 2 / 24 * Real.exp (-t ^ 2 / 4) := by
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
  have he : h ^ 2 * u ^ 2 / 24 * Real.exp (-t ^ 2 / 4) / |t| =
      h ^ 2 / 24 * |t| * Real.exp (-t ^ 2 / 4) / (n : ℝ) := by
    have hue : u ^ 2 = t ^ 2 / (n : ℝ) := (eq_div_iff hn0.ne').2 (by nlinarith [hu2])
    rw [hue, ← sq_abs t]
    field_simp [abs_ne_zero.mpr ht0]
  rw [he] at hdiv
  have hbase := fourierEdgeworthError_low_bound P hβ hb n hn t ht
  change fourierEdgeworthError P n t ≤ _ at hbase
  change jitterFourierError P n h t ≤ _ + fourierEdgeworthError P n t at hdiv
  calc
    _ ≤ h ^ 2 / 24 * |t| * Real.exp (-t ^ 2 / 4) / (n : ℝ) +
        lowFrequencyMajorant t / (n : ℝ) := hdiv.trans (add_le_add le_rfl hbase)
    _ = _ := by unfold jitterLowFrequencyMajorant; ring

def jitterLowFrequencyConstant (h : ℝ) : ℝ := ∫ t, jitterLowFrequencyMajorant h t

def jitterLowFrequencyIntegral (P : StandardizedLaw) (n : ℕ) (h : ℝ) : ℝ :=
  ∫ t in lowFrequencyRange n, jitterFourierError P n h t

theorem jitterFourierError_nonneg (P : StandardizedLaw) (n : ℕ) (h t : ℝ) :
    0 ≤ jitterFourierError P n h t := by unfold jitterFourierError; positivity

theorem jitterFourierError_measurable (P : StandardizedLaw) (n : ℕ) (h : ℝ) :
    Measurable (jitterFourierError P n h) := by
  letI := normalizedJitteredSumLaw_probability P n h
  have hc : Measurable (charFun (normalizedJitteredSumLaw P n h)) := measurable_charFun
  unfold jitterFourierError edgeworthChar
  fun_prop

theorem jitterLowFrequencyIntegral_integrable (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) :
    IntegrableOn (jitterFourierError P n h) (lowFrequencyRange n) := by
  apply ((jitterLowFrequencyMajorant_integrable h).div_const (n : ℝ)).integrableOn.mono'
    (jitterFourierError_measurable P n h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (show MeasurableSet (lowFrequencyRange n) from measurableSet_Icc)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (jitterFourierError_nonneg P n h t)]
  exact jitterFourierError_low_bound P hβ hb n hn h hh t ht

theorem jitterLowFrequencyIntegral_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ jitterLowFrequencyIntegral P n h ∧
      jitterLowFrequencyIntegral P n h ≤ jitterLowFrequencyConstant h / (n : ℝ) := by
  refine ⟨integral_nonneg (jitterFourierError_nonneg P n h), ?_⟩
  calc
    _ ≤ ∫ t in lowFrequencyRange n, jitterLowFrequencyMajorant h t / (n : ℝ) := by
      apply integral_mono_ae (jitterLowFrequencyIntegral_integrable P hβ hb n hn h hh)
        ((jitterLowFrequencyMajorant_integrable h).div_const (n : ℝ)).integrableOn
      filter_upwards [ae_restrict_mem (show MeasurableSet (lowFrequencyRange n) from measurableSet_Icc)] with t ht
      exact jitterFourierError_low_bound P hβ hb n hn h hh t ht
    _ ≤ ∫ t, jitterLowFrequencyMajorant h t / (n : ℝ) := by
      apply setIntegral_le_integral ((jitterLowFrequencyMajorant_integrable h).div_const (n : ℝ))
      exact ae_of_all _ (fun t => div_nonneg (jitterLowFrequencyMajorant_nonneg h t) (Nat.cast_nonneg n))
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const, jitterLowFrequencyConstant]

theorem jitterLowFrequencyIntegral_scaled_tendsto_zero (P : ℕ → StandardizedLaw) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hβ : ∀ j, thirdMoment (P j) ≤ 2)
    (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10) (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * jitterLowFrequencyIntegral (P j) (n j) h)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => jitterLowFrequencyConstant h / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))
  apply squeeze_zero _ _ hlim
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _)
      (jitterLowFrequencyIntegral_bound (P j) (hβ j) (hb j) _ (hn2 j) h hh).1
  · intro j
    have hbound := mul_le_mul_of_nonneg_left
      (jitterLowFrequencyIntegral_bound (P j) (hβ j) (hb j) _ (hn2 j) h hh).2
      (Real.sqrt_nonneg (n j : ℝ))
    convert hbound using 1
    have hn0 : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by have := hn2 j; omega)
    have hs := Real.sq_sqrt hn0.le
    field_simp [(Real.sqrt_pos.2 hn0).ne']
    rw [hs]

end BerryEsseen
