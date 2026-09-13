import BerryEsseen.GeneralNormalizedFourier
import BerryEsseen.GeneralCharacteristicTaylor
import BerryEsseen.GeneralCharacteristicDecay
import BerryEsseen.RawFourierError

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def generalLowFrequencyRange (B : ℝ) (n : ℕ) : Set ℝ :=
  Icc (-(Real.sqrt (n : ℝ) * (1 / (100 * B))))
    (Real.sqrt (n : ℝ) * (1 / (100 * B)))

theorem generalLowFrequencyBound_nonneg (B h ρ r t : ℝ) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) :
    0 ≤ generalLowFrequencyBound B h ρ r t := by
  unfold generalLowFrequencyBound
  positivity

theorem generalLowFrequencyBound_majorant (B h ρ r t : ℝ)
    (hρ : ρ ≤ B) (hr : 1 ≤ r) :
    generalLowFrequencyBound B h ρ r t ≤ generalLowFrequencyBound B h B 1 t := by
  have h2 := mul_le_mul_of_nonneg_left hρ (pow_nonneg (abs_nonneg t) 2)
  have h3 : |t| ^ 3 / r ≤ |t| ^ 3 := div_le_self (by positivity) hr
  have h5 : B ^ 2 * |t| ^ 5 / (36 * r) ≤ B ^ 2 * |t| ^ 5 / 36 := by
    calc
      _ = (B ^ 2 * |t| ^ 5 / 36) / r := by ring
      _ ≤ _ := div_le_self (by positivity) hr
  have h1 : h ^ 2 * |t| / (24 * r) ≤ h ^ 2 * |t| / 24 := by
    calc
      _ = (h ^ 2 * |t| / 24) / r := by ring
      _ ≤ _ := div_le_self (by positivity) hr
  unfold generalLowFrequencyBound
  norm_num only [div_one, mul_one]
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right (add_le_add h2 h3) (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le))
    (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)

theorem generalLowFrequencyBound_majorant_integrable (B h : ℝ) :
    Integrable (generalLowFrequencyBound B h B 1) := by
  have h2 := (gaussian_abs_pow_integrable 2 (1 / 8) (by norm_num)).const_mul B
  have h3 := gaussian_abs_pow_integrable 3 (1 / 8) (by norm_num)
  have h5 := (gaussian_abs_pow_integrable 5 (1 / 2) (by norm_num)).const_mul (B ^ 2 / 36)
  have h1 := (gaussian_abs_pow_integrable 1 (1 / 4) (by norm_num)).const_mul (h ^ 2 / 24)
  convert ((h2.add h3).add h5).add h1 using 1
  funext t
  dsimp only [generalLowFrequencyBound, Pi.add_apply]
  rw [show -(1 / 8 : ℝ) * t ^ 2 = -t ^ 2 / 8 by ring,
    show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring,
    show -(1 / 4 : ℝ) * t ^ 2 = -t ^ 2 / 4 by ring]
  ring

theorem generalLowFrequencyRange_argument (B : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ) (ht : t ∈ generalLowFrequencyRange B n) :
    |t / Real.sqrt (n : ℝ)| ≤ 1 / (100 * B) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).2
  simpa only [mul_comm] using (abs_le.mpr ht)

theorem general_jitter_low_frequency_scaled_bound (P : StandardizedLaw)
    (B : ℝ) (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h)
    (t : ℝ) (ht : t ∈ generalLowFrequencyRange B n) :
    Real.sqrt (n : ℝ) * jitterFourierError P n h t ≤
      generalLowFrequencyBound B h (characteristicCubicModulus P (t / Real.sqrt (n : ℝ)))
        (Real.sqrt (n : ℝ)) t := by
  have hu := generalLowFrequencyRange_argument B n hn t ht
  have husmall : |t / Real.sqrt (n : ℝ)| ≤ 1 / 2 :=
    (general_low_frequency_parameters B _ hB hu).1.trans (by norm_num)
  have hlog := manuscript_principal_log_remainder P _ husmall
  have hlog' : ‖manuscriptLogRemainder P (t / Real.sqrt (n : ℝ))‖ ≤
      |t / Real.sqrt (n : ℝ)| ^ 3 * characteristicCubicModulus P (t / Real.sqrt (n : ℝ)) +
        |t / Real.sqrt (n : ℝ)| ^ 4 := by
    convert hlog using 1
    unfold manuscriptLogModulus
    ring
  exact general_jitter_fourier_scaled_bound P n hn B h t _ (by linarith) hh
    ((signedThirdMoment_abs_le P).trans hβ) (characteristicCubicModulus_nonneg _ _)
    (manuscript_charFun_ne_zero P _ husmall) hlog'
    (manuscript_principal_log_smallness P B _ hB hβ hu)

theorem general_jitter_low_frequency_integrable (P : StandardizedLaw)
    (B : ℝ) (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) :
    IntegrableOn (jitterFourierError P n h) (generalLowFrequencyRange B n) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.sq_sqrt hn0]
  apply ((generalLowFrequencyBound_majorant_integrable B h).div_const (Real.sqrt (n : ℝ))).integrableOn.mono'
    (jitterFourierError_measurable P n h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (show MeasurableSet (generalLowFrequencyRange B n) from measurableSet_Icc)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (jitterFourierError_nonneg P n h t)]
  apply (le_div_iff₀ hs).2
  have hscale := general_jitter_low_frequency_scaled_bound P B hB hβ n hn h hh t ht
  have hdom := generalLowFrequencyBound_majorant B h
    (characteristicCubicModulus P (t / Real.sqrt (n : ℝ))) (Real.sqrt (n : ℝ)) t
    ((characteristicCubicModulus_le_thirdMoment P (t / Real.sqrt (n : ℝ))).trans hβ) hs1
  nlinarith only [hscale, hdom]

theorem generalLowFrequencyBound_diagonal_tendsto
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (B h t : ℝ) :
    Tendsto (fun j => generalLowFrequencyBound B h
      (characteristicCubicModulus (P j) (t / Real.sqrt (n j : ℝ)))
      (Real.sqrt (n j : ℝ)) t) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => Real.sqrt (n j : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hi : Tendsto (fun j => (Real.sqrt (n j : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hs
  have hu : Tendsto (fun j => t / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hρ := weak_thirdMoment_characteristicCubicModulus_diagonal_tendsto P Q hw hm _ hu
  have hh := (((hρ.const_mul (|t| ^ 2)).add (hi.const_mul (|t| ^ 3))).mul_const
    (Real.exp (-t ^ 2 / 8))).add
    (hi.const_mul (B ^ 2 * |t| ^ 5 / 36 * Real.exp (-t ^ 2 / 2)))
  have hh' := hh.add (hi.const_mul (h ^ 2 * |t| / 24 * Real.exp (-t ^ 2 / 4)))
  convert hh' using 1 <;>
    simp [generalLowFrequencyBound, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_left_comm, mul_comm]

theorem general_jitterLowFrequencyIntegral_scaled_tendsto_zero
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (B : ℝ) (hB : 1 ≤ B) (hβ : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ t in generalLowFrequencyRange B (n j), jitterFourierError (P j) (n j) h t)
      atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℝ := fun j => (generalLowFrequencyRange B (n j)).indicator
    (fun t => Real.sqrt (n j : ℝ) * jitterFourierError (P j) (n j) h t)
  have hF0 (j : ℕ) (t : ℝ) : 0 ≤ F j t :=
    indicator_nonneg (fun t _ => mul_nonneg (Real.sqrt_nonneg _)
      (jitterFourierError_nonneg _ _ _ _)) t
  have hFbound (j : ℕ) (t : ℝ) : F j t ≤ generalLowFrequencyBound B h
      (characteristicCubicModulus (P j) (t / Real.sqrt (n j : ℝ)))
      (Real.sqrt (n j : ℝ)) t := by
    by_cases ht : t ∈ generalLowFrequencyRange B (n j)
    · dsimp only [F]
      rw [indicator_of_mem ht]
      exact general_jitter_low_frequency_scaled_bound (P j) B hB (hβ j) (n j) (hn2 j) h hh t ht
    · dsimp only [F]
      rw [indicator_of_notMem ht]
      exact generalLowFrequencyBound_nonneg _ _ _ _ _ (characteristicCubicModulus_nonneg _ _)
        (Real.sqrt_nonneg _)
  have hDCT := tendsto_integral_of_dominated_convergence
    (generalLowFrequencyBound B h B 1)
    (F := F) (f := fun _ => (0 : ℝ)) (μ := volume)
    (fun j => (((jitterFourierError_measurable (P j) (n j) h).const_mul
      (Real.sqrt (n j : ℝ))).indicator measurableSet_Icc).aestronglyMeasurable)
    (generalLowFrequencyBound_majorant_integrable B h)
    (fun j => by
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 j t)]
      apply (hFbound j t).trans
      apply generalLowFrequencyBound_majorant
      · exact (characteristicCubicModulus_le_thirdMoment _ _).trans (hβ j)
      · have hn0 : 0 ≤ (n j : ℝ) := Nat.cast_nonneg _
        have hn' : (2 : ℝ) ≤ n j := by exact_mod_cast hn2 j
        nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg (n j : ℝ)])
    (by
      filter_upwards [] with t
      exact squeeze_zero (fun j => hF0 j t) (fun j => hFbound j t)
        (generalLowFrequencyBound_diagonal_tendsto P Q hw hm n hn B h t))
  simp only [integral_zero] at hDCT
  convert hDCT using 1
  funext j
  dsimp only [F]
  rw [integral_indicator (show MeasurableSet (generalLowFrequencyRange B (n j)) from measurableSet_Icc),
    integral_const_mul]

theorem general_rawJitterFourierError_low_integrable (P : StandardizedLaw)
    (B : ℝ) (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B)
    (n : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 ≤ h) :
    IntegrableOn (rawJitterFourierError P n h) (Icc (-(1 / (100 * B))) (1 / (100 * B))) := by
  let r := Real.sqrt (n : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hr1 : 1 ≤ r := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [r]
    nlinarith [Real.sq_sqrt hn0, Real.sqrt_nonneg (n : ℝ)]
  apply ((generalLowFrequencyBound_majorant_integrable B h).comp_mul_left' hr.ne').integrableOn.mono'
    (rawJitterFourierError_measurable P n h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierError_nonneg P n h u),
    rawJitterFourierError_scale P n (by omega) h hh]
  have ht : r * u ∈ generalLowFrequencyRange B n := by
    have ha := abs_le.mpr hu
    apply abs_le.mp
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left ha hr.le
  exact (general_jitter_low_frequency_scaled_bound P B hB hβ n hn h hh (r * u) ht).trans
    (generalLowFrequencyBound_majorant B h _ r _
      ((characteristicCubicModulus_le_thirdMoment P _).trans hβ) hr1)

theorem general_rawJitterFourierError_low_scaled_tendsto_zero
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (B : ℝ) (hB : 1 ≤ B) (hβ : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-(1 / (100 * B))) (1 / (100 * B)), rawJitterFourierError (P j) (n j) h u)
      atTop (𝓝 0) := by
  have hB0 : 0 < B := by linarith
  have hδ : 0 < (1 : ℝ) / (100 * B) := by positivity
  have hlim := general_jitterLowFrequencyIntegral_scaled_tendsto_zero P Q hw hm B hB hβ n hn hn2 h hh
  convert hlim using 1
  funext j
  rw [rawJitterFourierError_integral_scale (P j) (n j) (by have := hn2 j; omega)
    h _ _ hh (by linarith), generalLowFrequencyRange]
  simp only [mul_neg]

end BerryEsseen
