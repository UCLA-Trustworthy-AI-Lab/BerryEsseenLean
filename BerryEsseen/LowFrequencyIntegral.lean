import BerryEsseen.NormalizedFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The actual smoothing integral over low frequencies is uniformly O(1/n). -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def lowFrequencyMajorant (t : ℝ) : ℝ :=
  3 * |t| ^ 3 * Real.exp (-t ^ 2 / 8) + |t| ^ 5 / 9 * Real.exp (-t ^ 2 / 2)

theorem lowFrequencyMajorant_nonneg (t : ℝ) : 0 ≤ lowFrequencyMajorant t := by
  unfold lowFrequencyMajorant
  positivity

theorem gaussian_abs_pow_integrable (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ => |t| ^ k * Real.exp (-b * t ^ 2)) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb
    (s := (k : ℝ)) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)).norm
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (Real.exp_pos _)] using h

theorem lowFrequencyMajorant_integrable : Integrable lowFrequencyMajorant := by
  have h3 := (gaussian_abs_pow_integrable 3 (1 / 8) (by norm_num)).const_mul 3
  have h5 := (gaussian_abs_pow_integrable 5 (1 / 2) (by norm_num)).div_const 9
  convert h3.add h5 using 1
  funext t
  dsimp [lowFrequencyMajorant]
  rw [show -(1 / 8 : ℝ) * t ^ 2 = -t ^ 2 / 8 by ring,
    show -(1 / 2 : ℝ) * t ^ 2 = -t ^ 2 / 2 by ring]
  ring

def lowFrequencyConstant : ℝ := ∫ t, lowFrequencyMajorant t

theorem lowFrequencyConstant_nonneg : 0 ≤ lowFrequencyConstant :=
  integral_nonneg lowFrequencyMajorant_nonneg

def fourierEdgeworthError (P : StandardizedLaw) (n : ℕ) (t : ℝ) : ℝ :=
  ‖charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n - edgeworthChar n (signedThirdMoment P) t‖ / |t|

def lowFrequencyRange (n : ℕ) : Set ℝ :=
  Icc (-(Real.sqrt (n : ℝ) / 100)) (Real.sqrt (n : ℝ) / 100)

def lowFrequencyIntegral (P : StandardizedLaw) (n : ℕ) : ℝ :=
  ∫ t in lowFrequencyRange n, fourierEdgeworthError P n t

theorem fourierEdgeworthError_nonneg (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    0 ≤ fourierEdgeworthError P n t := by
  unfold fourierEdgeworthError
  positivity

theorem fourierEdgeworthError_measurable (P : StandardizedLaw) (n : ℕ) :
    Measurable (fourierEdgeworthError P n) := by
  have hc : Measurable (fun t : ℝ => charFun P.measure (t / Real.sqrt (n : ℝ))) :=
    measurable_charFun.comp (measurable_id.div_const _)
  unfold fourierEdgeworthError edgeworthChar
  fun_prop

theorem fourierEdgeworthError_low_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : t ∈ lowFrequencyRange n) :
    fourierEdgeworthError P n t ≤ lowFrequencyMajorant t / (n : ℝ) := by
  by_cases hzero : t = 0
  · simp [hzero, fourierEdgeworthError, lowFrequencyMajorant]
  have h := charFun_edgeworth_low_frequency P hβ hb n hn t (abs_le.2 ht)
  have hh := div_le_div_of_nonneg_right h (abs_nonneg t)
  change fourierEdgeworthError P n t ≤ _ at hh
  convert hh using 1
  unfold lowFrequencyMajorant
  field_simp [abs_ne_zero.mpr hzero]

theorem lowFrequencyIntegral_integrable (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) : IntegrableOn (fourierEdgeworthError P n) (lowFrequencyRange n) := by
  apply (lowFrequencyMajorant_integrable.div_const (n : ℝ)).integrableOn.mono'
    (fourierEdgeworthError_measurable P n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (show MeasurableSet (lowFrequencyRange n) from measurableSet_Icc)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (fourierEdgeworthError_nonneg P n t)]
  exact fourierEdgeworthError_low_bound P hβ hb n hn t ht

theorem lowFrequencyIntegral_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ lowFrequencyIntegral P n ∧ lowFrequencyIntegral P n ≤ lowFrequencyConstant / (n : ℝ) := by
  refine ⟨integral_nonneg (fourierEdgeworthError_nonneg P n), ?_⟩
  calc
    _ ≤ ∫ t in lowFrequencyRange n, lowFrequencyMajorant t / (n : ℝ) := by
      apply integral_mono_ae (lowFrequencyIntegral_integrable P hβ hb n hn)
        (lowFrequencyMajorant_integrable.div_const (n : ℝ)).integrableOn
      filter_upwards [ae_restrict_mem (show MeasurableSet (lowFrequencyRange n) from measurableSet_Icc)] with t ht
      exact fourierEdgeworthError_low_bound P hβ hb n hn t ht
    _ ≤ ∫ t, lowFrequencyMajorant t / (n : ℝ) := by
      apply setIntegral_le_integral (lowFrequencyMajorant_integrable.div_const (n : ℝ))
      exact ae_of_all _ (fun t => div_nonneg (lowFrequencyMajorant_nonneg t) (Nat.cast_nonneg n))
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const, lowFrequencyConstant]

theorem lowFrequencyIntegral_scaled_tendsto_zero (P : ℕ → StandardizedLaw) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hβ : ∀ j, thirdMoment (P j) ≤ 2)
    (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * lowFrequencyIntegral (P j) (n j)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => lowFrequencyConstant / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))
  apply squeeze_zero _ _ hlim
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _) (lowFrequencyIntegral_bound (P j) (hβ j) (hb j) _ (hn2 j)).1
  · intro j
    have h := mul_le_mul_of_nonneg_left
      (lowFrequencyIntegral_bound (P j) (hβ j) (hb j) _ (hn2 j)).2 (Real.sqrt_nonneg (n j : ℝ))
    convert h using 1
    have hn0 : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by have := hn2 j; omega)
    have hs := Real.sq_sqrt hn0.le
    field_simp [(Real.sqrt_pos.2 hn0).ne']
    rw [hs]

end BerryEsseen
