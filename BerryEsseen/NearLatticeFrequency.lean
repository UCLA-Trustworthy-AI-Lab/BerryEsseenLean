import BerryEsseen.NormalizedIID
import BerryEsseen.AnnularIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

def effectiveFourierEnvelope (n : ℕ) (κ t : ℝ) : ℝ :=
  effectiveLowFrequencyMajorant t / (n : ℝ) +
    annularInverse (Real.sqrt (n : ℝ) / 2) (1000 * Real.sqrt (n : ℝ)) t / (n : ℝ) +
    ({v : ℝ | Real.sqrt (n : ℝ) / 2 ≤ |v|}).indicator (edgeworthTailIntegrand n κ) t

theorem effectiveFourierEnvelope_nonneg (n : ℕ) (κ t : ℝ) : 0 ≤ effectiveFourierEnvelope n κ t := by
  have h1 := div_nonneg (effectiveLowFrequencyMajorant_nonneg t) (Nat.cast_nonneg (α := ℝ) n)
  have h2 := div_nonneg (annularInverse_nonneg (Real.sqrt (n : ℝ) / 2) (1000 * Real.sqrt (n : ℝ)) t) (Nat.cast_nonneg (α := ℝ) n)
  have h3 : 0 ≤ ({v : ℝ | Real.sqrt (n : ℝ) / 2 ≤ |v|}).indicator (edgeworthTailIntegrand n κ) t := by
    exact indicator_nonneg (fun x _ => edgeworthTailIntegrand_nonneg n κ x) t
  exact add_nonneg (add_nonneg h1 h2) h3

theorem effectiveFourierEnvelope_integrable (n : ℕ) (hn : 1 ≤ n) (κ : ℝ) :
    Integrable (effectiveFourierEnvelope n κ) := by
  have hs : 0 < Real.sqrt (n : ℝ) / 2 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  have h1 := effectiveLowFrequencyMajorant_integrable.div_const (n : ℝ)
  have h2 := (annularInverse_integrable (Real.sqrt (n : ℝ) / 2) (1000 * Real.sqrt (n : ℝ)) hs).div_const (n : ℝ)
  have h3 := (edgeworthTailIntegrand_integrable_tail n κ (Real.sqrt (n : ℝ) / 2) hs).integrable_indicator
    (measurableSet_le measurable_const measurable_abs)
  exact (h1.add h2).add h3

theorem fourier_error_le_envelope_of_gap (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (hgap : ∀ u : ℝ, 1 / 2 ≤ |u| → |u| ≤ 1000 → ‖charFun P.measure u‖ ≤ 1 - Real.log (n : ℝ) / (n : ℝ))
    (t : ℝ) (ht : t ∈ Icc (-(1000 * Real.sqrt (n : ℝ))) (1000 * Real.sqrt (n : ℝ))) :
    fourierEdgeworthError P n t ≤ effectiveFourierEnvelope n (signedThirdMoment P) t := by
  let s := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hlow0 : 0 ≤ effectiveLowFrequencyMajorant t / (n : ℝ) :=
    div_nonneg (effectiveLowFrequencyMajorant_nonneg t) (Nat.cast_nonneg n)
  have hann0 : 0 ≤ annularInverse (s / 2) (1000 * s) t / (n : ℝ) :=
    div_nonneg (annularInverse_nonneg _ _ _) (Nat.cast_nonneg n)
  have htail0 : 0 ≤ ({v : ℝ | s / 2 ≤ |v|}).indicator (edgeworthTailIntegrand n (signedThirdMoment P)) t :=
    indicator_nonneg (fun x _ => edgeworthTailIntegrand_nonneg n _ x) t
  by_cases hlo : |t| ≤ s / 2
  · have h := effective_fourierEdgeworthError_low_bound P hβ hb n hn t (abs_le.mp hlo)
    change fourierEdgeworthError P n t ≤ effectiveLowFrequencyMajorant t / (n : ℝ) +
      annularInverse (s / 2) (1000 * s) t / (n : ℝ) +
      ({v : ℝ | s / 2 ≤ |v|}).indicator (edgeworthTailIntegrand n (signedThirdMoment P)) t
    linarith
  · have habs : s / 2 ≤ |t| := (lt_of_not_ge hlo).le
    have hband : |t| ∈ Icc (s / 2) (1000 * s) := ⟨habs, abs_le.mpr ht⟩
    have hu1 : 1 / 2 ≤ |t / s| := by
      rw [abs_div, abs_of_pos hs]
      apply (le_div_iff₀ hs).mpr
      linarith
    have hu2 : |t / s| ≤ 1000 := by
      rw [abs_div, abs_of_pos hs]
      apply (div_le_iff₀ hs).mpr
      exact hband.2
    have hp := charFun_power_bound_of_log_gap P.measure n (by omega) (t / s) (hgap _ hu1 hu2)
    have hnrm := (norm_sub_le (charFun P.measure (t / s) ^ n) (edgeworthChar n (signedThirdMoment P) t)).trans
      (add_le_add_left hp _)
    have hd := div_le_div_of_nonneg_right hnrm (abs_nonneg t)
    have herror : fourierEdgeworthError P n t ≤ (|t|)⁻¹ / (n : ℝ) + edgeworthTailIntegrand n (signedThirdMoment P) t := by
      convert hd using 1 <;> dsimp only [fourierEdgeworthError, edgeworthTailIntegrand, s] <;> ring
    change fourierEdgeworthError P n t ≤ effectiveLowFrequencyMajorant t / (n : ℝ) +
      annularInverse (s / 2) (1000 * s) t / (n : ℝ) +
      ({v : ℝ | s / 2 ≤ |v|}).indicator (edgeworthTailIntegrand n (signedThirdMoment P)) t
    rw [annularInverse, indicator_of_mem hband, indicator_of_mem (show t ∈ {v : ℝ | s / 2 ≤ |v|} from habs)]
    linarith

theorem log_two_thousand_lt_eight : Real.log (2000 : ℝ) < 8 := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2000) (by norm_num : (2000 : ℝ) ≤ 2 ^ 11)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith [Real.log_two_lt_d9]

theorem effectiveFourierEnvelope_integral (n : ℕ) (hn : 2 ≤ n) (κ : ℝ) (hκ : |κ| ≤ 1.84) :
    (∫ t, effectiveFourierEnvelope n κ t) ≤ 22 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8) := by
  let s := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have ha : 0 < s / 2 := by positivity
  have haL : s / 2 ≤ 1000 * s := by linarith
  have hset : MeasurableSet {v : ℝ | s / 2 ≤ |v|} := measurableSet_le measurable_const measurable_abs
  have h1 := effectiveLowFrequencyMajorant_integrable.div_const (n : ℝ)
  have h2 := (annularInverse_integrable (s / 2) (1000 * s) ha).div_const (n : ℝ)
  have h3 := (edgeworthTailIntegrand_integrable_tail n κ (s / 2) ha).integrable_indicator hset
  have h12 : Integrable (fun t => effectiveLowFrequencyMajorant t / (n : ℝ) + annularInverse (s / 2) (1000 * s) t / (n : ℝ)) := h1.add h2
  have hratio : 1000 * s / (s / 2) = (2000 : ℝ) := by field_simp; norm_num
  change (∫ t, (effectiveLowFrequencyMajorant t / (n : ℝ) + annularInverse (s / 2) (1000 * s) t / (n : ℝ)) +
    ({v : ℝ | s / 2 ≤ |v|}).indicator (edgeworthTailIntegrand n κ) t) ≤ _
  rw [integral_add h12 h3, integral_add h1 h2, integral_div, integral_div,
    integral_indicator hset, annularInverse_integral (s / 2) (1000 * s) ha haL, hratio]
  have hb1 := div_le_div_of_nonneg_right effectiveLowFrequencyMajorant_integral.le (Nat.cast_nonneg (α := ℝ) n)
  have hb2 := div_le_div_of_nonneg_right
    (show 2 * Real.log (2000 : ℝ) ≤ 16 by linarith [log_two_thousand_lt_eight]) (Nat.cast_nonneg (α := ℝ) n)
  have hb3 := effective_edgeworth_gaussian_tail n hn κ hκ
  change (∫ t in {v : ℝ | s / 2 ≤ |v|}, edgeworthTailIntegrand n κ t) ≤ _ at hb3
  calc
    _ ≤ 6 / (n : ℝ) + 16 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8) := add_le_add (add_le_add hb1 hb2) hb3
    _ = _ := by ring

theorem fourier_error_integrable_of_gap (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (hgap : ∀ u : ℝ, 1 / 2 ≤ |u| → |u| ≤ 1000 → ‖charFun P.measure u‖ ≤ 1 - Real.log (n : ℝ) / (n : ℝ)) :
    IntegrableOn (fourierEdgeworthError P n) (Icc (-(1000 * Real.sqrt (n : ℝ))) (1000 * Real.sqrt (n : ℝ))) := by
  apply (effectiveFourierEnvelope_integrable n (by omega) (signedThirdMoment P)).integrableOn.mono'
    (fourierEdgeworthError_measurable P n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (fourierEdgeworthError_nonneg P n t)]
  exact fourier_error_le_envelope_of_gap P n hn hβ hb hgap t ht

theorem fourier_error_integral_of_gap (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (hgap : ∀ u : ℝ, 1 / 2 ≤ |u| → |u| ≤ 1000 → ‖charFun P.measure u‖ ≤ 1 - Real.log (n : ℝ) / (n : ℝ)) :
    (∫ t in Icc (-(1000 * Real.sqrt (n : ℝ))) (1000 * Real.sqrt (n : ℝ)), fourierEdgeworthError P n t) ≤
      22 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8) := by
  have hi := effectiveFourierEnvelope_integrable n (by omega) (signedThirdMoment P)
  calc
    _ ≤ ∫ t in Icc (-(1000 * Real.sqrt (n : ℝ))) (1000 * Real.sqrt (n : ℝ)),
        effectiveFourierEnvelope n (signedThirdMoment P) t := by
      apply integral_mono_ae (fourier_error_integrable_of_gap P n hn hβ hb hgap) hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact fourier_error_le_envelope_of_gap P n hn hβ hb hgap t ht
    _ ≤ ∫ t, effectiveFourierEnvelope n (signedThirdMoment P) t :=
      setIntegral_le_integral hi (ae_of_all _ (effectiveFourierEnvelope_nonneg n (signedThirdMoment P)))
    _ ≤ _ := effectiveFourierEnvelope_integral n hn (signedThirdMoment P) ((signedThirdMoment_abs_le P).trans hβ)

theorem edgeworthCDF_correction_bound (n : ℕ) (hn : 1 ≤ n) (κ x : ℝ) :
    |edgeworthCDF n κ x - normalCDF x| ≤ |κ| * phi0 / (6 * Real.sqrt (n : ℝ)) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hH : |(1 - x ^ 2) * standardNormalDensity x| ≤ phi0 := by
    have h := gaussian_second_derivative_bound x
    simpa only [show x ^ 2 - 1 = -(1 - x ^ 2) by ring, neg_mul, abs_neg] using h
  have he : edgeworthCDF n κ x - normalCDF x =
      (κ / (6 * Real.sqrt (n : ℝ))) * ((1 - x ^ 2) * standardNormalDensity x) := by unfold edgeworthCDF; ring
  rw [he, abs_mul, abs_div, abs_of_pos (by positivity : 0 < 6 * Real.sqrt (n : ℝ))]
  convert mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ |κ| / (6 * Real.sqrt (n : ℝ))) using 1 <;> ring

theorem sqrt_exponential_tail_large (n : ℕ) (hn : 1024 ≤ n) :
    Real.sqrt (n : ℝ) * Real.exp (-(n : ℝ) / 8) ≤ 1 / 256 := by
  let s := Real.sqrt (n : ℝ)
  have hnR : (1024 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs32 : (32 : ℝ) ≤ s := by nlinarith only [hs0, hs2, hnR]
  have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hs32 3) hs0
  have he := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ (n : ℝ) / 8)
  have hn4 : (n : ℝ) ^ 2 = s ^ 4 := by rw [← hs2]; ring
  change s * Real.exp (-(n : ℝ) / 8) ≤ _
  rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith only [he, hpow, hn4, hnR]

theorem effective_gap_numeric_budget (n : ℕ) (hn : 1024 ≤ n) :
    Real.sqrt (n : ℝ) * ((1 / 4 : ℝ) * (22 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8)) +
      24 / (1000 * Real.sqrt (n : ℝ))) + phi0 / 6 < cE := by
  let s := Real.sqrt (n : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < s := Real.sqrt_pos.mpr hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hs32 : (32 : ℝ) ≤ s := by
    have hnR : (1024 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [hs, hs2, hnR]
  have he : (5 / 4 : ℝ) * (s * Real.exp (-(n : ℝ) / 8)) ≤ 1 / s := by
    have hnR : (1024 : ℝ) ≤ n := by exact_mod_cast hn
    have hpoly := mul_nonneg (sub_nonneg.mpr hnR) hn0.le
    have hexp := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ (n : ℝ) / 8)
    have hne : (5 / 4 : ℝ) * (n : ℝ) * Real.exp (-(n : ℝ) / 8) ≤ 1 := by
      rw [show -(n : ℝ) / 8 = -((n : ℝ) / 8) by ring, Real.exp_neg]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith only [hexp, hpoly, hnR]
    apply (le_div_iff₀ hs).mpr
    nth_rw 1 [← hs2] at hne
    nlinarith only [hne]
  have heq : s * ((1 / 4 : ℝ) * (22 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8)) +
      24 / (1000 * s)) + phi0 / 6 =
      11 / (2 * s) + (5 / 4) * (s * Real.exp (-(n : ℝ) / 8)) + 3 / 125 + phi0 / 6 := by
    rw [← hs2]
    field_simp
    <;> ring
  change s * ((1 / 4 : ℝ) * (22 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8)) +
      24 / (1000 * s)) + phi0 / 6 < _
  rw [heq]
  have h13 : 13 / (2 * s) ≤ (13 / 64 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hsum : 11 / (2 * s) + (5 / 4) * (s * Real.exp (-(n : ℝ) / 8)) ≤ 13 / (2 * s) := by
    norm_num [div_eq_mul_inv, mul_inv_rev] at he ⊢
    nlinarith only [he]
  linarith [phi0_lt_two_fifths, cE_numeric_bounds.1]

theorem normalizedDiscrepancy_lt_of_fourier_gap (S : PublishedSignedSmoothing)
    (P : StandardizedLaw) (n : ℕ) (hn : 1024 ≤ n)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (hgap : ∀ u : ℝ, 1 / 2 ≤ |u| → |u| ≤ 1000 → ‖charFun P.measure u‖ ≤ 1 - Real.log (n : ℝ) / (n : ℝ))
    (x : ℝ) : normalizedDiscrepancy P n x < cE := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  let s := Real.sqrt (n : ℝ)
  let B := (1 / 4 : ℝ) * (22 / (n : ℝ) + 5 * Real.exp (-(n : ℝ) / 8)) + 24 / (1000 * s)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hβpos := thirdMoment_pos P
  have hsm := iid_signed_smoothing S P n hn1 hβ (1000 * s) (by positivity)
    (fourier_error_integrable_of_gap P n hn2 hβ hb hgap) x
  have hint := mul_le_mul_of_nonneg_left (fourier_error_integral_of_gap P n hn2 hβ hb hgap)
    (by positivity : (0 : ℝ) ≤ 1 / 4)
  have hsm' : |cdf (normalizedIIDSumLaw P n) x - edgeworthCDF n (signedThirdMoment P) x| ≤ B := by
    dsimp only [B]
    linarith
  have hcorr : |edgeworthCDF n (signedThirdMoment P) x - normalCDF x| ≤ thirdMoment P * phi0 / (6 * s) := by
    exact (edgeworthCDF_correction_bound n hn1 (signedThirdMoment P) x).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (signedThirdMoment_abs_le P) phi0_pos.le) (by positivity))
  have htri := (abs_sub_le (cdf (normalizedIIDSumLaw P n) x) (edgeworthCDF n (signedThirdMoment P) x) (normalCDF x)).trans
    (add_le_add hsm' hcorr)
  have hnorm : normalizedDiscrepancy P n x ≤ s * B + phi0 / 6 := by
    rw [normalizedDiscrepancy_eq_iid_error P n hn1 x]
    calc
      _ ≤ (s / thirdMoment P) * (B + thirdMoment P * phi0 / (6 * s)) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
      _ = s * B / thirdMoment P + phi0 / 6 := by field_simp [(thirdMoment_pos P).ne']
      _ ≤ _ := add_le_add_left (div_le_self (mul_nonneg hs.le hB) (thirdMoment_ge_one P)) _
  exact hnorm.trans_lt (effective_gap_numeric_budget n hn)

theorem exists_large_characteristic_of_violation (S : PublishedSignedSmoothing)
    (P : StandardizedLaw) (n : ℕ) (hn : 1024 ≤ n)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (x : ℝ) (hviol : cE < normalizedDiscrepancy P n x) :
    ∃ u : ℝ, 1 / 2 ≤ u ∧ u ≤ 1000 ∧ 1 - Real.log (n : ℝ) / (n : ℝ) < ‖charFun P.measure u‖ := by
  have hex : ∃ u : ℝ, 1 / 2 ≤ |u| ∧ |u| ≤ 1000 ∧ 1 - Real.log (n : ℝ) / (n : ℝ) < ‖charFun P.measure u‖ := by
    by_contra h
    push_neg at h
    have hlt := normalizedDiscrepancy_lt_of_fourier_gap S P n hn hβ hb h x
    exact lt_asymm hviol hlt
  obtain ⟨u, hu1, hu2, hu3⟩ := hex
  refine ⟨|u|, hu1, hu2, ?_⟩
  by_cases hu : 0 ≤ u
  · rwa [abs_of_nonneg hu]
  · rw [abs_of_neg (lt_of_not_ge hu), charFun_neg, Complex.norm_conj]
    exact hu3

end BerryEsseen
