import BerryEsseen.EdgeworthTails

/-! Connecting normalized Fourier errors to the raw frequency estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def rawJitterFourierError (P : StandardizedLaw) (n : ℕ) (h u : ℝ) : ℝ :=
  ‖(Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n -
    edgeworthChar n (signedThirdMoment P) (Real.sqrt (n : ℝ) * u)‖ / |u|

theorem rawJitterFourierError_nonneg (P : StandardizedLaw) (n : ℕ) (h u : ℝ) :
    0 ≤ rawJitterFourierError P n h u := by unfold rawJitterFourierError; positivity

theorem rawJitterFourierError_measurable (P : StandardizedLaw) (n : ℕ) (h : ℝ) :
    Measurable (rawJitterFourierError P n h) := by
  unfold rawJitterFourierError edgeworthChar
  fun_prop

theorem rawJitterFourierError_le_sum (P : StandardizedLaw) (n : ℕ) (h u : ℝ) :
    rawJitterFourierError P n h u ≤ rawJitterFourierIntegrand P n h u +
      rawEdgeworthIntegrand n (signedThirdMoment P) u := by
  have hh := norm_sub_le ((Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n)
    (edgeworthChar n (signedThirdMoment P) (Real.sqrt (n : ℝ) * u))
  have hd := div_le_div_of_nonneg_right hh (abs_nonneg u)
  simpa only [rawJitterFourierError, rawJitterFourierIntegrand, rawEdgeworthIntegrand,
    add_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using hd

theorem rawJitterFourierError_scale (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : 0 ≤ h) (u : ℝ) :
    rawJitterFourierError P n h u = Real.sqrt (n : ℝ) *
      jitterFourierError P n h (Real.sqrt (n : ℝ) * u) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  rw [jitterFourierError, charFun_normalizedJitteredSumLaw P n h hh,
    mul_div_cancel_left₀ u hs.ne', abs_mul, abs_of_pos hs]
  unfold rawJitterFourierError
  field_simp [hs.ne']

theorem integral_Icc_scale (f : ℝ → ℝ) (a b s : ℝ) (hab : a ≤ b) (hs : 0 < s) :
    s * (∫ u in Icc a b, f (s * u)) = ∫ t in Icc (s * a) (s * b), f t := by
  simp only [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hs.le)]
  exact intervalIntegral.smul_integral_comp_mul_left f s

theorem rawJitterFourierError_integral_scale (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h a b : ℝ) (hh : 0 ≤ h) (hab : a ≤ b) :
    (∫ u in Icc a b, rawJitterFourierError P n h u) =
      ∫ t in Icc (Real.sqrt (n : ℝ) * a) (Real.sqrt (n : ℝ) * b), jitterFourierError P n h t := by
  simp_rw [rawJitterFourierError_scale P n hn h hh]
  rw [integral_const_mul]
  exact integral_Icc_scale _ a b _ hab (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega)))

theorem rawJitterFourierError_low_integral_eq (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ) (hh : 0 ≤ h) :
    (∫ u in Icc (-(1 / 100 : ℝ)) (1 / 100), rawJitterFourierError P n h u) =
      jitterLowFrequencyIntegral P n h := by
  rw [rawJitterFourierError_integral_scale P n hn h _ _ hh (by norm_num)]
  unfold jitterLowFrequencyIntegral lowFrequencyRange
  congr 2 <;> ring

theorem rawJitterFourierError_low_integrable (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10) (h : ℝ) (hh : 0 ≤ h) :
    IntegrableOn (rawJitterFourierError P n h) (Icc (-(1 / 100 : ℝ)) (1 / 100)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hi := (((jitterLowFrequencyMajorant_integrable h).comp_mul_left' hs.ne').div_const (n : ℝ)).const_mul (Real.sqrt (n : ℝ))
  apply hi.integrableOn.mono' (rawJitterFourierError_measurable P n h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierError_nonneg P n h u),
    rawJitterFourierError_scale P n (by omega) h hh]
  apply mul_le_mul_of_nonneg_left _ hs.le
  apply jitterFourierError_low_bound P hβ hb n hn h hh
  change -(Real.sqrt (n : ℝ) / 100) ≤ Real.sqrt (n : ℝ) * u ∧
    Real.sqrt (n : ℝ) * u ≤ Real.sqrt (n : ℝ) / 100
  have hlo := mul_le_mul_of_nonneg_left hu.1 hs.le
  have hhi := mul_le_mul_of_nonneg_left hu.2 hs.le
  constructor <;> linarith

theorem rawJitterFourierError_away_integrable (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h B a T : ℝ) (hβ : thirdMoment P ≤ B) (ha : 0 < a) (K : Set ℝ) (hK : IsCompact K)
    (hl : ∀ u ∈ K, a ≤ |u|) (hu : ∀ u ∈ K, |u| ≤ T) :
    IntegrableOn (rawJitterFourierError P n h) K := by
  have hi1 := rawJitterFourier_integrableOn P n h a K hK ha hl
  have hi2 := rawEdgeworth_integrableOn n hn (signedThirdMoment P) B a T
    ((signedThirdMoment_abs_le P).trans hβ) ha K hK hl hu
  apply (hi1.add hi2).mono' (rawJitterFourierError_measurable P n h).aestronglyMeasurable
  exact ae_of_all _ (fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierError_nonneg P n h u)]
    exact rawJitterFourierError_le_sum P n h u)

theorem compact_rawJitterFourierError_away_tendsto_zero (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (K : Set ℝ) (hK : IsCompact K) (a T : ℝ) (ha : 0 < a)
    (hl : ∀ u ∈ K, a ≤ |u|) (hu : ∀ u ∈ K, |u| ≤ T) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * ∫ u in K, rawJitterFourierError (P j) (n j) h u)
      atTop (𝓝 0) := by
  have h1 := compact_rawFourier_integral_tendsto_zero P Q hw hW3 B hB n hn h hh hzero K hK a ha hl
  have h2 := compact_rawEdgeworth_integral_tendsto_zero n hn (fun j => signedThirdMoment (P j)) B a T
    (fun j => (signedThirdMoment_abs_le (P j)).trans (hB j)) ha K hK hl hu
  have hsum := h1.add h2
  simp only [add_zero] at hsum
  apply squeeze_zero' _ _ hsum
  · exact Eventually.of_forall (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg (rawJitterFourierError_nonneg (P j) (n j) h)))
  · filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hnj
    have hi1 := rawJitterFourier_integrableOn (P j) (n j) h a K hK ha hl
    have hi2 := rawEdgeworth_integrableOn (n j) hnj (signedThirdMoment (P j)) B a T
      ((signedThirdMoment_abs_le (P j)).trans (hB j)) ha K hK hl hu
    have hb := integral_mono
      (rawJitterFourierError_away_integrable (P j) (n j) hnj h B a T (hB j) ha K hK hl hu)
      (hi1.add hi2) (rawJitterFourierError_le_sum (P j) (n j) h)
    change (∫ u in K, rawJitterFourierError (P j) (n j) h u) ≤
      ∫ u in K, rawJitterFourierIntegrand (P j) (n j) h u +
        rawEdgeworthIntegrand (n j) (signedThirdMoment (P j)) u at hb
    rw [integral_add hi1 hi2] at hb
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (n j : ℝ))

theorem manuscript_nonresonant_rawJitterFourierError_away_tendsto_zero (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (K : Set ℝ) (hK : IsCompact K) (a T : ℝ) (ha : 0 < a)
    (hl : ∀ u ∈ K, a ≤ |u|) (hu : ∀ u ∈ K, |u| ≤ T)
    (hT : T ∉ resonanceSubgroup Q.measure) (hnegT : -T ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * ∫ u in K, rawJitterFourierError (P j) (n j) h u)
      atTop (𝓝 0) := by
  have h1 := manuscript_partition_rawFourier_integral_tendsto_zero P Q hw hW3 B hB n hn h hh hzero
    K hK a T ha hl hu hT hnegT
  have h2 := compact_rawEdgeworth_integral_tendsto_zero n hn (fun j => signedThirdMoment (P j)) B a T
    (fun j => (signedThirdMoment_abs_le (P j)).trans (hB j)) ha K hK hl hu
  have hsum := h1.add h2
  simp only [add_zero] at hsum
  apply squeeze_zero' _ _ hsum
  · exact Eventually.of_forall (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg (rawJitterFourierError_nonneg (P j) (n j) h)))
  · filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hnj
    have hi1 := rawJitterFourier_integrableOn (P j) (n j) h a K hK ha hl
    have hi2 := rawEdgeworth_integrableOn (n j) hnj (signedThirdMoment (P j)) B a T
      ((signedThirdMoment_abs_le (P j)).trans (hB j)) ha K hK hl hu
    have hb := integral_mono
      (rawJitterFourierError_away_integrable (P j) (n j) hnj h B a T (hB j) ha K hK hl hu)
      (hi1.add hi2) (rawJitterFourierError_le_sum (P j) (n j) h)
    change (∫ u in K, rawJitterFourierError (P j) (n j) h u) ≤
      ∫ u in K, rawJitterFourierIntegrand (P j) (n j) h u +
        rawEdgeworthIntegrand (n j) (signedThirdMoment (P j)) u at hb
    rw [integral_add hi1 hi2] at hb
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (n j : ℝ))

theorem manuscript_separated_rawJitterFourierError_away_tendsto_zero (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (a T : ℝ) (ha : 0 < a)
    (hisolated : ∀ u, |u| ≤ 2 * a → u ∈ resonanceSubgroup Q.measure → u = 0)
    (hT : T ∉ resonanceSubgroup Q.measure) (hnegT : -T ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * ∫ u in manuscriptFrequencyAnnulus a T, rawJitterFourierError (P j) (n j) h u)
      atTop (𝓝 0) := by
  let K := manuscriptFrequencyAnnulus a T
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hl : ∀ u ∈ K, a ≤ |u| := fun _ hu => hu.2
  have hu : ∀ u ∈ K, |u| ≤ T := fun _ hu => abs_le.2 hu.1
  have h1 := manuscript_separated_rawFourier_integral_tendsto_zero P Q hw hW3 B hB n hn h hh hzero
    a T ha hisolated hT hnegT
  have h2 := compact_rawEdgeworth_integral_tendsto_zero n hn (fun j => signedThirdMoment (P j)) B a T
    (fun j => (signedThirdMoment_abs_le (P j)).trans (hB j)) ha K hK hl hu
  have hsum := h1.add h2
  simp only [add_zero] at hsum
  apply squeeze_zero' _ _ hsum
  · exact Eventually.of_forall (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg (rawJitterFourierError_nonneg (P j) (n j) h)))
  · filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hnj
    have hi1 := rawJitterFourier_integrableOn (P j) (n j) h a K hK ha hl
    have hi2 := rawEdgeworth_integrableOn (n j) hnj (signedThirdMoment (P j)) B a T
      ((signedThirdMoment_abs_le (P j)).trans (hB j)) ha K hK hl hu
    have hb := integral_mono
      (rawJitterFourierError_away_integrable (P j) (n j) hnj h B a T (hB j) ha K hK hl hu)
      (hi1.add hi2) (rawJitterFourierError_le_sum (P j) (n j) h)
    change (∫ u in K, rawJitterFourierError (P j) (n j) h u) ≤
      ∫ u in K, rawJitterFourierIntegrand (P j) (n j) h u +
        rawEdgeworthIntegrand (n j) (signedThirdMoment (P j)) u at hb
    rw [integral_add hi1 hi2] at hb
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (n j : ℝ))

end BerryEsseen
