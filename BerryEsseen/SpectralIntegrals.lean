import BerryEsseen.ResonanceIntegrals
import BerryEsseen.SpectralGap

/-! Actual exponentially small Fourier integrals off the limiting resonances. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem rawJitterFourierIntegrand_le_inv (P : StandardizedLaw) (n : ℕ) (h u : ℝ) :
    rawJitterFourierIntegrand P n h u ≤ 1 / |u| := by
  unfold rawJitterFourierIntegrand
  apply div_le_div_of_nonneg_right _ (abs_nonneg u)
  have hp : ‖charFun P.measure u‖ ^ n ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one (μ := P.measure) u) n
  simpa only [one_mul] using mul_le_mul (Real.abs_sinc_le_one _) hp (pow_nonneg (norm_nonneg _) _) zero_le_one

theorem rawJitterFourier_integrableOn (P : StandardizedLaw) (n : ℕ)
    (h a : ℝ) (K : Set ℝ) (hK : IsCompact K) (ha : 0 < a)
    (hu : ∀ u ∈ K, a ≤ |u|) : IntegrableOn (rawJitterFourierIntegrand P n h) K := by
  have hi : IntegrableOn (fun _ : ℝ => 1 / a) K := integrableOn_const hK.measure_lt_top.ne
  apply hi.mono' (rawJitterFourierIntegrand_measurable P n h).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with u hmem
  rw [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierIntegrand_nonneg P n h u)]
  exact (rawJitterFourierIntegrand_le_inv P n h u).trans
    (div_le_div_of_nonneg_left zero_le_one ha (hu u hmem))

theorem rawJitterFourierIntegrand_bound_away_zero (P : StandardizedLaw) (n : ℕ)
    (h a u E : ℝ) (ha : 0 < a) (hu : a ≤ |u|) (hf : ‖charFun P.measure u‖ ^ n ≤ E) :
    rawJitterFourierIntegrand P n h u ≤ E / a := by
  have hE : 0 ≤ E := (pow_nonneg (norm_nonneg _) _).trans hf
  unfold rawJitterFourierIntegrand
  calc
    _ ≤ E / |u| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg u)
      calc
        _ ≤ 1 * E := mul_le_mul (Real.abs_sinc_le_one _) hf
          (pow_nonneg (norm_nonneg _) _) zero_le_one
        _ = E := one_mul _
    _ ≤ E / a := div_le_div_of_nonneg_left hE ha hu

theorem rawJitterFourierIntegral_bound_away_zero (P : StandardizedLaw) (n : ℕ)
    (h a E : ℝ) (K : Set ℝ) (hK : IsCompact K) (ha : 0 < a)
    (hu : ∀ u ∈ K, a ≤ |u|) (hf : ∀ u ∈ K, ‖charFun P.measure u‖ ^ n ≤ E) :
    (∫ u in K, rawJitterFourierIntegrand P n h u) ≤ (volume K).toReal * (E / a) := by
  have hiC : IntegrableOn (fun _ : ℝ => E / a) K := integrableOn_const hK.measure_lt_top.ne
  have hle : ∀ᵐ u ∂volume.restrict K, rawJitterFourierIntegrand P n h u ≤ E / a := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with u hmem
    exact rawJitterFourierIntegrand_bound_away_zero P n h a u E ha (hu u hmem) (hf u hmem)
  have hi : IntegrableOn (rawJitterFourierIntegrand P n h) K := by
    apply hiC.mono' (rawJitterFourierIntegrand_measurable P n h).aestronglyMeasurable
    filter_upwards [hle] with u hmem
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierIntegrand_nonneg P n h u)] using hmem
  calc
    _ ≤ ∫ u in K, E / a := integral_mono_ae hi hiC hle
    _ = _ := by rw [setIntegral_const]; rfl

theorem actual_spectral_integral_tendsto_zero (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (h a : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (ha : 0 < a) (hu : ∀ u ∈ K, a ≤ |u|)
    (hnr : ∀ u ∈ K, u ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in K, rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, he⟩ := compact_characteristic_spectral_gap P Q hw hW3 K hK hnr
  have hlim : Tendsto (fun j => (volume K).toReal / a *
      (Real.sqrt (n j : ℝ) * Real.exp (-(n j : ℝ) * δ / 2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (sqrt_mul_exp_decay n hn δ hδ).const_mul ((volume K).toReal / a)
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg (rawJitterFourierIntegrand_nonneg (P j) (n j) h)))
  · filter_upwards [he] with j hj
    have hb := rawJitterFourierIntegral_bound_away_zero (P j) (n j) h a
      (Real.exp (-(n j : ℝ) * δ / 2)) K hK ha hu (fun u hu => hj u hu (n j))
    have hbound := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (n j : ℝ))
    convert hbound using 1
    ring

end BerryEsseen
