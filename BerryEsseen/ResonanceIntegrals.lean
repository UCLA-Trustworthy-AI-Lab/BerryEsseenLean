import BerryEsseen.ResonanceNeighborhoods
import BerryEsseen.GaussianPeakIntegral

/-! The actual Fourier integrals at displaced resonance peaks. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def rawJitterFourierIntegrand (P : StandardizedLaw) (n : ℕ) (h u : ℝ) : ℝ :=
  |Real.sinc (h * u / 2)| * ‖charFun P.measure u‖ ^ n / |u|

theorem rawJitterFourierIntegrand_nonneg (P : StandardizedLaw) (n : ℕ) (h u : ℝ) :
    0 ≤ rawJitterFourierIntegrand P n h u := by unfold rawJitterFourierIntegrand; positivity

theorem rawJitterFourierIntegrand_measurable (P : StandardizedLaw) (n : ℕ) (h : ℝ) :
    Measurable (rawJitterFourierIntegrand P n h) := by
  unfold rawJitterFourierIntegrand
  fun_prop

theorem resonance_interval_away_zero (r d : ℝ) (hdr : d ≤ |r| / 2)
    (u : ℝ) (hu : u ∈ Icc (r - d) (r + d)) : |r| / 2 ≤ |u| := by
  have hdist : |r - u| ≤ d := abs_le.2 ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hh := abs_sub_le r u 0
  simp only [sub_zero] at hh
  linarith

theorem resonance_integrand_bound (P : StandardizedLaw) (n : ℕ) (h r d s m : ℝ)
    (hh : 0 ≤ h) (hr : r ≠ 0) (hdr : d ≤ |r| / 2)
    (hzero : Real.sinc (h * r / 2) = 0)
    (hf : ∀ u ∈ Icc (r - d) (r + d), ‖charFun P.measure u‖ ^ n ≤ peakGaussian s m u)
    (u : ℝ) (hu : u ∈ Icc (r - d) (r + d)) :
    rawJitterFourierIntegrand P n h u ≤
      (h / 4 / (|r| / 2)) * (|u - m| + |m - r|) * peakGaussian s m u := by
  have ha : 0 < |r| / 2 := div_pos (abs_pos.2 hr) (by norm_num)
  have hlu := resonance_interval_away_zero r d hdr u hu
  have hH := spanJitter_multiplier_lipschitz h u r hh
  rw [hzero, sub_zero] at hH
  have htri := abs_sub_le u m r
  have hH' : |Real.sinc (h * u / 2)| ≤ h / 4 * (|u - m| + |m - r|) :=
    hH.trans (mul_le_mul_of_nonneg_left htri (by positivity))
  unfold rawJitterFourierIntegrand
  calc
    _ ≤ (h / 4 * (|u - m| + |m - r|) * peakGaussian s m u) / |u| := by
      apply div_le_div_of_nonneg_right _ (abs_nonneg u)
      exact mul_le_mul hH' (hf u hu) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ ≤ (h / 4 * (|u - m| + |m - r|) * peakGaussian s m u) / (|r| / 2) :=
      div_le_div_of_nonneg_left (by unfold peakGaussian; positivity) ha hlu
    _ = _ := by ring

theorem resonance_integral_bound (P : StandardizedLaw) (n : ℕ) (h r d s m : ℝ)
    (hh : 0 ≤ h) (hr : r ≠ 0) (hdr : d ≤ |r| / 2) (hs : 0 < s)
    (hzero : Real.sinc (h * r / 2) = 0)
    (hf : ∀ u ∈ Icc (r - d) (r + d), ‖charFun P.measure u‖ ^ n ≤ peakGaussian s m u) :
    (∫ u in Icc (r - d) (r + d), rawJitterFourierIntegrand P n h u) ≤
      (h / 4 / (|r| / 2)) * (peakGaussianFirst / s ^ 2 + |m - r| * peakGaussianMass / s) := by
  let C := h / 4 / (|r| / 2)
  let g := fun u => C * (|u - m| + |m - r|) * peakGaussian s m u
  have hg : Integrable g := moving_gaussian_envelope_integrable s m r C hs
  have hgn : ∀ u, 0 ≤ g u := by intro u; dsimp [g, C, peakGaussian]; positivity
  have hle : ∀ᵐ u ∂volume.restrict (Icc (r - d) (r + d)), rawJitterFourierIntegrand P n h u ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact resonance_integrand_bound P n h r d s m hh hr hdr hzero hf u hu
  have hi : IntegrableOn (rawJitterFourierIntegrand P n h) (Icc (r - d) (r + d)) := by
    apply hg.integrableOn.mono' (rawJitterFourierIntegrand_measurable P n h).aestronglyMeasurable
    filter_upwards [hle] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rawJitterFourierIntegrand_nonneg P n h u)] using hu
  calc
    _ ≤ ∫ u in Icc (r - d) (r + d), g u := integral_mono_ae hi hg.integrableOn hle
    _ ≤ ∫ u, g u := setIntegral_le_integral hg (ae_of_all _ hgn)
    _ = _ := moving_gaussian_envelope_integral s m r C hs

theorem actual_resonance_integral_tendsto_zero_on (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h r d : ℝ) (hh : 0 ≤ h) (hr : r ≠ 0) (hd : 0 < d) (hdr : d ≤ |r| / 2)
    (hcurv : ∀ u ∈ Icc (r - d) (r + d), characteristicSquareCurvature Q u ≤ -3 / 2)
    (hstrict : ∀ u ∈ Icc (r - d) (r + d), u ≠ r →
      characteristicSquare Q u < characteristicSquare Q r)
    (hzero : Real.sinc (h * r / 2) = 0) :
      Tendsto (fun j => Real.sqrt (n j : ℝ) *
        ∫ u in Icc (r - d) (r + d), rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
  obtain ⟨m, hm, he⟩ := actual_moving_resonance_envelopes_on P Q hw hW3 B hB r d hd hcurv hstrict
  let C := h / 4 / (|r| / 2)
  have hlim1 : Tendsto (fun j => peakGaussianFirst / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))
  have hlim2 : Tendsto (fun j => |m j - r| * peakGaussianMass) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using (hm.sub_const r).abs.mul_const peakGaussianMass
  have hlim : Tendsto (fun j => C * (peakGaussianFirst / Real.sqrt (n j : ℝ) +
      |m j - r| * peakGaussianMass)) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hlim1.add hlim2).const_mul C
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg (rawJitterFourierIntegrand_nonneg (P j) (n j) h)))
  · filter_upwards [he, hn.eventually (eventually_ge_atTop 1)] with j hj hnj
    have hnpos : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by omega)
    have hs : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.2 hnpos
    have hcf : ∀ u ∈ Icc (r - d) (r + d), ‖charFun (P j).measure u‖ ^ n j ≤
        peakGaussian (Real.sqrt (n j : ℝ)) (m j) u := by
      intro u hu
      simpa only [peakGaussian, mul_pow, Real.sq_sqrt hnpos.le, neg_mul] using hj.2 u hu (n j)
    have hi := resonance_integral_bound (P j) (n j) h r d _ (m j) hh hr hdr hs hzero hcf
    have hb := mul_le_mul_of_nonneg_left hi hs.le
    convert hb using 1
    dsimp [C]
    field_simp [hs.ne']
    <;> ring

theorem actual_resonance_integral_tendsto_zero (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h r : ℝ) (hh : 0 ≤ h) (hr : r ≠ 0) (hres : r ∈ resonanceSubgroup Q.measure)
    (hzero : Real.sinc (h * r / 2) = 0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ |r| / 2 ∧
      Tendsto (fun j => Real.sqrt (n j : ℝ) *
        ∫ u in Icc (r - d) (r + d), rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
  obtain ⟨d, hd, hdr, hcurv, hstrict⟩ := resonance_neighborhood Q r hr hres
  exact ⟨d, hd, hdr, actual_resonance_integral_tendsto_zero_on P Q hw hW3 B hB n hn
    h r d hh hr hd hdr hcurv hstrict hzero⟩

end BerryEsseen
