import BerryEsseen.BoundedJitterExpansion

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem jitterFourierError_low_integrable_of_raw (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hi : IntegrableOn (rawJitterFourierError P n h) (Icc (-δ) δ)) :
    IntegrableOn (jitterFourierError P n h)
      (Icc (-δ * Real.sqrt (n : ℝ)) (δ * Real.sqrt (n : ℝ))) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0 < n by omega))
  have hi0 : IntervalIntegrable (rawJitterFourierError P n h) volume (-δ) δ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hi
  have hi1 := (hi0.comp_mul_left (c := (Real.sqrt (n : ℝ))⁻¹)).div_const (Real.sqrt (n : ℝ))
  have he : (fun t => rawJitterFourierError P n h ((Real.sqrt (n : ℝ))⁻¹ * t) /
      Real.sqrt (n : ℝ)) = jitterFourierError P n h := by
    funext t
    rw [rawJitterFourierError_scale P n hn h hh]
    simp only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_div_cancel_left₀ _ hs.ne']
  rw [he] at hi1
  have hb : -δ * Real.sqrt (n : ℝ) ≤ δ * Real.sqrt (n : ℝ) := by nlinarith [mul_pos hδ hs]
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).1
  simpa only [div_inv_eq_mul] using hi1

theorem jitterFourierError_integrable_of_raw_low (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n)
    (h δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hi : IntegrableOn (rawJitterFourierError P n h) (Icc (-δ) δ)) (L : ℝ) :
    IntegrableOn (jitterFourierError P n h) (Icc (-L) L) := by
  let a := δ * Real.sqrt (n : ℝ)
  let K := Icc (-L) L ∩ {t : ℝ | a ≤ |t|}
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := mul_pos hδ (Real.sqrt_pos.mpr hnpos)
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hcJ := normalizedJittered_charFun_continuous P n h hh
  have hnum : Continuous (fun t => ‖charFun (normalizedJitteredSumLaw P n h) t -
      edgeworthChar n (signedThirdMoment P) t‖) := by
    unfold edgeworthChar
    fun_prop
  have hc : ContinuousOn (jitterFourierError P n h) K :=
    hnum.continuousOn.div continuous_abs.continuousOn (fun t ht => (ha.trans_le ht.2).ne')
  have hiK : IntegrableOn (jitterFourierError P n h) K := hc.integrableOn_compact hK
  have hiA := jitterFourierError_low_integrable_of_raw P n hn h δ hh hδ hi
  apply (hiA.union hiK).mono_set
  intro t ht
  by_cases hlow : |t| ≤ a
  · left
    simpa only [a, neg_mul] using abs_le.1 hlow
  · exact Or.inr ⟨ht, (lt_of_not_ge hlow).le⟩

/-- Restrict the already proved raw low-frequency estimate to a smaller
positive radius. Both integrability and the scaled little-o bound are inherited
from nonnegativity; no new estimate or assumption is introduced. -/
theorem manuscript_raw_low_frequency_shrink (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (h δ d : ℝ) (hsmall : d ≤ δ)
    (hi : ∀ j, IntegrableOn (rawJitterFourierError (P j) (n j) h) (Icc (-δ) δ))
    (hlow : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-δ) δ, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0)) :
    (∀ j, IntegrableOn (rawJitterFourierError (P j) (n j) h) (Icc (-d) d)) ∧
      Tendsto (fun j => Real.sqrt (n j : ℝ) *
        ∫ u in Icc (-d) d, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0) := by
  have hsub : Icc (-d) d ⊆ Icc (-δ) δ := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  refine ⟨fun j => (hi j).mono_set hsub, ?_⟩
  apply squeeze_zero _ _ hlow
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (rawJitterFourierError_nonneg (P j) (n j) h))
  · intro j
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact setIntegral_mono_set (hi j)
      (ae_of_all _ (rawJitterFourierError_nonneg (P j) (n j) h)) (ae_of_all _ hsub)

/-- Compact raw-frequency assembly, conditional only on the actual integral
estimate at frequency zero. Every nonzero resonance and the comparison tail
are handled by previously proved general moment-bound estimates. -/
theorem general_compact_rawJitterFourier_of_low
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (h δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (hi : ∀ j, IntegrableOn (rawJitterFourierError (P j) (n j) h) (Icc (-δ) δ))
    (hlow : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-δ) δ, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0))
    (T : ℝ) (hδT : δ < T)
    (hisolated : ∀ u, |u| ≤ 2 * δ → u ∈ resonanceSubgroup Q.measure → u = 0)
    (hTnr : T ∉ resonanceSubgroup Q.measure)
    (hnegTnr : -T ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-T) T, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0) := by
  let A := Icc (-δ) δ
  let K := manuscriptFrequencyAnnulus δ T
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hl : ∀ u ∈ K, δ ≤ |u| := fun _ hu => hu.2
  have hu : ∀ u ∈ K, |u| ≤ T := fun _ hu => abs_le.2 hu.1
  have hcover : Icc (-T) T ⊆ A ∪ K := by
    intro u humem
    by_cases hlow : |u| ≤ δ
    · exact Or.inl (abs_le.1 hlow)
    · exact Or.inr ⟨humem, (lt_of_not_ge hlow).le⟩
  have haway := manuscript_separated_rawJitterFourierError_away_tendsto_zero P Q hw hW3 B hB n hn h hh hzero
    δ T hδ hisolated hTnr hnegTnr
  have hsum := hlow.add haway
  simp only [add_zero] at hsum
  apply squeeze_zero _ _ hsum
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (rawJitterFourierError_nonneg (P j) (n j) h))
  · intro j
    have hiK := rawJitterFourierError_away_integrable (P j) (n j) (hn1 j) h B δ T
      (hB j) hδ K hK hl hu
    have hiAll : IntegrableOn (rawJitterFourierError (P j) (n j) h) (Icc (-T) T) :=
      ((hi j).union hiK).mono_set hcover
    have he := manuscript_low_annulus_integral_decomposition δ T hδT
      (rawJitterFourierError (P j) (n j) h) hiAll
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (le_of_eq he) (Real.sqrt_nonneg (n j : ℝ))

theorem general_compact_jitterFourier_of_low
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (h δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (hi : ∀ j, IntegrableOn (rawJitterFourierError (P j) (n j) h) (Icc (-δ) δ))
    (hlow : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-δ) δ, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0))
    (T : ℝ) (hT : 0 ≤ T) (hδT : δ < T)
    (hisolated : ∀ u, |u| ≤ 2 * δ → u ∈ resonanceSubgroup Q.measure → u = 0)
    (hTnr : T ∉ resonanceSubgroup Q.measure)
    (hnegTnr : -T ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ t in Icc (-T * Real.sqrt (n j : ℝ)) (T * Real.sqrt (n j : ℝ)),
        jitterFourierError (P j) (n j) h t) atTop (𝓝 0) := by
  have hraw := general_compact_rawJitterFourier_of_low P Q hw hW3 B hB n hn hn1 h δ hh hδ hzero hi hlow T hδT hisolated hTnr hnegTnr
  convert hraw using 1
  funext j
  rw [rawJitterFourierError_integral_scale (P j) (n j) (hn1 j) h (-T) T hh (by linarith)]
  simp only [mul_comm]

theorem general_actual_jitter_smoothing_bound (S : PublishedSignedSmoothing)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (B : ℝ) (hB : thirdMoment P ≤ B)
    (h : ℝ) (L : ℝ) (hL : 0 < L)
    (hi : IntegrableOn (jitterFourierError P n h) (Icc (-L) L)) (x : ℝ) :
    |jitterCDFError P n h x| ≤ (1 / 4) *
      (∫ t in Icc (-L) L, jitterFourierError P n h t) +
        (24) * ((1 + 3 * B) * phi0) / L := by
  have hB0 : 0 ≤ B := (thirdMoment_pos P).le.trans hB
  have hg : ∀ x, |edgeworthDensity n (signedThirdMoment P) x| ≤ (1 + 3 * B) * phi0 :=
    edgeworthDensity_uniform_bound n hn (signedThirdMoment P) B ((signedThirdMoment_abs_le P).trans hB)
  have hi' : IntegrableOn (fun t => ‖charFun (normalizedJitteredSumLaw P n h) t -
      densityFourier (edgeworthDensity n (signedThirdMoment P)) t‖ / |t|) (Icc (-L) L) := by
    simpa only [edgeworthDensity_fourier, jitterFourierError] using hi
  have hbnd := S.bound (normalizedJitteredSumLaw P n h) (normalizedJitteredSumLaw_probability P n h)
    (normalizedJitteredSumLaw_first_integrable P n h)
    (edgeworthDensity n (signedThirdMoment P)) (edgeworthDensity_integrable _ _) (edgeworthDensity_first_integrable _ _) (edgeworthDensity_mass_one _ _)
    ((1 + 3 * B) * phi0) L (mul_pos (by linarith) phi0_pos) hL hg hi' x
  simpa only [← edgeworthCDF_cumulative, edgeworthDensity_fourier, jitterCDFError, jitterFourierError] using hbnd

/-- General actual jitter-CDF assembly. The only manuscript sublemma supplied
as an argument is the integrable raw low-frequency error with vanishing scaled
integral; it is not an external published input. -/
theorem general_jitter_uniform_expansion_of_raw_low (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (h δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (hi : ∀ j, IntegrableOn (rawJitterFourierError (P j) (n j) h) (Icc (-δ) δ))
    (hlow : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-δ) δ, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0)) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop := by
  obtain ⟨d, hd, hdδ, hisolated⟩ := manuscript_low_resonance_isolation Q δ hδ
  obtain ⟨hid, hlowd⟩ := manuscript_raw_low_frequency_shrink P n h δ d hdδ hi hlow
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  let C := (24) * ((1 + 3 * B) * phi0)
  have htail : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨R, hR⟩ := eventually_atTop.1 ((eventually_gt_atTop (0 : ℝ)).and
    (htail.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))))
  obtain ⟨T, hT, hmaxT, hTnr, hnegTnr⟩ := manuscript_nonresonant_cutoff Q (max R d)
  have hRT : R < T := (le_max_left R d).trans_lt hmaxT
  have hdT : d < T := (le_max_right R d).trans_lt hmaxT
  have hTC := (hR T hRT.le).2
  have hI := (general_compact_jitterFourier_of_low P Q hw hW3 B hB n hn hn1 h d hh hd hzero hid hlowd T hT.le hdT hisolated hTnr hnegTnr).const_mul (1 / 4)
  simp only [mul_zero] at hI
  filter_upwards [hI.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hj
  intro x
  have hnpos : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by have := hn1 j; omega)
  have hs : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.2 hnpos
  have hfull := jitterFourierError_integrable_of_raw_low (P j) (n j) (hn1 j) h d hh hd (hid j)
    (T * Real.sqrt (n j : ℝ))
  have hsm := general_actual_jitter_smoothing_bound S (P j) (n j) (hn1 j) B (hB j) h
    (T * Real.sqrt (n j : ℝ)) (mul_pos hT hs) hfull x
  have hbnd := mul_le_mul_of_nonneg_left hsm hs.le
  have he : Real.sqrt (n j : ℝ) * ((1 / 4) *
      (∫ t in Icc (-(T * Real.sqrt (n j : ℝ))) (T * Real.sqrt (n j : ℝ)),
        jitterFourierError (P j) (n j) h t) + C / (T * Real.sqrt (n j : ℝ))) =
      (1 / 4) * (Real.sqrt (n j : ℝ) *
        ∫ t in Icc (-T * Real.sqrt (n j : ℝ)) (T * Real.sqrt (n j : ℝ)),
          jitterFourierError (P j) (n j) h t) + C / T := by
    rw [neg_mul]
    field_simp [hs.ne', hT.ne']
    <;> ring
  change Real.sqrt (n j : ℝ) * |jitterCDFError (P j) (n j) h x| ≤ _ at hbnd
  rw [he] at hbnd
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_mul, abs_of_pos hs]
  linarith

end BerryEsseen
