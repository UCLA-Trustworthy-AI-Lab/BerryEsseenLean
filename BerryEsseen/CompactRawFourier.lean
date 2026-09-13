import BerryEsseen.SpectralIntegrals
import BerryEsseen.ManuscriptSeparatedResonancePartition

/-! The manuscript compact-frequency decomposition: finitely many disjoint
resonance intervals and one compact nonresonant remainder. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- Fixed nonresonant cutoff version. Every moving peak is constructed on the
same interval selected by the disjoint partition; the exact integral
partition is used before taking the finite sum of limits. -/
theorem manuscript_partition_rawFourier_integral_tendsto_zero
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (K : Set ℝ) (hK : IsCompact K) (a T : ℝ) (ha : 0 < a)
    (haway : ∀ u ∈ K, a ≤ |u|) (hbound : ∀ u ∈ K, |u| ≤ T)
    (hT : T ∉ resonanceSubgroup Q.measure) (hnegT : -T ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in K, rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
  classical
  have hr0 : ∀ r ∈ K, r ≠ 0 := by
    intro r hr hz
    have hv := haway r hr
    rw [hz, abs_zero] at hv
    linarith
  have hloc : ∀ r : ℝ, ∃ d : ℝ, ∀ (_ : r ∈ K) (_ : r ∈ resonanceSubgroup Q.measure),
      0 < d ∧ d ≤ |r| / 2 ∧
      (∀ u ∈ Icc (r - d) (r + d), characteristicSquareCurvature Q u ≤ -3 / 2) ∧
      (∀ u ∈ Icc (r - d) (r + d), u ≠ r → characteristicSquare Q u < characteristicSquare Q r) := by
    intro r
    by_cases hr : r ∈ K ∧ r ∈ resonanceSubgroup Q.measure
    · obtain ⟨d, hd, hdr, hc, hs⟩ := resonance_neighborhood Q r (hr0 r hr.1) hr.2
      exact ⟨d, fun _ _ => ⟨hd, hdr, hc, hs⟩⟩
    · exact ⟨1, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
  choose d₀ hd₀ using hloc
  obtain ⟨D, hDsmall⟩ := manuscript_resonance_partition_exists Q K hK T hT hnegT hbound d₀
    (fun r hr hs => (hd₀ r hr hs).1) (fun r hr hs => (hd₀ r hr hs).2.1)
  have hlim : ∀ r ∈ D.centers,
      Tendsto (fun j => Real.sqrt (n j : ℝ) *
        ∫ u in Icc (r - D.radius r) (r + D.radius r),
          rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
    intro r hr
    have hmem := (D.centers_spec r).1 hr
    have hsub : Icc (r - D.radius r) (r + D.radius r) ⊆ Icc (r - d₀ r) (r + d₀ r) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, hDsmall r hr]
    exact actual_resonance_integral_tendsto_zero_on P Q hw hW3 B hB n hn h r (D.radius r)
      hh (hr0 r hmem.1) (D.radius_pos r hr) (D.radius_away r hr)
      (fun u hu => (hd₀ r hmem.1 hmem.2).2.2.1 u (hsub hu))
      (fun u hu => (hd₀ r hmem.1 hmem.2).2.2.2 u (hsub hu))
      (hzero r (hr0 r hmem.1) hmem.2)
  have hresidual := actual_spectral_integral_tendsto_zero P Q hw hW3 n hn h a D.remainder
    (D.remainder_compact hK) ha (fun u hu => haway u hu.1) D.remainder_nonresonant
  have hsum : Tendsto (fun j => ∑ r ∈ D.centers, Real.sqrt (n j : ℝ) *
      ∫ u in Icc (r - D.radius r) (r + D.radius r),
        rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum D.centers hlim
  have htotal := hresidual.add hsum
  simp only [add_zero] at htotal
  apply squeeze_zero _ _ htotal
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (rawJitterFourierIntegrand_nonneg (P j) (n j) h))
  · intro j
    let f := rawJitterFourierIntegrand (P j) (n j) h
    have hiK : IntegrableOn f K := rawJitterFourier_integrableOn (P j) (n j) h a K hK ha haway
    have he := D.integral_decomposition hK.measurableSet f hiK
    have hle : (∫ u in K, f u) ≤ (∫ u in D.remainder, f u) +
        ∑ r ∈ D.centers, ∫ u in Icc (r - D.radius r) (r + D.radius r), f u := by
      rw [he]
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro r hr
      have hmem := (D.centers_spec r).1 hr
      have hiR : IntegrableOn f (Icc (r - D.radius r) (r + D.radius r)) :=
        rawJitterFourier_integrableOn (P j) (n j) h (|r| / 2)
          (Icc (r - D.radius r) (r + D.radius r)) isCompact_Icc
          (div_pos (abs_pos.2 (hr0 r hmem.1)) (by norm_num))
          (resonance_interval_away_zero r (D.radius r) (D.radius_away r hr))
      exact setIntegral_mono_set hiR
        (ae_of_all _ (rawJitterFourierIntegrand_nonneg (P j) (n j) h))
        (ae_of_all _ (fun _ hu => Ioo_subset_Icc_self hu.2))
    simpa only [mul_add, Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg (n j : ℝ))

theorem manuscript_separated_rawFourier_integral_tendsto_zero
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (a T : ℝ) (ha : 0 < a)
    (hisolated : ∀ u, |u| ≤ 2 * a → u ∈ resonanceSubgroup Q.measure → u = 0)
    (hT : T ∉ resonanceSubgroup Q.measure) (hnegT : -T ∉ resonanceSubgroup Q.measure) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in manuscriptFrequencyAnnulus a T, rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
  classical
  let K := manuscriptFrequencyAnnulus a T
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have haway : ∀ u ∈ K, a ≤ |u| := fun _ hu => hu.2
  have hr0 : ∀ r ∈ K, r ≠ 0 := by
    intro r hr hz
    have hv := haway r hr
    rw [hz, abs_zero] at hv
    linarith
  have hloc : ∀ r : ℝ, ∃ d : ℝ, ∀ (_ : r ∈ K) (_ : r ∈ resonanceSubgroup Q.measure),
      0 < d ∧ d ≤ |r| / 2 ∧
      (∀ u ∈ Icc (r - d) (r + d), characteristicSquareCurvature Q u ≤ -3 / 2) ∧
      (∀ u ∈ Icc (r - d) (r + d), u ≠ r → characteristicSquare Q u < characteristicSquare Q r) := by
    intro r
    by_cases hr : r ∈ K ∧ r ∈ resonanceSubgroup Q.measure
    · obtain ⟨d, hd, hdr, hc, hs⟩ := resonance_neighborhood Q r (hr0 r hr.1) hr.2
      exact ⟨d, fun _ _ => ⟨hd, hdr, hc, hs⟩⟩
    · exact ⟨1, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
  choose d₀ hd₀ using hloc
  obtain ⟨Dsep, hDsmall⟩ := manuscript_separated_resonance_partition_exists Q a T ha hisolated hT hnegT d₀
    (fun r hr hs => (hd₀ r hr hs).1) (fun r hr hs => (hd₀ r hr hs).2.1)
  let D := Dsep.toManuscriptResonancePartition
  have hlim : ∀ r ∈ D.centers,
      Tendsto (fun j => Real.sqrt (n j : ℝ) *
        ∫ u in Icc (r - D.radius r) (r + D.radius r),
          rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
    intro r hr
    have hmem := (D.centers_spec r).1 hr
    have hsub : Icc (r - D.radius r) (r + D.radius r) ⊆ Icc (r - d₀ r) (r + d₀ r) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, hDsmall r hr]
    exact actual_resonance_integral_tendsto_zero_on P Q hw hW3 B hB n hn h r (D.radius r)
      hh (hr0 r hmem.1) (D.radius_pos r hr) (D.radius_away r hr)
      (fun u hu => (hd₀ r hmem.1 hmem.2).2.2.1 u (hsub hu))
      (fun u hu => (hd₀ r hmem.1 hmem.2).2.2.2 u (hsub hu))
      (hzero r (hr0 r hmem.1) hmem.2)
  have hresidual := actual_spectral_integral_tendsto_zero P Q hw hW3 n hn h a D.remainder
    (D.remainder_compact hK) ha (fun u hu => haway u hu.1) D.remainder_nonresonant
  have hsum : Tendsto (fun j => ∑ r ∈ D.centers, Real.sqrt (n j : ℝ) *
      ∫ u in Icc (r - D.radius r) (r + D.radius r),
        rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum D.centers hlim
  have htotal := hresidual.add hsum
  simp only [add_zero] at htotal
  apply squeeze_zero _ _ htotal
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (rawJitterFourierIntegrand_nonneg (P j) (n j) h))
  · intro j
    let f := rawJitterFourierIntegrand (P j) (n j) h
    have hiK : IntegrableOn f K := rawJitterFourier_integrableOn (P j) (n j) h a K hK ha haway
    have he := Dsep.integral_decomposition f hiK
    have hle := le_of_eq he
    simpa only [mul_add, Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg (n j : ℝ))

/-- The arbitrary-compact API is retained by selecting a larger fixed
nonresonant cutoff, then using the disjoint resonance partition. -/
theorem compact_rawFourier_integral_tendsto_zero (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (K : Set ℝ) (hK : IsCompact K) (a : ℝ) (ha : 0 < a) (haway : ∀ u ∈ K, a ≤ |u|) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in K, rawJitterFourierIntegrand (P j) (n j) h u) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨T, _, hRT, hT, hnegT⟩ := manuscript_nonresonant_cutoff Q R
  have hbound : ∀ u ∈ K, |u| ≤ T := by
    intro u hu
    have hb := hR hu
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hb
    exact hb.trans hRT.le
  exact manuscript_partition_rawFourier_integral_tendsto_zero P Q hw hW3 B hB n hn h hh hzero
    K hK a T ha haway hbound hT hnegT

end BerryEsseen
