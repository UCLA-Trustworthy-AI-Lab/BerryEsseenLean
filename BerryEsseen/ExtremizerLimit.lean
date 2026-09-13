import BerryEsseen.LimitIdentification
import BerryEsseen.BoundedExtremizers

/-! Extraction of an Esseen limit from the actual maximizing sequence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem signedRatio_violation_scaled (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ) (hv : cE < signedRatio P (n - 1) t) :
    cE * thirdMoment P ≤ Real.sqrt (n : ℝ) *
      (normalizedSumCDF P n (t / Real.sqrt (n : ℝ)) - normalCDF (t / Real.sqrt (n : ℝ))) := by
  have hne : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hnc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hne
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))).ne'
  have he : Real.sqrt (n : ℝ) * (t / Real.sqrt (n : ℝ)) = t := by field_simp
  unfold signedRatio at hv
  rw [hnc, hne] at hv
  rw [normalizedSumCDF, he]
  exact ((lt_div_iff₀ (thirdMoment_pos P)).1 hv).le

theorem bounded_violating_subsequence
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (P : ℕ → StandardizedLaw) (hβ : ∀ j, thirdMoment (P j) ≤ 2)
    (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (z : ℕ → ℝ) (hviol : ∀ j, cE * thirdMoment (P j) ≤
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) (z j) - normalCDF (z j))) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      Tendsto (fun j => (P (u j)).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P (u j))) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P (u j))) atTop (𝓝 kappaE) ∧
      Tendsto (z ∘ u) atTop (𝓝 0) := by
  obtain ⟨Q, u, b, hu, _, _, _, hw, _⟩ := standardized_moment_subsequence P 2 hβ
  have hi := bounded_violation_limit_identification W S E (P ∘ u) Q hw (fun j => hβ _) (fun j => hb _)
    (n ∘ u) (hn.comp hu.tendsto_atTop) (fun j => hn2 _) (z ∘ u) (fun j => hviol _)
  obtain ⟨rfl, hz⟩ := hi
  refine ⟨u, hu, hw, ?_, ?_, hz⟩
  · simpa only [thirdMoment_esseen] using
      bounded_thirdMoment_tendsto (P ∘ u) esseenLaw hw 10 (by norm_num) (fun j => hb _)
  · simpa only [signedThirdMoment_esseen] using
      bounded_signedThirdMoment_tendsto (P ∘ u) esseenLaw hw 10 (by norm_num) (fun j => hb _)

/-- Identify any bounded extremizing sequence supplied by a proved
selection, independently of the way the indices were selected. -/
theorem identified_extremizing_sequence_of_bounded
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (hbounded : ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0)) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t j / Real.sqrt (n j : ℝ)) atTop (𝓝 0) := by
  obtain ⟨n, P, t, hn, hprops, hd⟩ := hbounded
  have hβ (j : ℕ) : thirdMoment (P j) ≤ 2 := by
    have hp := (hprops j).2.2.2.2.1
    linarith [momentCutoff_bounds.2]
  have hb (j : ℕ) : ∀ᵐ x ∂(P j).measure, |x| ≤ 10 := by
    filter_upwards [(P j).measure.support_mem_ae] with x hx
    have hi := (hprops j).2.2.2.2.2 hx
    exact (abs_le.2 ⟨hi.1.le, hi.2.le⟩)
  have hv (j : ℕ) := signedRatio_violation_scaled (P j) (n j) (hprops j).1 (t j)
    (by rw [(hprops j).2.1]; exact (hprops j).2.2.1)
  obtain ⟨u, hu, hw, hβlim, hκlim, hz⟩ := bounded_violating_subsequence W S E P hβ hb n
    hn.tendsto_atTop (fun j => (hprops j).1) (fun j => t j / Real.sqrt (n j : ℝ)) hv
  exact ⟨n ∘ u, P ∘ u, t ∘ u, hn.comp hu, fun j => hprops (u j),
    hd.comp hu.tendsto_atTop, hw, hβlim, hκlim, hz⟩

/-- Historical extraction interface, retained for existing consumers. -/
theorem identified_extremizing_sequence_of_not_main
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (hmain : ¬ MainClaim) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t j / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
  identified_extremizing_sequence_of_bounded W S E
    (bounded_extremizing_sequence_of_not_main H hmain)

theorem manuscript_identified_extremizing_sequence_of_not_main
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (hmain : ¬ MainClaim) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t j / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
  identified_extremizing_sequence_of_bounded W S E
    (manuscript_bounded_extremizing_sequence_of_not_main H A hmain)

end BerryEsseen
