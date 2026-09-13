import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ExtremizerLimit

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem bounded_violating_wassersteinThree_subsequence
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
      Tendsto (z ∘ u) atTop (𝓝 0) ∧
      Tendsto (fun j => wassersteinThree (P (u j)).measure esseenLaw.measure) atTop (𝓝 0) := by
  obtain ⟨u, hu, hw, hβlim, hκlim, hz⟩ :=
    bounded_violating_subsequence W S E P hβ hb n hn hn2 z hviol
  refine ⟨u, hu, hw, hβlim, hκlim, hz, ?_⟩
  apply (standardized_wassersteinThree_tendsto_iff W (P ∘ u) esseenLaw).2
  exact ⟨hw, by simpa only [thirdMoment_esseen] using hβlim⟩

theorem identified_wassersteinThree_extremizing_sequence_of_not_main
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (hmain : ¬ MainClaim) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t j / Real.sqrt (n j : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun j => wassersteinThree (P j).measure esseenLaw.measure) atTop (𝓝 0) := by
  obtain ⟨n, P, t, hn, hprops, hd, hw, hβ, hκ, hz⟩ :=
    identified_extremizing_sequence_of_not_main H W S E hmain
  refine ⟨n, P, t, hn, hprops, hd, hw, hβ, hκ, hz, ?_⟩
  apply (standardized_wassersteinThree_tendsto_iff W P esseenLaw).2
  exact ⟨hw, by simpa only [thirdMoment_esseen] using hβ⟩

end BerryEsseen
