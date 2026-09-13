import BerryEsseen.GeneralJitterExpansion
import BerryEsseen.GeneralSignedThirdLimit

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem wassersteinThree_jitter_envelopes
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h) (hspan : 0 < h → IsLatticeSpan Q.measure h)
    (hmax : ∀ d, IsLatticeSpan Q.measure d → d ≤ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      edgeworthEnvelope (-h) (signedThirdMoment (P j)) x - ε ≤
        Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤
        edgeworthEnvelope h (signedThirdMoment (P j)) x + ε := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  obtain ⟨B, hB⟩ := hm.bddAbove_range
  exact general_jitter_envelopes_of_expansion P n hn hn1 B
    (fun j => (signedThirdMoment_abs_le (P j)).trans (hB ⟨j, rfl⟩)) h hh
    (maximal_span_wassersteinThree_jitter_expansion W S P Q hW n hn h hh hspan hmax)

theorem wassersteinThree_jitter_limit_envelopes
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h) (hspan : 0 < h → IsLatticeSpan Q.measure h)
    (hmax : ∀ d, IsLatticeSpan Q.measure d → d ≤ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      edgeworthEnvelope (-h) (signedThirdMoment Q) x - ε ≤
        Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤
        edgeworthEnvelope h (signedThirdMoment Q) x + ε := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  obtain ⟨B, hB⟩ := hm.bddAbove_range
  exact general_jitter_limit_envelopes_of_expansion P n hn hn1 B
    (fun j => (signedThirdMoment_abs_le (P j)).trans (hB ⟨j, rfl⟩)) h hh
    (maximal_span_wassersteinThree_jitter_expansion W S P Q hW n hn h hh hspan hmax)
    (signedThirdMoment Q) (weak_thirdMoment_signedThirdMoment_tendsto P Q hw hm)

/-- The complete limsup statement of the manuscript jitter-envelope corollary. -/
theorem wassersteinThree_jitter_limsup
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h) (hspan : 0 < h → IsLatticeSpan Q.measure h)
    (hmax : ∀ d, IsLatticeSpan Q.measure d → d ≤ h) :
    atTop.limsup (fun j => scaledSumCDFSup (P j) (n j)) ≤
      (|signedThirdMoment Q| + 3 * h) * phi0 / 6 := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  obtain ⟨B, hB⟩ := hm.bddAbove_range
  exact general_jitter_limsup_of_expansion P n hn hn1 B
    (fun j => (signedThirdMoment_abs_le (P j)).trans (hB ⟨j, rfl⟩)) h hh
    (maximal_span_wassersteinThree_jitter_expansion W S P Q hW n hn h hh hspan hmax)
    (signedThirdMoment Q) (weak_thirdMoment_signedThirdMoment_tendsto P Q hw hm)

end BerryEsseen
