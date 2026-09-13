import BerryEsseen.ClassicalBounds
import BerryEsseen.PublishedEsseenFixedLawAsymptotic

/-! The manuscript's full extremal-constant limit and its direct harmonic
selection. The lower bound uses the cited fixed-law Esseen asymptotic;
the upper bound uses the classical uniform remainder. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The actual fixed Esseen law supplies a lower bound for the supremum
over all standardized laws, at every positive sample size. -/
theorem manuscript_fixed_esseen_sup_le_extremalConstant
    (H : ClassicalBerryEsseenBounds) (n : ℕ) (hn : 1 ≤ n) :
    sSup (range (normalizedDiscrepancy esseenLaw n)) ≤ extremalConstant n := by
  apply csSup_le (range_nonempty _)
  rintro r ⟨x, rfl⟩
  exact normalizedDiscrepancy_le_extremalConstant H esseenLaw n hn x

/-- Equation `eq:cn-limit`: convergence of the full sequence, without a
violation or subsequence hypothesis. -/
theorem manuscript_extremalConstant_tendsto
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic) :
    Tendsto extremalConstant atTop (𝓝 cE) := by
  have hlower := original_manuscript_esseen_constant_tendsto A
  have hrem : Tendsto (fun n : ℕ => (4.75 : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _
  have hupper : Tendsto (fun n : ℕ => cE + 4.75 / Real.sqrt (n : ℝ))
      atTop (𝓝 cE) := by
    simpa only [add_zero] using hrem.const_add cE
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact manuscript_fixed_esseen_sup_le_extremalConstant H n hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (extremalConstant_bounds H n hn).2

/-- Apply the harmonic lemma to the manuscript's actual sequence
`a_n = C_n - cE`, using the full limit just proved. -/
theorem manuscript_extremal_harmonic_selection
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (hviol : ∀ K : ℕ, ∃ n ≥ K, cE < extremalConstant n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ cE < extremalConstant (u j)) ∧
      Tendsto (fun j => scaledDrop extremalConstant (u j)) atTop (𝓝 0) := by
  have hzero : Tendsto (fun n => extremalConstant n - cE) atTop (𝓝 0) := by
    simpa only [sub_self] using (manuscript_extremalConstant_tendsto H A).sub_const cE
  have hpositive : ∀ K : ℕ, ∃ n ≥ K, 0 < extremalConstant n - cE := by
    intro K
    obtain ⟨n, hn, hv⟩ := hviol K
    exact ⟨n, hn, sub_pos.mpr hv⟩
  obtain ⟨u, hu, hp, hd⟩ :=
    manuscript_harmonic_selection (fun n => extremalConstant n - cE) hzero hpositive
  refine ⟨u, hu, fun j => ⟨(hp j).1, sub_pos.mp (hp j).2⟩, ?_⟩
  have he : (fun j => scaledDrop (fun n => extremalConstant n - cE) (u j)) =
      (fun j => scaledDrop extremalConstant (u j)) := by
    funext j
    unfold scaledDrop
    congr 2
    ring
  rwa [he] at hd

theorem manuscript_extremal_harmonic_selection_of_not_main
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (hmain : ¬ MainClaim) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ cE < extremalConstant (u j)) ∧
      Tendsto (fun j => scaledDrop extremalConstant (u j)) atTop (𝓝 0) := by
  apply manuscript_extremal_harmonic_selection H A
  intro K
  by_contra h
  push_neg at h
  apply hmain
  apply (mainClaim_iff_extremalConstant H).2
  exact ⟨max K 1, le_max_right _ _, fun n hn => h n ((le_max_left _ _).trans hn)⟩

end BerryEsseen
