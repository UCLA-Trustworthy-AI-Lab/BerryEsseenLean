import BerryEsseen.Attainment
import BerryEsseen.ManuscriptExtremalLimit

/-! The full bounded-extremizer extraction in the manuscript's Section 4. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- Attainment and the radius-ten argument depend only on an already
proved harmonic selection witness. -/
theorem bounded_extremizing_sequence_of_selection (H : ClassicalBerryEsseenBounds)
    (hselection : ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ cE < extremalConstant (u j)) ∧
      Tendsto (fun j => scaledDrop extremalConstant (u j)) atTop (𝓝 0)) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) := by
  obtain ⟨u, hu, hupos, hdrop⟩ := hselection
  have he : ∀ᶠ j in atTop, 2 ≤ u j ∧ scaledDrop extremalConstant (u j) ≤ 1 := by
    filter_upwards [hu.tendsto_atTop.eventually (eventually_ge_atTop 2),
      hdrop.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj hd
    exact ⟨hj, hd.le⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.1 he
  let n : ℕ → ℕ := fun j => u (j + J)
  have hn (j : ℕ) : 2 ≤ n j := (hJ (j + J) (by omega)).1
  have hd (j : ℕ) : scaledDrop extremalConstant (n j) ≤ 1 := (hJ (j + J) (by omega)).2
  have hc (j : ℕ) : cE < extremalConstant (n j) := (hupos (j + J)).2
  have hne (j : ℕ) : n j - 1 + 1 = n j := Nat.sub_add_cancel (by have := hn j; omega)
  have hex (j : ℕ) := extremal_attainment H (n j - 1) (by rw [hne j]; exact hc j)
  choose P t hattain hβ hβB using hex
  have hatt (j : ℕ) : signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) := by
    simpa only [hne j] using hattain j
  refine ⟨n, P, t, ?_, ?_, ?_⟩
  · intro i j hij
    exact hu (by omega)
  · intro j
    refine ⟨hn j, hatt j, hc j, hβ j, hβB j, ?_⟩
    apply extremizer_support_subset_ten H (P j) (n j - 1) (by have := hn j; omega) (t j)
      (hattain j) (by rw [hatt j]; exact hc j)
    rw [hne j]
    exact hd j
  · exact hdrop.comp (tendsto_add_atTop_nat J)

/-- Historical selection interface, retained for existing consumers. -/
theorem bounded_extremizing_sequence (H : ClassicalBerryEsseenBounds)
    (hviol : ∀ K : ℕ, ∃ n ≥ K, cE < extremalConstant n) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) :=
  bounded_extremizing_sequence_of_selection H (extremal_harmonic_selection H hviol)

/-- The original arbitrarily-late-violation statement, with the original full-limit selection. -/
theorem manuscript_bounded_extremizing_sequence (H : ClassicalBerryEsseenBounds)
    (A : PublishedEsseenFixedLawAsymptotic)
    (hviol : ∀ K : ℕ, ∃ n ≥ K, cE < extremalConstant n) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) :=
  bounded_extremizing_sequence_of_selection H (manuscript_extremal_harmonic_selection H A hviol)

theorem manuscript_bounded_extremizing_sequence_of_not_main
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (hmain : ¬ MainClaim) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) :=
by
  apply manuscript_bounded_extremizing_sequence H A
  intro K
  by_contra h
  push_neg at h
  apply hmain
  apply (mainClaim_iff_extremalConstant H).2
  exact ⟨max K 1, le_max_right _ _, fun n hn => h n ((le_max_left _ _).trans hn)⟩

theorem bounded_extremizing_sequence_of_not_main (H : ClassicalBerryEsseenBounds)
    (hmain : ¬ MainClaim) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) := by
  apply bounded_extremizing_sequence H
  intro K
  by_contra h
  push_neg at h
  apply hmain
  apply (mainClaim_iff_extremalConstant H).2
  exact ⟨max K 1, le_max_right _ _, fun n hn => h n ((le_max_left _ _).trans hn)⟩

end BerryEsseen
