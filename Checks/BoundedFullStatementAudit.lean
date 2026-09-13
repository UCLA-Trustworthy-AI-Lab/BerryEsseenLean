import BerryEsseen.BoundedExtremizers

/-! Independent audit wrapper: restore the redundant full-supremum conjunct
of manuscript Proposition `prop:bounded-extremizers`, using the same n, P, t
returned by the production endpoint. No new external premise is added. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen.CurrentRecheck

theorem bounded_extremizers_full_manuscript_statement
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (hviol : ∀ K : ℕ, ∃ n ≥ K, cE < extremalConstant n) :
    ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧
        signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        sSup (range (normalizedDiscrepancy (P j) (n j))) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧
        1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) := by
  obtain ⟨n, P, t, hn, hprops, hd⟩ :=
    manuscript_bounded_extremizing_sequence H A hviol
  refine ⟨n, P, t, hn, ?_, hd⟩
  intro j
  obtain ⟨hnj, hatt, hc, hβ, hβB, hsupp⟩ := hprops j
  have he : n j - 1 + 1 = n j := Nat.sub_add_cancel (by omega)
  have hC : 0 ≤ extremalConstant (n j - 1 + 1) := by
    rw [he]
    exact (cE_pos.trans hc).le
  have hatt' : signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j - 1 + 1) := by
    rwa [he]
  have hfull := manuscript_attained_full_ratio H (P j) (n j - 1) (t j) hC hatt'
  rw [he] at hfull
  exact ⟨hnj, hatt, hfull, hc, hβ, hβB, hsupp⟩

#check bounded_extremizers_full_manuscript_statement
#print axioms bounded_extremizers_full_manuscript_statement

end BerryEsseen.CurrentRecheck
