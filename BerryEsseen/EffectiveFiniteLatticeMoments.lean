import BerryEsseen.EffectiveRoundedMoments
import BerryEsseen.RawMaximalSpan

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The finite approximation and all moment/span assertions preceding the uniform
jitter estimate in the manuscript's effective-global-jitter lemma. -/
theorem effective_finite_lattice_moments (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) (hviol : ¬ BoundAt P n) :
    ∃ (Q : Measure ℝ) (F : Finset ℝ) (h : ℝ),
      IsProbabilityMeasure Q ∧ F.card < 2000 ∧ Q.support ⊆ (F : Set ℝ) ∧
      (∀ x ∈ F, |x| < 13) ∧ (∀ x ∈ F, appendixRetention ≤ Q.real {x}) ∧
      Real.pi / 500 ≤ h ∧ h ≤ 5 ∧ IsLatticeSpan Q h ∧
      (∀ d : ℝ, IsLatticeSpan Q d → d ≤ h) ∧
      wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      |rawMean Q| ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention ∧
      |rawThirdAbsoluteMoment Q - thirdMoment P| +
        |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 2 * (10 : ℝ) ^ 9 * appendixRetention ∧
      ∃ Z : StandardizedLaw,
        Z.measure = standardizedMeasure Q (rawMean Q) (rawStdDev Q) ∧
        Z.measure.support ⊆ Icc (-15) 15 ∧ thirdMoment Z < 2 ∧
        IsMaximalSpan Z (h / rawStdDev Q) := by
  have hn1 : 1 ≤ n := by
    have hnbig := (appendix_sample_size_bounds n (appendix_conf_sample_size n hn).1).1
    omega
  have hβ : thirdMoment P ≤ 1.84 := by
    have hviol' := hviol
    rw [BoundAt_iff_normalized P n hn1] at hviol'
    push_neg at hviol'
    obtain ⟨x, hx⟩ := hviol'
    exact ((normalized_violation_momentCutoff H P n hn1 x hx).trans momentCutoff_bounds.2).le
  obtain ⟨Q, F, h₀, hprob, hcard, hsQ, hbF, haF, hlo, hhi, hlat, hW⟩ :=
    effective_finite_lattice_approximation H S K P n hn hsupp hviol
  letI : IsProbabilityMeasure Q := hprob
  have hbQ : ∀ᵐ x ∂Q, |x| ≤ 13 := by
    filter_upwards [Q.support_mem_ae] with x hx
    exact (hbF x (hsQ hx)).le
  have hbP : ∀ᵐ x ∂P.measure, |x| ≤ 6 := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact abs_le.mpr (hsupp hx)
  obtain ⟨hm, hσ, hv, hthird, hρ, Z, hmap, hsZ, hZβ⟩ := effective_rounded_moment_bounds K P Q hbP hbQ hβ hW
  obtain ⟨h, k, hlower, hupper, hh, hmax, hzmax, hk, he⟩ :=
    effective_raw_maximal_span E Q Z (rawMean Q) (rawStdDev Q) h₀ hσ hmap hZβ hlo hlat
  exact ⟨Q, F, h, hprob, hcard, hsQ, hbF, haF, hlower, hupper, hh, hmax,
    hW, hm, hv, hthird, Z, hmap, hsZ, hZβ, hzmax⟩

end BerryEsseen
