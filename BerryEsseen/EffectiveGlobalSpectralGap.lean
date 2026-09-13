import BerryEsseen.FiniteSpectralGap
import BerryEsseen.GlobalSpectralBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem effective_global_spectral_gap (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) (hviol : ¬ BoundAt P n) :
    ∃ (Q : Measure ℝ) (F : Finset ℝ) (h : ℝ) (Z : StandardizedLaw),
      IsProbabilityMeasure Q ∧ F.card < 2000 ∧ Q.support ⊆ (F : Set ℝ) ∧
      (∀ x ∈ F, |x| < 13) ∧ (∀ x ∈ F, appendixRetention ≤ Q.real {x}) ∧
      h ∈ Icc (Real.pi / 500) 5 ∧ IsLatticeSpan Q h ∧
      (∀ d : ℝ, IsLatticeSpan Q d → d ≤ h) ∧
      wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      |rawMean Q| ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention ∧
      |rawThirdAbsoluteMoment Q - thirdMoment P| +
        |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 2 * (10 : ℝ) ^ 9 * appendixRetention ∧
      Z.measure = standardizedMeasure Q (rawMean Q) (rawStdDev Q) ∧
      Z.measure.support ⊆ Icc (-15) 15 ∧ thirdMoment Z < 2 ∧
      IsMaximalSpan Z (h / rawStdDev Q) ∧
      ∀ u : ℝ, |u| ≤ appendixGlobalCutoff →
        1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) →
        ‖charFun P.measure u‖ ≤ 1 - appendixGlobalGap := by
  have hnbig := (appendix_sample_size_bounds n (appendix_conf_sample_size n hn).1).1
  have hn1 : 1 ≤ n := by omega
  have hβ : thirdMoment P ≤ 1.84 := by
    have hv := hviol
    rw [BoundAt_iff_normalized P n hn1] at hv
    push_neg at hv
    obtain ⟨x, hx⟩ := hv
    exact ((normalized_violation_momentCutoff H P n hn1 x hx).trans momentCutoff_bounds.2).le
  obtain ⟨a, h₀, hlo, hhi, hprob, hcard, hs0, hb0, hlat, herr, hW⟩ :=
    effective_finite_lattice_rounding H S K P n (by omega) hsupp hviol
  have hh₀ : 0 < h₀ := hlat.1
  let μ := latticeRoundedMeasure P a h₀
  let F₀ := latticeRoundingPoints a h₀
  let F := retainedAtoms μ F₀ appendixRetention
  let Q := retainedMeasure μ F₀ appendixRetention
  letI : IsProbabilityMeasure μ := hprob
  have hF₀ : ∀ᵐ x ∂μ, x ∈ F₀ := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hs0 hx
  have hτ := appendix_retention_bounds.1
  have hcardR : (F₀.card : ℝ) ≤ 2000 := by exact_mod_cast hcard.le
  have hsmall : (F₀.card : ℝ) * appendixRetention < 1 :=
    (mul_le_mul_of_nonneg_right hcardR hτ.le).trans_lt appendix_retention_bounds.2.1
  letI : IsProbabilityMeasure Q := retainedMeasure_probability μ F₀ appendixRetention hτ.le hF₀ hsmall
  have hsQ : Q.support ⊆ (F : Set ℝ) := retainedMeasure_support μ F₀ appendixRetention
  have hFcard : F.card < 2000 :=
    (Finset.card_le_card (retainedAtoms_subset μ F₀ appendixRetention)).trans_lt hcard
  have hFbound : ∀ x ∈ F, |x| < 13 :=
    fun x hx => hb0 x (retainedAtoms_subset μ F₀ appendixRetention hx)
  have hFatom : ∀ x ∈ F, appendixRetention ≤ Q.real {x} :=
    fun x hx => retainedMeasure_atom_lower μ F₀ appendixRetention hτ.le hF₀ hsmall x hx
  have hbμ : ∀ᵐ x ∂μ, |x| ≤ 13 := by
    filter_upwards [hF₀] with x hx
    exact (hb0 x hx).le
  have hbQ : ∀ᵐ x ∂Q, |x| ≤ 13 := retainedMeasure_bounded μ F₀ appendixRetention 13 hbμ
  have hbP : ∀ᵐ x ∂P.measure, |x| ≤ 6 := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact abs_le.mpr (hsupp hx)
  have hiμ := real_function_integrable_of_abs_le μ (fun x : ℝ => x) 13 measurable_id hbμ
  have hiQ := real_function_integrable_of_abs_le Q (fun x : ℝ => x) 13 measurable_id hbQ
  have hQlat : IsLatticeSpan Q h₀ := by
    refine ⟨hh₀, a, ?_⟩
    intro x hx
    have hxf : x ∈ F₀ := retainedAtoms_subset μ F₀ appendixRetention (hsQ hx)
    change x ∈ (latticeRoundingIndices a h₀).image (fun k : ℤ => a + h₀ * (k : ℝ)) at hxf
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hxf
    exact ⟨k, by ring⟩
  have hWQ : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention := by
    have hr := retainedMeasure_wasserstein K μ F₀ appendixRetention 13 hτ.le (by norm_num) hF₀ hsmall hbμ
    have htriangle := wassersteinOne_triangle K P.measure μ Q P.first_integrable hiμ hiQ
    have he : 5 * Real.sqrt (Real.log (n : ℝ) / n) ≤ appendixRetention := by
      have hT : 1 ≤ appendixGlobalCutoff := Real.one_le_exp_iff.mpr (by norm_num [appendixA])
      have hE := mul_le_mul_of_nonneg_right hT
        (show 0 ≤ 5 * Real.sqrt (Real.log (n : ℝ) / n) by positivity)
      have hTe := appendix_global_rounding_frequency_budget n hn
      have hgτ : appendixGlobalGap ≤ appendixRetention := by
        have ht := appendix_retention_tiny
        have ht0 := appendix_retention_bounds.1.le
        unfold appendixGlobalGap
        norm_num
        nlinarith [mul_le_mul_of_nonneg_right ht ht0]
      nlinarith only [hE, hTe, hgτ]
    have hc := mul_le_mul_of_nonneg_right hcardR hτ.le
    change wassersteinOne μ Q ≤ 2 * 13 * (F₀.card : ℝ) * appendixRetention at hr
    change wassersteinOne P.measure μ ≤ _ at hW
    nlinarith only [htriangle, hW, he, hr, hc, hτ]
  obtain ⟨hm, hσ, hv, hthird, hρ, Z, hmap, hsZ, hZβ⟩ :=
    effective_rounded_moment_bounds K P Q hbP hbQ hβ hWQ
  obtain ⟨h, k, hlower, hupper, hh, hmax, hzmax, hk, he⟩ :=
    effective_raw_maximal_span E Q Z (rawMean Q) (rawStdDev Q) h₀ hσ hmap hZβ hlo hQlat
  refine ⟨Q, F, h, Z, inferInstance, hFcard, hsQ, hFbound, hFatom,
    ⟨hlower, hupper⟩, hh, hmax, hWQ, hm, hv, hthird, hmap, hsZ, hZβ, hzmax, ?_⟩
  intro u hu hdist
  have hFround : F ⊆ latticeRoundingPoints a h₀ := retainedAtoms_subset μ F₀ appendixRetention
  have h₀h : h₀ ≤ h := hmax h₀ hQlat
  have hspec := manuscript_finite_lattice_appendix_nonresonance_gap Q F a h₀ h u
    hsQ hFround hFatom hlo h₀h hh hmax hdist
  have hchar := charFun_rounding_retention_bound P a h₀ appendixRetention u hh₀ hτ.le hsupp hsmall
  let r := μ.real (F : Set ℝ)ᶜ
  have hrange : r ∈ Icc 0 (1 / 100) := by
    refine ⟨measureReal_nonneg, ?_⟩
    have hdel := retained_outside_mass μ F₀ appendixRetention hτ.le hF₀
    have hc := mul_le_mul_of_nonneg_right hcardR hτ.le
    change r ≤ _ at hdel
    nlinarith only [hdel, hc, appendix_retention_tiny]
  have herror0 : 0 ≤ ∫ x, |x - latticeRound a h₀ x| ∂P.measure := integral_nonneg (fun x => abs_nonneg _)
  have heU : |u| * (∫ x, |x - latticeRound a h₀ x| ∂P.measure) ≤ appendixGlobalGap := by
    have hmul := mul_le_mul hu herr herror0 (Real.exp_pos (20 * appendixA)).le
    exact hmul.trans (appendix_global_rounding_frequency_budget n hn)
  apply mixture_spectral_gap_absorption r appendixGlobalGap (‖charFun P.measure u‖) (‖charFun Q u‖)
    (|u| * (∫ x, |x - latticeRound a h₀ x| ∂P.measure)) hrange
    (by unfold appendixGlobalGap; positivity) _ hspec heU
  exact hchar

end BerryEsseen
