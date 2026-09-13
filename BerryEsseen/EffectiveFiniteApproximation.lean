import BerryEsseen.FiniteRetention
import BerryEsseen.GlobalParameters

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem effective_finite_lattice_approximation (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) (hviol : ¬ BoundAt P n) :
    ∃ (Q : Measure ℝ) (F : Finset ℝ) (h : ℝ),
      IsProbabilityMeasure Q ∧ F.card < 2000 ∧ Q.support ⊆ (F : Set ℝ) ∧
      (∀ x ∈ F, |x| < 13) ∧ (∀ x ∈ F, appendixRetention ≤ Q.real {x}) ∧
      Real.pi / 500 ≤ h ∧ h ≤ 4 * Real.pi ∧ IsLatticeSpan Q h ∧
      wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention := by
  have hnbig := (appendix_sample_size_bounds n (appendix_conf_sample_size n hn).1).1
  obtain ⟨a, h, hlo, hhi, hprob, hcard, hs0, hb0, hlat, herr, hW⟩ :=
    effective_finite_lattice_rounding H S K P n (by omega) hsupp hviol
  let μ := latticeRoundedMeasure P a h
  let F := latticeRoundingPoints a h
  let E := retainedAtoms μ F appendixRetention
  let Q := retainedMeasure μ F appendixRetention
  letI : IsProbabilityMeasure μ := hprob
  have hF : ∀ᵐ x ∂μ, x ∈ F := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hs0 hx
  have hτ := appendix_retention_bounds.1
  have hcardR : (F.card : ℝ) ≤ 2000 := by exact_mod_cast hcard.le
  have hsmall : (F.card : ℝ) * appendixRetention < 1 :=
    (mul_le_mul_of_nonneg_right hcardR hτ.le).trans_lt appendix_retention_bounds.2.1
  letI : IsProbabilityMeasure Q := retainedMeasure_probability μ F appendixRetention hτ.le hF hsmall
  have hsQ : Q.support ⊆ (E : Set ℝ) := retainedMeasure_support μ F appendixRetention
  have hbμ : ∀ᵐ x ∂μ, |x| ≤ 13 := by
    filter_upwards [hF] with x hx
    exact (hb0 x hx).le
  have hbQ : ∀ᵐ x ∂Q, |x| ≤ 13 := retainedMeasure_bounded μ F appendixRetention 13 hbμ
  have hiμ := real_function_integrable_of_abs_le μ (fun x : ℝ => x) 13 measurable_id hbμ
  have hiQ := real_function_integrable_of_abs_le Q (fun x : ℝ => x) 13 measurable_id hbQ
  refine ⟨Q, E, h, inferInstance,
    (Finset.card_le_card (retainedAtoms_subset μ F appendixRetention)).trans_lt hcard, hsQ,
    (fun x hx => hb0 x (retainedAtoms_subset μ F appendixRetention hx)),
    (fun x hx => retainedMeasure_atom_lower μ F appendixRetention hτ.le hF hsmall x hx),
    hlo, hhi, ?_, ?_⟩
  · refine ⟨hlat.1, a, ?_⟩
    intro x hx
    have hxf : x ∈ F := retainedAtoms_subset μ F appendixRetention (hsQ hx)
    change x ∈ (latticeRoundingIndices a h).image (fun k : ℤ => a + h * (k : ℝ)) at hxf
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hxf
    exact ⟨k, by ring⟩
  · have hr := retainedMeasure_wasserstein K μ F appendixRetention 13 hτ.le (by norm_num) hF hsmall hbμ
    have htriangle := wassersteinOne_triangle K P.measure μ Q P.first_integrable hiμ hiQ
    have he := appendix_rounding_below_retention n hn
    have hr' : wassersteinOne μ Q ≤ 52000 * appendixRetention := by
      have hc := mul_le_mul_of_nonneg_right hcardR hτ.le
      change wassersteinOne μ Q ≤ 2 * 13 * (F.card : ℝ) * appendixRetention at hr
      nlinarith only [hr, hc]
    change wassersteinOne P.measure μ ≤ _ at hW
    nlinarith only [htriangle, hW, he, hr', hτ]

end BerryEsseen
