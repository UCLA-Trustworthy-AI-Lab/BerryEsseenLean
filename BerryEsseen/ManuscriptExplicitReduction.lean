import BerryEsseen.ManuscriptConfinement

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Actual interval stability conclusion used by the finite reduction.
The final theorem supplies its proof; this definition asserts nothing. -/
def ManuscriptEffectiveIntervalStabilityInput : Prop :=
  ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
    μ.support ⊆ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) →
    (|μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar ∨
      |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)| < appendixEtaStar) →
    ∀ (n : ℕ), appendixNStar ≤ n → rawNormalizedConstant μ n < cE

theorem manuscript_confined_extremizer_impossible
    (hstab : ManuscriptEffectiveIntervalStabilityInput)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n) (t : ℝ)
    (hatt : signedRatio P (n - 1) t = extremalConstant n)
    (hviol : cE < extremalConstant n)
    (hb : (P.measure.map (fun x => pE + sigmaE * x)).support ⊆
      Icc (-appendixEtaStar / 2) (appendixEtaStar / 2) ∪
        Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2))
    (hp : |(P.measure.map (fun x => pE + sigmaE * x)).real (Ioi (1 / 2)) - pE| < appendixEtaStar) :
    False := by
  let μ := P.measure.map (fun x => pE + sigmaE * x)
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hη := appendixEtaStar_bounds.1
  have hb' : μ.support ⊆ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) := by
    intro x hx
    rcases hb hx with hx | hx
    · left
      constructor <;> linarith [hx.1, hx.2]
    · right
      constructor <;> linarith [hx.1, hx.2]
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hb' hx
  have hp' : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar := by
    rw [← upper_interval_mass_eq μ appendixEtaStar (by linarith [hη.2]) hae]
    exact hp
  have hNstar := (appendix_conf_sample_size n hn).1
  have hn1 : 1 ≤ n := by have := appendixNConf_ge_two.trans hn; omega
  have hs := hstab μ inferInstance hb' (Or.inl hp') n hNstar
  rw [rawNormalizedConstant_eq μ P pE sigmaE sigmaE_pos
    (esseen_affine_standardization P) n hn1] at hs
  have he : n - 1 + 1 = n := by omega
  have hratio : signedRatio P (n - 1) t ≤
      sSup (range (normalizedDiscrepancy P n)) := by
    calc
      _ ≤ |signedRatio P (n - 1) t| := le_abs_self _
      _ = normalizedDiscrepancy P n (t / Real.sqrt ((n - 1 : ℕ) + 1 : ℝ)) := by
        simpa only [he] using abs_signedRatio_eq_normalized P (n - 1) t
      _ ≤ _ := le_csSup (normalizedDiscrepancy_range_bddAbove P n hn1) (mem_range_self _)
  rw [hatt] at hratio
  exact (not_lt_of_ge (hratio.trans hs.le)) hviol

/-- The original finite threshold argument using the proved manuscript confinement
and an actual interval stability endpoint, which is instantiated in the final theorem. -/
theorem manuscript_explicit_claim_of_interval_stability (H : ClassicalBerryEsseenBounds)
    (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality) (U : PublishedNonuniformBound)
    (hstab : ManuscriptEffectiveIntervalStabilityInput) : ExplicitClaim := by
  intro N hN P
  have hNconf : 2 * appendixNConf ≤ N := by rwa [explicitThreshold_eq_twice_conf] at hN
  have hN4 : 4 ≤ N := by have := appendixNConf_ge_two; omega
  have hN1 : 1 ≤ N := by omega
  apply (BoundAt_iff_normalized P N hN1).2
  intro x
  apply (normalizedDiscrepancy_le_extremalConstant H P N hN1 x).trans
  by_contra hC
  have hC : cE < extremalConstant N := lt_of_not_ge hC
  obtain ⟨n, hnm, hnN, hcn, hd1, hd2, hsupp⟩ :=
    effective_selection_with_support H N hN4 hC
  have hnconf : appendixNConf ≤ n := by
    unfold finiteHalfIndex at hnm
    omega
  have hn2 : 2 ≤ n := appendixNConf_ge_two.trans hnconf
  have he : n - 1 + 1 = n := by omega
  obtain ⟨Q, t, hatt, hβ1, hβ2⟩ := extremal_attainment H (n - 1) (by rwa [he])
  rw [he] at hatt
  have hb := (hsupp Q t hatt).trans Ioo_subset_Icc_self
  have hd := selected_drop_effective_bound N n hN4 (by omega) hnN hd2
  obtain ⟨hbc, hpc⟩ := manuscript_effective_confinement H E K U Q n t hnconf hatt hcn hb hd
  exact manuscript_confined_extremizer_impossible hstab Q n hnconf t hatt hcn hbc hpc

end BerryEsseen
