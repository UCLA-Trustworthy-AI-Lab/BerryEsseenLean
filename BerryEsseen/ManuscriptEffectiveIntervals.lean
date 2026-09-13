import BerryEsseen.ManuscriptExplicitReduction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The real two-cluster stability conclusion; its proof is supplied to the
interval wrapper and instantiated in the manuscript's final explicit theorem. -/
def ManuscriptEffectiveClusterStabilityInput : Prop :=
  ∀ (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)),
    (∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA)) →
    (∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA)) →
    ∀ (n : ℕ), appendixNStar ≤ n →
      sSup (range (normalizedDiscrepancy
        (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) < cE

theorem manuscript_interval_standardization_of_clusters (hcluster : ManuscriptEffectiveClusterStabilityInput)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar) :
    ∃ (Z : StandardizedLaw) (m σ : ℝ), 0 < σ ∧
      Z.measure = standardizedMeasure μ m σ ∧
      ∀ n, appendixNStar ≤ n → sSup (range (normalizedDiscrepancy Z n)) < cE := by
  have hη := appendixEtaStar_bounds
  have hmass := upper_interval_mass_eq μ appendixEtaStar (by linarith [hη.1.2]) hb
  let p := μ.real (Ioi (1 / 2))
  have hpI : p ∈ Icc (2 / 5) (9 / 20) := by
    apply effective_cluster_probability
    simpa only [p, hmass] using hp
  have hp01 := (effective_binomial_parameters p hpI).1
  have hb' : ∀ᵐ x ∂μ, x ∈ Icc (0 - appendixEtaStar) (0 + appendixEtaStar) ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) := by simpa only [zero_sub, zero_add] using hb
  obtain ⟨P, Q, m, d, hd, hdb, hP, hQ, hrep⟩ :=
    bounded_two_cluster_affine_representation μ 0 1 appendixEtaStar hη.1.1.le
      (by linarith [hη.1.2]) hb' (by simpa [p] using hp01)
  have hdhalf : 1 / 2 ≤ d := by norm_num at hdb; linarith [hdb.1, hη.1.2]
  have hnoise : 2 * appendixEtaStar / d ≤ Real.exp (-appendixA) := by
    calc
      2 * appendixEtaStar / d ≤ 4 * appendixEtaStar := by
        apply (div_le_iff₀ hd).mpr
        nlinarith [hη.1.1]
      _ ≤ _ := hη.2.2
  have hPb := hP.mono (fun _ hx => hx.trans hnoise)
  have hQb := hQ.mono (fun _ hx => hx.trans hnoise)
  let Z := standardizedTwoClusterLaw P Q p hp01
  let σ := Real.sqrt (clusterVariance P Q p)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp01)
  refine ⟨Z, m + d * p, d * σ, mul_pos hd hσ, ?_, ?_⟩
  · change (standardizedTwoClusterLaw P Q p hp01).measure = _
    rw [standardizedTwoClusterLaw_measure]
    change standardizedMeasure (twoClusterMeasure P Q p) p σ = _
    have hrep' : standardizedMeasure μ m d = twoClusterMeasure P Q p := by simpa [p] using hrep
    rw [← hrep']
    unfold standardizedMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    change ((x - m) / d - p) / σ = (x - (m + d * p)) / (d * σ)
    field_simp [hd.ne', hσ.ne']
    <;> ring
  · intro n hn
    exact hcluster P Q p hpI hPb hQb n hn

theorem manuscript_interval_stability_of_clusters (hcluster : ManuscriptEffectiveClusterStabilityInput)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar ∨
      |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)| < appendixEtaStar)
    (n : ℕ) (hn : appendixNStar ≤ n) : rawNormalizedConstant μ n < cE := by
  have hn1 : 1 ≤ n := by have h := (appendix_sample_size_bounds n hn).1; omega
  rcases hp with hp | hp
  · obtain ⟨Z, m, σ, hσ, hmap, hbound⟩ := manuscript_interval_standardization_of_clusters hcluster μ hb hp
    rw [rawNormalizedConstant_eq μ Z m σ hσ hmap n hn1]
    exact hbound n hn
  · let ν := μ.map (fun x => 1 - x)
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
    have hbν := reflected_intervals_support μ appendixEtaStar hb
    have hpν : |ν.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar := by
      rw [show ν = μ.map (fun x => 1 - x) from rfl,
        reflected_upper_interval_mass μ appendixEtaStar (by linarith [appendixEtaStar_bounds.1.2]) hb]
      have he : 1 - μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE =
          -(μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)) := by ring
      rw [he, abs_neg]
      exact hp
    obtain ⟨Z, m, σ, hσ, hmap, hbound⟩ := manuscript_interval_standardization_of_clusters hcluster ν hbν hpν
    have hmap' : (reflectedLaw Z).measure = standardizedMeasure μ (1 - m) σ := by
      change Z.measure.map (fun x => -x) = _
      rw [hmap]
      unfold standardizedMeasure
      change ((μ.map (fun x => 1 - x)).map (fun x => (x - m) / σ)).map (fun x => -x) = _
      rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      dsimp only [Function.comp_def]
      ring
    rw [rawNormalizedConstant_eq μ (reflectedLaw Z) (1 - m) σ hσ hmap' n hn1,
      normalizedDiscrepancy_sup_reflected Z n hn1]
    exact hbound n hn

theorem manuscript_interval_stability_support_of_clusters (hcluster : ManuscriptEffectiveClusterStabilityInput)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : μ.support ⊆ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar ∨
      |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)| < appendixEtaStar)
    (n : ℕ) (hn : appendixNStar ≤ n) : rawNormalizedConstant μ n < cE :=
  manuscript_interval_stability_of_clusters hcluster μ (by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hb hx) hp n hn

theorem manuscript_effective_intervals_of_clusters
    (hcluster : ManuscriptEffectiveClusterStabilityInput) : ManuscriptEffectiveIntervalStabilityInput := by
  intro μ hprob hb hp n hn
  letI : IsProbabilityMeasure μ := hprob
  exact manuscript_interval_stability_support_of_clusters hcluster μ hb hp n hn

end BerryEsseen
