import BerryEsseen.ManuscriptClusters
import BerryEsseen.SelectedClusters

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def manuscriptPrincipalAffineLaw (P : StandardizedLaw) : Measure ℝ :=
  P.measure.map (fun x => pE + sigmaE * x)

instance manuscriptPrincipalAffineLaw_probability (P : StandardizedLaw) :
    IsProbabilityMeasure (manuscriptPrincipalAffineLaw P) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem manuscript_principal_affine_standardization (P : StandardizedLaw) :
    P.measure = standardizedMeasure (manuscriptPrincipalAffineLaw P) pE sigmaE := by
  unfold manuscriptPrincipalAffineLaw standardizedMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => ((fun x => (x - pE) / sigmaE) ∘ (fun x => pE + sigmaE * x)) x) = id := by
    funext x
    dsimp only [Function.comp_apply, id_eq]
    field_simp [sigmaE_pos.ne']
    <;> ring
  change P.measure = P.measure.map (fun x : ℝ => ((fun x => (x - pE) / sigmaE) ∘ (fun x => pE + sigmaE * x)) x)
  rw [he, Measure.map_id]

theorem manuscript_principal_affine_support (P : StandardizedLaw) (η : ℝ)
    (hsupp : P.measure.support ⊆
      Ioo (-aE - η / sigmaE) (-aE + η / sigmaE) ∪
        Ioo (bE - η / sigmaE) (bE + η / sigmaE)) :
    (manuscriptPrincipalAffineLaw P).support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) := by
  apply Measure.support_subset_of_isClosed (isClosed_Icc.union isClosed_Icc)
  apply (ae_map_iff (by fun_prop) (measurableSet_Icc.union measurableSet_Icc)).2
  have ha : sigmaE * aE = pE := by unfold aE; field_simp [sigmaE_pos.ne' ]
  have hb : sigmaE * bE = 1 - pE := by unfold bE qE; field_simp [sigmaE_pos.ne' ]
  have hη : sigmaE * (η / sigmaE) = η := by field_simp [sigmaE_pos.ne' ]
  filter_upwards [P.measure.support_mem_ae] with x hx
  rcases hsupp hx with hx | hx
  · left
    have hlo := mul_lt_mul_of_pos_left hx.1 sigmaE_pos
    have hhi := mul_lt_mul_of_pos_left hx.2 sigmaE_pos
    constructor <;> nlinarith [ha, hη]
  · right
    have hlo := mul_lt_mul_of_pos_left hx.1 sigmaE_pos
    have hhi := mul_lt_mul_of_pos_left hx.2 sigmaE_pos
    constructor <;> nlinarith [hb, hη]

theorem manuscript_principal_affine_halfline_mass (P : StandardizedLaw) :
    (manuscriptPrincipalAffineLaw P).real (Ioi (1 / 2)) =
      P.measure.real (Ioi ((1 / 2 - pE) / sigmaE)) := by
  unfold manuscriptPrincipalAffineLaw Measure.real
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 2
  ext x
  simp only [mem_preimage, mem_Ioi]
  rw [div_lt_iff₀ sigmaE_pos]
  constructor <;> intro h <;> nlinarith

theorem manuscript_principal_affine_cut :
    (1 / 2 - pE) / sigmaE ∈ Ioo (-aE) bE := by
  have ha : sigmaE * aE = pE := by unfold aE; field_simp [sigmaE_pos.ne' ]
  have hb : sigmaE * bE = 1 - pE := by unfold bE qE; field_simp [sigmaE_pos.ne' ]
  constructor
  · apply (lt_div_iff₀ sigmaE_pos).2
    nlinarith [ha]
  · apply (div_lt_iff₀ sigmaE_pos).2
    nlinarith [hb]

/-- The final manuscript argument, after Lemmas 5.1--5.3: apply the fixed
affine map pE + sigmaE*x, use its eventual full support confinement and weak
upper-cluster mass convergence, and invoke Proposition 3.1. -/
theorem manuscript_selected_extremizers_impossible
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (X : SelectedExtremizers) : False := by
  obtain ⟨η, hη, N, hlocal⟩ := manuscript_two_interval_cluster_stability W S B I
  have hδ : 0 < η / sigmaE := div_pos hη.1 sigmaE_pos
  have hmass := weak_esseen_halfline_mass_tendsto X.P X.weak
    ((1 / 2 - pE) / sigmaE) manuscript_principal_affine_cut
  have hclose := Metric.tendsto_nhds.1 hmass η hη.1
  obtain ⟨j, hsupp, hpclose, hn⟩ :=
    ((X.confined H W S (η / sigmaE) hδ).and
      (hclose.and (X.n_tendsto.eventually (eventually_ge_atTop N)))).exists
  let μ := manuscriptPrincipalAffineLaw (X.P j)
  have hsuppμ : μ.support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) :=
    manuscript_principal_affine_support (X.P j) η hsupp
  have hbμ : ∀ᵐ x ∂μ, x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η) := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hsuppμ hx
  have hpμ : |μ.real (Icc (1 - η) (1 + η)) - pE| < η := by
    rw [← upper_interval_mass_eq μ η (hη.2.trans (by norm_num)) hbμ,
      manuscript_principal_affine_halfline_mass]
    simpa only [Real.dist_eq] using hpclose
  have hbound := hlocal μ (by infer_instance) hsuppμ (Or.inl hpμ) (X.n j + 1) (by omega)
  have hn1 : 1 ≤ X.n j + 1 := by omega
  rw [rawNormalizedConstant_eq μ (X.P j) pE sigmaE sigmaE_pos
    (manuscript_principal_affine_standardization (X.P j)) (X.n j + 1) hn1] at hbound
  have hpoint := le_csSup (normalizedDiscrepancy_range_bddAbove (X.P j) (X.n j + 1) hn1)
    (Set.mem_range_self (X.t j / Real.sqrt ((X.n j + 1 : ℕ) : ℝ)))
  have hratio : signedRatio (X.P j) (X.n j) (X.t j) ≤ cE := by
    apply (le_abs_self _).trans
    rw [abs_signedRatio_eq_normalized]
    simpa only [Nat.cast_add, Nat.cast_one] using hpoint.trans hbound
  rw [X.attain j] at hratio
  exact (not_le_of_gt (X.violate j)) hratio

/-- The existence assertion in the original manuscript, using its original
Proposition 3.1 route, the full `C_n → cE` limit and direct difference
selection, and the original Lemma 3.3 proof. The smoothing lemma is explicit here; the other interfaces are the published
classical results, including the W₃ topology characterization used by Lemma 2.2. -/
theorem manuscript_main_theorem (H : ClassicalBerryEsseenBounds)
    (A : PublishedEsseenFixedLawAsymptotic) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (E : PublishedEsseenMoment) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) : MainClaim := by
  classical
  by_contra hmain
  obtain ⟨X⟩ := manuscript_exists_selectedExtremizers_of_not_main H A W S E hmain
  exact manuscript_selected_extremizers_impossible H W S B I X

end BerryEsseen
