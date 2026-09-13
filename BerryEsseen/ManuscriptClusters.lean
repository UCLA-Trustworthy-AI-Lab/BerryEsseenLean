import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.GeneralAccumulatedVarianceCorollary
import BerryEsseen.ClusterRepresentation
import BerryEsseen.EffectiveIntervals
import BerryEsseen.ManuscriptSmallVarianceOriginalParameters

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Exact qualitative small-variance statement needed in the manuscript's
Proposition 3.1 proof. This internal interface is supplied by the proved
manuscript_small_cluster_variance_original_parameters below; it is not a published input. -/
def ManuscriptSmallVarianceStatement : Prop :=
  ∃ (a b ε lam : ℝ) (N : ℕ),
    a < b ∧ IsCompact (Icc a b) ∧ Icc a b ⊆ Ioo (0 : ℝ) (1 / 2) ∧
    pE ∈ Ioo a b ∧ 0 < ε ∧ 0 < lam ∧
    ∀ (P Q : CenteredFourthLaw) (p : ℝ), p ∈ Icc a b →
      (∀ᵐ x ∂P.measure, |x| ≤ ε) → (∀ᵐ x ∂Q.measure, |x| ≤ ε) →
      ∀ n, N ≤ n → accumulatedNoiseVariance P Q p n ≤ lam →
        rawNormalizedConstant (twoClusterMeasure P Q p) n ≤ rawNormalizedConstant (bernoulliMeasure p) n ∧
        rawNormalizedConstant (bernoulliMeasure p) n < cE ∧
        (0 < averageNoiseVariance P Q p →
          rawNormalizedConstant (twoClusterMeasure P Q p) n < rawNormalizedConstant (bernoulliMeasure p) n)

/-- Positive affine invariance in the actual conditional-mean representation. -/
theorem manuscript_raw_affine_two_cluster (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (m d : ℝ) (hd : 0 < d)
    (hrep : standardizedMeasure μ m d = twoClusterMeasure P Q p)
    (n : ℕ) (hn : 1 ≤ n) :
    rawNormalizedConstant μ n = rawNormalizedConstant (twoClusterMeasure P Q p) n := by
  let Z := standardizedTwoClusterLaw P Q p hp
  let σ := Real.sqrt (clusterVariance P Q p)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp)
  have hmap : Z.measure = standardizedMeasure μ (m + d * p) (d * σ) := by
    change standardizedMeasure (twoClusterMeasure P Q p) p σ = _
    rw [← hrep]
    unfold standardizedMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    change ((x - m) / d - p) / σ = (x - (m + d * p)) / (d * σ)
    field_simp [hd.ne', hσ.ne']
    <;> ring
  rw [rawNormalizedConstant_eq μ Z (m + d * p) (d * σ) (mul_pos hd hσ) hmap n hn,
    rawNormalizedConstant_twoCluster P Q p hp n hn]

/-- The manuscript's envelope step: a shrinking two-cluster sequence violating
the Esseen bound has ratios converging to cE. The upper bound comes from the
ordinary jitter envelopes, not from a global Berry--Esseen remainder theorem. -/
theorem manuscript_cluster_violations_converge (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hplim : Tendsto p atTop (𝓝 pE))
    (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hR : ∀ j, cE < rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j)) :
    Tendsto (fun j => rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j))
      atTop (𝓝 cE) := by
  let Z := fun j => standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)
  have hpE : pE ∈ Ioo 0 1 := ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩
  have hw := standardizedTwoClusterLaw_tendsto P Q p ε hp pE hpE hplim hε hεlim hP hQ
  have hm := standardizedTwoCluster_third_tendsto P Q p ε hp pE hpE hplim hε hεlim hP hQ
  have hk := standardizedTwoCluster_signed_third_tendsto P Q p ε hp pE hpE hplim hε hεlim hP hQ
  have hU := general_variable_jitter_uniform_expansion W S Z (standardizedBernoulliLaw pE hpE)
    hw hm n hn hE hE_pos.le (standardizedBernoulli_resonance_multiplier_zero pE hpE)
    (fun _ => hE) (fun _ => hE_pos.le) tendsto_const_nhds
  rw [standardizedBernoulli_pE, thirdMoment_esseen] at hm
  rw [standardizedBernoulli_pE, signedThirdMoment_esseen] at hk
  obtain ⟨K, hK⟩ := hm.bddAbove_range
  have hκ : ∀ j, |signedThirdMoment (Z j)| ≤ K :=
    fun j => (signedThirdMoment_abs_le (Z j)).trans (hK (Set.mem_range_self j))
  have henv := general_jitter_uniform_absolute_bound_of_expansion Z n hn hn1 K hκ hE
    hE_pos.le hU kappaE hk
  have hpeak : (hE / 2 + |kappaE| / 6) * phi0 = cE * betaE := by
    rw [abs_of_pos kappaE_pos]
    exact esseen_peak_identity
  have hs : Tendsto (fun j => scaledSumCDFSup (Z j) (n j)) atTop (𝓝 (cE * betaE)) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      have hβ := hm.const_mul cE
      filter_upwards [hβ.eventually (lt_mem_nhds ha)] with j hj
      have hmul := mul_lt_mul_of_pos_left (hR j) (thirdMoment_pos (Z j))
      rw [cluster_scaledSumCDFSup_eq_third_mul_raw (P j) (Q j) (p j) (hp j) (n j) (hn1 j)]
      nlinarith only [hj, hmul]
    · intro b hb
      filter_upwards [henv ((b - cE * betaE) / 2) (by linarith)] with j hj
      have hsle : scaledSumCDFSup (Z j) (n j) ≤ cE * betaE + (b - cE * betaE) / 2 := by
        unfold scaledSumCDFSup
        apply csSup_le (Set.range_nonempty _)
        rintro y ⟨x, rfl⟩
        simpa only [hpeak] using hj x
      linarith
  have hβpos : 0 < betaE := by simpa only [thirdMoment_esseen] using thirdMoment_pos esseenLaw
  have hdiv := hs.div hm hβpos.ne'
  rw [mul_div_cancel_right₀ cE hβpos.ne'] at hdiv
  apply hdiv.congr'
  apply Eventually.of_forall
  intro j
  change scaledSumCDFSup (Z j) (n j) / thirdMoment (Z j) = _
  rw [cluster_scaledSumCDFSup_eq_third_mul_raw (P j) (Q j) (p j) (hp j) (n j) (hn1 j),
    mul_div_cancel_left₀ _ (thirdMoment_pos (Z j)).ne']

/-- Last two steps of Proposition 3.1: the accumulated-variance lemma forces
ns to zero, and the fixed neighborhood in Lemma 3.3 gives the contradiction. -/
theorem manuscript_shrinking_cluster_violations_impossible
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (L : ManuscriptSmallVarianceStatement)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hplim : Tendsto p atTop (𝓝 pE))
    (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hR : ∀ j, cE < rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j)) : False := by
  have hRlim := manuscript_cluster_violations_converge W S P Q p ε hp hplim hε hεlim hP hQ n hn hn1 hR
  have hlam := accumulated_cluster_variance_tendsto_zero_of_open_parameters W S I P Q p ε hp pE
    ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩ (Or.inl rfl) hplim hε hεlim hP hQ n hn hRlim
  obtain ⟨a, b, ε₀, lam₀, N, hab, hcompact, hI, hpE, hε₀, hlam₀, hsmall⟩ := L
  obtain ⟨j, hjp, hjε, hjlam, hjn⟩ :=
    ((hplim.eventually (isOpen_Ioo.mem_nhds hpE)).and
      ((hεlim.eventually (gt_mem_nhds hε₀)).and
        ((hlam.eventually (gt_mem_nhds hlam₀)).and (hn.eventually (eventually_ge_atTop N))))).exists
  have hbound := hsmall (P j) (Q j) (p j) ⟨hjp.1.le, hjp.2.le⟩
    ((hP j).mono (fun _ hx => hx.trans hjε.le))
    ((hQ j).mono (fun _ hx => hx.trans hjε.le)) (n j) hjn hjlam.le
  exact (not_lt_of_ge (hbound.1.trans hbound.2.1.le)) (hR j)

/-- Proposition 3.1 at pE, following its original contradiction proof.
The index j+200 is merely the manuscript's deletion of finitely many initial
indices in the neighborhoods 1/j. No appendix stability theorem is used. -/
theorem manuscript_interval_stability_at_pE_of_small_variance
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (L : ManuscriptSmallVarianceStatement) :
    ∃ η ∈ Ioo (0 : ℝ) (1 / 100), ∃ N : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      μ.support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) →
      |μ.real (Icc (1 - η) (1 + η)) - pE| < η →
      ∀ n, N ≤ n → rawNormalizedConstant μ n ≤ cE := by
  classical
  by_contra hlocal
  push_neg at hlocal
  let η : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 200)
  have hηpos : ∀ j, 0 < η j := by intro j; dsimp [η]; positivity
  have hηle : ∀ j, η j ≤ 1 / 200 := by
    intro j
    dsimp only [η]
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 200)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hηsmall : ∀ j, η j ∈ Ioo (0 : ℝ) (1 / 100) :=
    fun j => ⟨hηpos j, (hηle j).trans_lt (by norm_num)⟩
  have hηlim : Tendsto η atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).atTop_add
        (tendsto_const_nhds (x := (200 : ℝ))))
  have hex (j : ℕ) := hlocal (η j) (hηsmall j) (j + 200)
  choose μ hprob hsupp hmass n hn hviolate using hex
  letI (j : ℕ) : IsProbabilityMeasure (μ j) := hprob j
  have hns : Tendsto n atTop atTop := tendsto_atTop_mono
    (fun j => by change j ≤ n j; have := hn j; omega) tendsto_id
  have hn1 : ∀ j, 1 ≤ n j := fun j => by have := hn j; omega
  have hb (j : ℕ) : ∀ᵐ x ∂μ j, x ∈ Icc (-η j) (η j) ∪ Icc (1 - η j) (1 + η j) := by
    filter_upwards [(μ j).support_mem_ae] with x hx
    exact hsupp j hx
  let p := fun j => (μ j).real (Ioi (1 / 2))
  have hpabs (j : ℕ) : |p j - pE| < η j := by
    dsimp only [p]
    rw [upper_interval_mass_eq (μ j) (η j) ((hηle j).trans_lt (by norm_num)) (hb j)]
    exact hmass j
  have hp (j : ℕ) : p j ∈ Ioo 0 1 := by
    have ha := abs_lt.mp (hpabs j)
    have hηj := hηle j
    constructor <;> linarith [pE_bounds.1, pE_bounds.2]
  have hplim : Tendsto p atTop (𝓝 pE) := by
    apply Metric.tendsto_nhds.2
    intro δ hδ
    filter_upwards [hηlim.eventually (gt_mem_nhds hδ)] with j hj
    simpa only [Real.dist_eq] using (hpabs j).trans hj
  have hrepresentation (j : ℕ) := bounded_two_cluster_affine_representation (μ j) 0 1 (η j)
    (hηpos j).le (by have := hηle j; norm_num; linarith)
    (by simpa only [zero_sub, zero_add] using hb j) (by simpa [p] using hp j)
  choose P Q m d hd hdb hP hQ hrep using hrepresentation
  let ε := fun j => 2 * η j / d j
  have hεnonneg : ∀ j, 0 ≤ ε j := fun j => div_nonneg (by have := hηpos j; positivity) (hd j).le
  have hdhalf (j : ℕ) : 1 / 2 ≤ d j := by
    have h := (hdb j).1
    have hh := hηle j
    norm_num at h
    linarith
  have hεbound (j : ℕ) : ε j ≤ 4 * η j := by
    apply (div_le_iff₀ (hd j)).2
    nlinarith [hdhalf j, hηpos j]
  have hεlim : Tendsto ε atTop (𝓝 0) := squeeze_zero hεnonneg hεbound
    (by simpa only [mul_zero] using hηlim.const_mul 4)
  have hR (j : ℕ) : cE < rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j) := by
    rw [← manuscript_raw_affine_two_cluster (μ j) (P j) (Q j) (p j) (hp j)
      (m j) (d j) (hd j) (by simpa [p] using hrep j) (n j) (hn1 j)]
    exact hviolate j
  exact manuscript_shrinking_cluster_violations_impossible W S I L P Q p ε hp hplim hεnonneg hεlim
    hP hQ n hns hn1 hR

/-- A bounded two-interval law with both intervals charged has a genuine
standardization. This is only the conditional-mean affine construction. -/
theorem manuscript_interval_standardized_representation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) (1 / 2))
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η))
    (hp : μ.real (Ioi (1 / 2)) ∈ Ioo 0 1) :
    ∃ (Z : StandardizedLaw) (m σ : ℝ), 0 < σ ∧ Z.measure = standardizedMeasure μ m σ := by
  obtain ⟨P, Q, m, d, hd, hdb, hP, hQ, hrep⟩ := bounded_two_cluster_affine_representation μ 0 1 η
    hη.1.le (by linarith [hη.2]) (by simpa only [zero_sub, zero_add] using hb)
    (by simpa only [zero_add] using hp)
  let p := μ.real (Ioi (1 / 2))
  let σ := Real.sqrt (clusterVariance P Q p)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp)
  refine ⟨standardizedTwoClusterLaw P Q p hp, m + d * p, d * σ, mul_pos hd hσ, ?_⟩
  change standardizedMeasure (twoClusterMeasure P Q p) p σ = _
  have hr : standardizedMeasure μ m d = twoClusterMeasure P Q p := by simpa only [zero_add] using hrep
  rw [← hr]
  unfold standardizedMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  change ((x - m) / d - p) / σ = (x - (m + d * p)) / (d * σ)
  field_simp [hd.ne', hσ.ne']
  <;> ring

theorem manuscript_raw_reflection_of_standardization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hmap : Z.measure = standardizedMeasure μ m σ) (n : ℕ) (hn : 1 ≤ n) :
    rawNormalizedConstant (μ.map (fun x => 1 - x)) n = rawNormalizedConstant μ n := by
  let ν := μ.map (fun x => 1 - x)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hmap' : (reflectedLaw Z).measure = standardizedMeasure ν (1 - m) σ := by
    change Z.measure.map (fun x => -x) = _
    rw [hmap]
    unfold standardizedMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    dsimp only [ν]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    dsimp only [Function.comp_def]
    ring
  rw [rawNormalizedConstant_eq ν (reflectedLaw Z) (1 - m) σ hσ hmap' n hn,
    rawNormalizedConstant_eq μ Z m σ hσ hmap n hn,
    normalizedDiscrepancy_sup_reflected Z n hn]

/-- The full two-parameter Proposition 3.1, obtained from its original pE
contradiction argument followed by X ↦ 1-X. The sole internal obligation L is
the separately implemented original Lemma 3.3, never the appendix or MainClaim. -/
theorem manuscript_two_interval_cluster_stability_of_small_variance
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (L : ManuscriptSmallVarianceStatement) :
    ∃ η ∈ Ioo (0 : ℝ) (1 / 4), ∃ N : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      μ.support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) →
      (|μ.real (Icc (1 - η) (1 + η)) - pE| < η ∨
        |μ.real (Icc (1 - η) (1 + η)) - (1 - pE)| < η) →
      ∀ n, N ≤ n → rawNormalizedConstant μ n ≤ cE := by
  obtain ⟨η, hη, N, hlocal⟩ := manuscript_interval_stability_at_pE_of_small_variance W S I L
  refine ⟨η, ⟨hη.1, hη.2.trans (by norm_num)⟩, max N 1, ?_⟩
  intro μ hprob hsupp hp n hn
  letI := hprob
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hb : ∀ᵐ x ∂μ, x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η) := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hsupp hx
  rcases hp with hp | hp
  · exact hlocal μ hprob hsupp hp n hnN
  · let ν := μ.map (fun x => 1 - x)
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
    have hbν := reflected_intervals_support μ η hb
    have hsuppν : ν.support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) :=
      Measure.support_subset_of_isClosed (isClosed_Icc.union isClosed_Icc) hbν
    have hpν : |ν.real (Icc (1 - η) (1 + η)) - pE| < η := by
      rw [show ν = μ.map (fun x => 1 - x) from rfl,
        reflected_upper_interval_mass μ η (hη.2.trans (by norm_num)) hb]
      have he : 1 - μ.real (Icc (1 - η) (1 + η)) - pE =
        -(μ.real (Icc (1 - η) (1 + η)) - (1 - pE)) := by ring
      rw [he, abs_neg]
      exact hp
    have hp01 : μ.real (Ioi (1 / 2)) ∈ Ioo 0 1 := by
      rw [upper_interval_mass_eq μ η (hη.2.trans (by norm_num)) hb]
      have ha := abs_lt.mp hp
      constructor <;> linarith [hη.2, pE_bounds.1, pE_bounds.2]
    obtain ⟨Z, m, σ, hσ, hmap⟩ := manuscript_interval_standardized_representation μ η
      ⟨hη.1, hη.2.trans (by norm_num)⟩ hb hp01
    rw [← manuscript_raw_reflection_of_standardization μ Z m σ hσ hmap n hn1]
    exact hlocal ν (by infer_instance) hsuppν hpν n hnN

/-- Proposition 3.1 with its original proof fully connected. The original
Lemma 3.3 is proved from W S and B, not assumed and not taken from the appendix. -/
theorem manuscript_two_interval_cluster_stability
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) :
    ∃ η ∈ Ioo (0 : ℝ) (1 / 4), ∃ N : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      μ.support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) →
      (|μ.real (Icc (1 - η) (1 + η)) - pE| < η ∨
        |μ.real (Icc (1 - η) (1 + η)) - (1 - pE)| < η) →
      ∀ n, N ≤ n → rawNormalizedConstant μ n ≤ cE :=
  manuscript_two_interval_cluster_stability_of_small_variance W S I
    (manuscript_small_cluster_variance_original_parameters W S B)

end BerryEsseen
