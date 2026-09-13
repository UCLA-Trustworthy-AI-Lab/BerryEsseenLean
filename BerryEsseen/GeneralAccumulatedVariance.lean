import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.GeneralTwoClusterLocalMass
import BerryEsseen.GeneralClusterJitter
import BerryEsseen.GeneralJitterGap
import BerryEsseen.RepresentedVariance

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The limiting Bernoulli envelope, expressed in the manuscript's raw parameters. -/
def clusterEnvelopeConstant (p : ℝ) : ℝ :=
  phi0 * (3 + |1 - 2 * p|) / (6 * Real.sqrt (p * (1 - p)))

theorem clusterEnvelopeConstant_eq (p : ℝ) (hp : p ∈ Ioo 0 1) :
    clusterEnvelopeConstant p =
      (1 / Real.sqrt (p * (1 - p)) / 2 +
        |(1 - 2 * p) / Real.sqrt (p * (1 - p))| / 6) * phi0 := by
  have hs : 0 < Real.sqrt (p * (1 - p)) :=
    Real.sqrt_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  rw [abs_div, abs_of_pos hs]
  unfold clusterEnvelopeConstant
  field_simp
  ring

theorem general_cluster_strict_pointwise_cdf_gap
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (Lstar : ℝ) (hLstar : 0 < Lstar)
    (hL : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) :
    ∃ δ > 0, ∀ᶠ j in atTop, ∀ z : ℝ,
      Real.sqrt (n j : ℝ) *
        |normalizedSumCDF (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j) z - normalCDF z| ≤
        (1 / Real.sqrt (p₀ * (1 - p₀)) / 2 +
          |(1 - 2 * p₀) / Real.sqrt (p₀ * (1 - p₀))| / 6) * phi0 - δ := by
  let σ : ℕ → ℝ := fun j => Real.sqrt (clusterVariance (P j) (Q j) (p j))
  let t : ℕ → ℝ → ℝ := fun j z => (n j : ℝ) * p j + σ j * Real.sqrt (n j : ℝ) * z
  let F : ℕ → ℝ → ℝ := fun j z => Real.sqrt (n j : ℝ) *
    (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (t j z) - normalCDF z)
  let J : ℝ → ℕ → ℝ → ℝ := fun b j z => Real.sqrt (n j : ℝ) *
    (cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j) ∗ uniformJitter 1)
      (t j z + b / 2) - normalCDF z)
  have hσ : ∀ j, 0 < σ j := fun j => Real.sqrt_pos.mpr (clusterVariance_pos _ _ _ (hp j))
  have hσlim := (clusterVariance_tendsto_general P Q p p₀ hplim
    (averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ)).sqrt
  obtain ⟨sigmaBound, hsigmaBound⟩ := hσlim.bddAbove_range
  have hsigmaBoundj : ∀ j, σ j ≤ sigmaBound := fun j => hsigmaBound (Set.mem_range_self j)
  have hsigmaBoundpos : 0 < sigmaBound := (hσ 0).trans_le (hsigmaBoundj 0)
  have hK : IsCompact (insert p₀ (Set.range p)) := hplim.isCompact_insert_range
  have hKI : insert p₀ (Set.range p) ⊆ Ioo 0 1 := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨j, rfl⟩
    · exact hp₀
    · exact hp j
  have horder : ∀ᶠ j in atTop, ∀ z, J (-1) j z ≤ F j z ∧ F j z ≤ J 1 j z := by
    apply Filter.Eventually.of_forall
    intro j z
    letI := twoClusterMeasure_probability (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩
    have ho := spanJitter_cdf_sandwich (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j))
      1 (by norm_num) (t j z)
    simp only [spanJitter, if_pos (by norm_num : (0 : ℝ) < 1)] at ho
    dsimp only [J, F]
    have he : t j z + (-1 : ℝ) / 2 = t j z - 1 / 2 := by ring
    rw [he]
    exact ⟨mul_le_mul_of_nonneg_left (sub_le_sub_right ho.1 _) (Real.sqrt_nonneg _),
      mul_le_mul_of_nonneg_left (sub_le_sub_right ho.2 _) (Real.sqrt_nonneg _)⟩
  have hgap : ∀ R ≥ 0, ∃ D > 0, ∀ᶠ j in atTop, ∀ z, |z| ≤ R →
      J (-1) j z + D ≤ F j z ∧ F j z ≤ J 1 j z - D := by
    intro R hR
    obtain ⟨c, hc, he⟩ := compact_twoCluster_local_jitter_gaps W S I _ hK hKI Lstar (R * sigmaBound)
      hLstar (mul_nonneg hR hsigmaBoundpos.le) P Q p ε (fun j => Set.mem_insert_of_mem _ (Set.mem_range_self j))
      hεlim hP hQ n hn hL
    refine ⟨c, hc, ?_⟩
    filter_upwards [he, hn.eventually (eventually_ge_atTop 1)] with j hj hnj
    intro z hz
    have hr : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n j by omega))
    have ht : |t j z - (n j : ℝ) * p j| ≤ R * sigmaBound * Real.sqrt (n j : ℝ) := by
      dsimp only [t]
      rw [add_sub_cancel_left, abs_mul, abs_mul, abs_of_pos (hσ j), abs_of_pos hr]
      calc
        σ j * Real.sqrt (n j : ℝ) * |z| ≤ sigmaBound * Real.sqrt (n j : ℝ) * R :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hsigmaBoundj j) hr.le) hz (abs_nonneg _) (by positivity)
        _ = R * sigmaBound * Real.sqrt (n j : ℝ) := by ring
    have hg := hj (t j z) ht
    have hg1 := (div_le_iff₀ hr).mp hg.1
    have hg2 := (div_le_iff₀ hr).mp hg.2
    dsimp only [F, J]
    have he : t j z + (-1 : ℝ) / 2 = t j z - 1 / 2 := by ring
    rw [he]
    constructor <;> nlinarith only [hg1, hg2]
  have hu := general_cluster_shifted_jitter_envelopes W S P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ n hn 1
  have hl := general_cluster_shifted_jitter_envelopes W S P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ n hn (-1)
  have hroot : 0 < Real.sqrt (p₀ * (1 - p₀)) := Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))
  have hh : 0 < 1 / Real.sqrt (p₀ * (1 - p₀)) := one_div_pos.mpr hroot
  obtain ⟨δ, hδ, he⟩ := strict_gap_of_jitter_envelopes F (J 1) (J (-1))
    (1 / Real.sqrt (p₀ * (1 - p₀))) ((1 - 2 * p₀) / Real.sqrt (p₀ * (1 - p₀))) hh
    hu (by simpa only [J, t, σ, neg_div] using hl) horder hgap
  refine ⟨δ, hδ, he.mono ?_⟩
  intro j hj z
  have ht : normalizedSumCDF (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j) z =
      cdf (iidSumLaw (twoClusterMeasure (P j) (Q j) (p j)) (n j)) (t j z) := by
    unfold normalizedSumCDF
    rw [standardizedTwoCluster_sum_cdf]
    congr 1
    dsimp only [t, σ]
    ring
  rw [ht]
  simpa only [F, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (n j : ℝ))] using hj z

theorem general_cluster_strict_scaled_cdf_gap
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (Lstar : ℝ) (hLstar : 0 < Lstar)
    (hL : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) :
    ∃ δ > 0, ∀ᶠ j in atTop,
      scaledSumCDFSup (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j) ≤
        (1 / Real.sqrt (p₀ * (1 - p₀)) / 2 +
          |(1 - 2 * p₀) / Real.sqrt (p₀ * (1 - p₀))| / 6) * phi0 - δ := by
  obtain ⟨δ, hδ, he⟩ := general_cluster_strict_pointwise_cdf_gap W S I P Q p ε hp p₀ hp₀
    hplim hε hεlim hP hQ n hn Lstar hLstar hL
  refine ⟨δ, hδ, he.mono ?_⟩
  intro j hj
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨z, rfl⟩
  exact hj z


/-- The actual raw-sum Kolmogorov error with its true cluster mean and variance.
It is defined without imposing conditions on the finitely many initial parameters. -/
def rawTwoClusterScaledCDFSup (P Q : CenteredFourthLaw) (p : ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (fun z : ℝ => Real.sqrt (n : ℝ) *
    |cdf (iidSumLaw (twoClusterMeasure P Q p) n)
      ((n : ℝ) * p + Real.sqrt (clusterVariance P Q p) * Real.sqrt (n : ℝ) * z) - normalCDF z|))

theorem rawTwoClusterScaledCDFSup_eq (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) :
    rawTwoClusterScaledCDFSup P Q p n = scaledSumCDFSup (standardizedTwoClusterLaw P Q p hp) n := by
  unfold rawTwoClusterScaledCDFSup scaledSumCDFSup normalizedSumCDF
  congr 2
  funext z
  rw [standardizedTwoCluster_sum_cdf]
  have he : Real.sqrt (clusterVariance P Q p) * (Real.sqrt (n : ℝ) * z) + (n : ℝ) * p =
      (n : ℝ) * p + Real.sqrt (clusterVariance P Q p) * Real.sqrt (n : ℝ) * z := by ring
  rw [he]

/-- Full parameter range: convergence into the open unit interval is sufficient;
no global compact-set or initial-segment hypothesis is imposed. -/
theorem general_cluster_strict_raw_cdf_gap
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (Lstar : ℝ) (hLstar : 0 < Lstar)
    (hL : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) :
    ∃ δ > 0, ∀ᶠ j in atTop, rawTwoClusterScaledCDFSup (P j) (Q j) (p j) (n j) ≤
      clusterEnvelopeConstant p₀ - δ := by
  let q : ℕ → ℝ := fun j => if p j ∈ Ioo 0 1 then p j else p₀
  have hq : ∀ j, q j ∈ Ioo 0 1 := by
    intro j
    dsimp only [q]
    split_ifs with hj
    · exact hj
    · exact hp₀
  have heq : q =ᶠ[atTop] p := by
    filter_upwards [hplim.eventually (isOpen_Ioo.mem_nhds hp₀)] with j hj
    exact if_pos hj
  have hqlim : Tendsto q atTop (𝓝 p₀) := hplim.congr' heq.symm
  have hLq : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (q j) (n j) := by
    filter_upwards [hL, heq] with j hj he
    simpa only [he] using hj
  have hε : ∀ j, 0 ≤ ε j := by
    intro j
    obtain ⟨x, hx⟩ := (hP j).exists
    exact (abs_nonneg x).trans hx
  obtain ⟨δ, hδ, he⟩ := general_cluster_strict_scaled_cdf_gap W S I P Q q ε hq p₀ hp₀
    hqlim hε hεlim hP hQ n hn Lstar hLstar hLq
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [he, heq] with j hj he
  rw [← rawTwoClusterScaledCDFSup_eq, he, ← clusterEnvelopeConstant_eq p₀ hp₀] at hj
  exact hj

/-- The macroscopic strict gap in `lem:accumulated-cluster-variance`, formulated
for the actual supremum and an eventual positive accumulated-variance bound. -/
theorem general_cluster_strict_raw_cdf_limsup
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (Lstar : ℝ) (hLstar : 0 < Lstar)
    (hL : ∀ᶠ j in atTop, Lstar ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) :
    ∃ δ > 0, atTop.limsup (fun j => rawTwoClusterScaledCDFSup (P j) (Q j) (p j) (n j)) ≤
      clusterEnvelopeConstant p₀ - δ := by
  obtain ⟨δ, hδ, he⟩ := general_cluster_strict_raw_cdf_gap W S I P Q p ε p₀ hp₀ hplim hεlim hP hQ n hn
    Lstar hLstar hL
  refine ⟨δ, hδ, limsup_le_of_le ?_ he⟩
  apply isCoboundedUnder_le_of_eventually_le atTop (x := 0)
  filter_upwards [hplim.eventually (isOpen_Ioo.mem_nhds hp₀)] with j hj
  rw [rawTwoClusterScaledCDFSup_eq _ _ _ hj]
  exact scaledSumCDFSup_nonneg _ _

/-- A real-valued liminf corollary. The extended-real theorem below also covers divergence to infinity. -/
theorem general_cluster_macroscopic_gap_of_real_liminf
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hL : 0 < atTop.liminf (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j))) :
    ∃ δ > 0, atTop.limsup (fun j => rawTwoClusterScaledCDFSup (P j) (Q j) (p j) (n j)) ≤
      phi0 * (3 + |1 - 2 * p₀|) / (6 * Real.sqrt (p₀ * (1 - p₀))) - δ := by
  let L := atTop.liminf (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j))
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) := by
    apply isBoundedUnder_of_eventually_ge (a := 0)
    filter_upwards [hplim.eventually (isOpen_Ioo.mem_nhds hp₀)] with j hj
    exact accumulatedNoiseVariance_nonneg _ _ _ ⟨hj.1.le, hj.2.le⟩ _
  have he : ∀ᶠ j in atTop, L / 2 ≤ accumulatedNoiseVariance (P j) (Q j) (p j) (n j) :=
    (eventually_lt_of_lt_liminf (show L / 2 < L by dsimp [L]; linarith) hb).mono fun _ hj => hj.le
  exact general_cluster_strict_raw_cdf_limsup W S I P Q p ε p₀ hp₀ hplim hεlim hP hQ n hn
    (L / 2) (by dsimp [L]; linarith) he


/-- A positive extended-real liminf is exactly a positive eventual real lower
bound. In particular, this equivalence includes liminf equal to positive infinity. -/
theorem positive_ereal_liminf_iff_eventual_positive_lower (u : ℕ → ℝ) :
    (0 : EReal) < atTop.liminf (fun j => (u j : EReal)) ↔
      ∃ L > 0, ∀ᶠ j in atTop, L ≤ u j := by
  constructor
  · intro h
    obtain ⟨L, hL, hbelow⟩ := EReal.exists_between_coe_real h
    refine ⟨L, EReal.coe_pos.mp hL, ?_⟩
    filter_upwards [eventually_lt_of_lt_liminf hbelow] with j hj
    exact (EReal.coe_lt_coe_iff.mp hj).le
  · rintro ⟨L, hL, he⟩
    apply (EReal.coe_pos.mpr hL).trans_le
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [he] with j hj
    exact EReal.coe_le_coe_iff.mpr hj

/-- The complete macroscopic-gap implication in the manuscript, with liminf in
extended reals so that unbounded accumulated variance is included. -/
theorem general_cluster_macroscopic_gap
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hL : (0 : EReal) < atTop.liminf
      (fun j => (accumulatedNoiseVariance (P j) (Q j) (p j) (n j) : EReal))) :
    ∃ δ > 0, atTop.limsup (fun j => rawTwoClusterScaledCDFSup (P j) (Q j) (p j) (n j)) ≤
      phi0 * (3 + |1 - 2 * p₀|) / (6 * Real.sqrt (p₀ * (1 - p₀))) - δ := by
  obtain ⟨L, hLpos, he⟩ := (positive_ereal_liminf_iff_eventual_positive_lower _).mp hL
  exact general_cluster_strict_raw_cdf_limsup W S I P Q p ε p₀ hp₀ hplim hεlim hP hQ n hn L hLpos he

end BerryEsseen
