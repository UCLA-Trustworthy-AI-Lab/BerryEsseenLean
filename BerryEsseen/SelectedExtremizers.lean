import BerryEsseen.ClusterConfinement

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The selected sequence constructed from failure of the main theorem.
The sample size in the extremum is n + 1; n is the preceding row size. -/
structure SelectedExtremizers where
  P : ℕ → StandardizedLaw
  n : ℕ → ℕ
  t : ℕ → ℝ
  n_tendsto : Tendsto n atTop atTop
  n_ge_two : ∀ j, 2 ≤ n j
  attain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1)
  violate : ∀ j, cE < extremalConstant (n j + 1)
  drop : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0)
  weak : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure)
  threshold : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0)
  support : ∀ j, (P j).measure.support ⊆ Icc (-10) 10

/-- Convert an already identified maximizing sequence to the predecessor
indexing used by the support-confinement argument. -/
theorem exists_selectedExtremizers_of_identified
    (hidentified : ∃ (n : ℕ → ℕ) (P : ℕ → StandardizedLaw) (t : ℕ → ℝ), StrictMono n ∧
      (∀ j, 2 ≤ n j ∧ signedRatio (P j) (n j - 1) (t j) = extremalConstant (n j) ∧
        cE < extremalConstant (n j) ∧ 1 ≤ thirdMoment (P j) ∧ thirdMoment (P j) < momentCutoff ∧
        (P j).measure.support ⊆ Ioo (-10) 10) ∧
      Tendsto (fun j => scaledDrop extremalConstant (n j)) atTop (𝓝 0) ∧
      Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) ∧
      Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 kappaE) ∧
      Tendsto (fun j => t j / Real.sqrt (n j : ℝ)) atTop (𝓝 0)) :
    Nonempty SelectedExtremizers := by
  obtain ⟨n, P, t, hn, hprops, hd, hw, _, _, hz⟩ := hidentified
  let m : ℕ → ℕ := fun j => n (j + 1) - 1
  have hn3 (j : ℕ) : 3 ≤ n (j + 1) := by
    have hlt := hn (Nat.lt_succ_self j)
    change n j < n (j + 1) at hlt
    have hge := (hprops j).1
    omega
  have hm2 (j : ℕ) : 2 ≤ m j := by dsimp [m]; have := hn3 j; omega
  have hne (j : ℕ) : m j + 1 = n (j + 1) := by dsimp [m]; have := hn3 j; omega
  have hnc (j : ℕ) : (m j + 1 : ℝ) = (n (j + 1) : ℝ) := by exact_mod_cast hne j
  have hmmono : StrictMono m := by
    intro i j hij
    have hlt := hn (show i + 1 < j + 1 by omega)
    have hi := hn3 i
    dsimp [m]
    omega
  refine ⟨{
    P := fun j => P (j + 1)
    n := m
    t := fun j => t (j + 1)
    n_tendsto := hmmono.tendsto_atTop
    n_ge_two := hm2
    attain := ?_
    violate := ?_
    drop := ?_
    weak := hw.comp (tendsto_add_atTop_nat 1)
    threshold := ?_
    support := ?_
  }⟩
  · intro j
    rw [hne]
    exact (hprops (j + 1)).2.1
  · intro j
    rw [hne]
    exact (hprops (j + 1)).2.2.1
  · simpa only [hne, Function.comp_apply] using hd.comp (tendsto_add_atTop_nat 1)
  · simpa only [hnc, Function.comp_apply] using hz.comp (tendsto_add_atTop_nat 1)
  · intro j x hx
    have hi := (hprops (j + 1)).2.2.2.2.2 hx
    exact ⟨hi.1.le, hi.2.le⟩

/-- Historical extraction interface, retained for existing consumers. -/
theorem exists_selectedExtremizers_of_not_main
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (hmain : ¬ MainClaim) : Nonempty SelectedExtremizers :=
  exists_selectedExtremizers_of_identified
    (identified_extremizing_sequence_of_not_main H W S E hmain)

theorem manuscript_exists_selectedExtremizers_of_not_main
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (hmain : ¬ MainClaim) : Nonempty SelectedExtremizers :=
  exists_selectedExtremizers_of_identified
    (manuscript_identified_extremizing_sequence_of_not_main H A W S E hmain)

theorem SelectedExtremizers.confined (X : SelectedExtremizers)
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j in atTop, (X.P j).measure.support ⊆
      Ioo (-aE - η) (-aE + η) ∪ Ioo (bE - η) (bE + η) :=
  extremizer_uniform_two_cluster_confinement H W S X.P X.n X.t X.n_tendsto X.n_ge_two X.attain
    X.violate X.drop X.weak X.threshold X.support η hη

end BerryEsseen
