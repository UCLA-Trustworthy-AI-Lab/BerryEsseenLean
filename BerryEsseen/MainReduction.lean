import BerryEsseen.SelectedExtremizers

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The standardized local stability conclusion sufficient for the qualitative
main theorem. It is proved independently as a corollary in MainTheorem.lean and
is not an assumed published result. -/
def StandardizedTwoClusterStability : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ P : StandardizedLaw,
    P.measure.support ⊆ Ioo (-aE - η) (-aE + η) ∪ Ioo (bE - η) (bE + η) →
    |(P.measure (Ioi 0)).toReal - pE| < η → BoundAt P n

/-- An alternative global reduction from standardized local stability. The final
main theorem uses a direct argument and does not depend on this implication. -/
theorem mainClaim_of_local_two_cluster_stability
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (hlocal : StandardizedTwoClusterStability) : MainClaim := by
  by_contra hmain
  obtain ⟨X⟩ := exists_selectedExtremizers_of_not_main H W S E hmain
  obtain ⟨η, hη, N, hlocal⟩ := hlocal
  have hmass := weak_esseen_upper_cluster_mass_tendsto X.P X.weak
  have hclose := Metric.tendsto_nhds.1 hmass η hη
  have hevent := (X.confined H W S η hη).and (hclose.and (X.n_tendsto.eventually (eventually_ge_atTop N)))
  obtain ⟨j, hsupp, hprob, hn⟩ := hevent.exists
  have hb := hlocal (X.n j + 1) (by omega) (X.P j) hsupp (by simpa only [Real.dist_eq] using hprob)
  have hr : signedRatio (X.P j) (X.n j) (X.t j) ≤ cE := by
    apply (le_abs_self _).trans
    rw [abs_signedRatio_eq_normalized]
    exact (BoundAt_iff_normalized (X.P j) (X.n j + 1) (by omega)).1 hb _
  rw [X.attain j] at hr
  exact (not_le_of_gt (X.violate j)) hr

end BerryEsseen
