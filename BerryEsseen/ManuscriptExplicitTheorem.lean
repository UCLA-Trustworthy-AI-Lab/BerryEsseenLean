import BerryEsseen.ManuscriptEffectiveIntervals
import BerryEsseen.ManuscriptEffectiveClusters

/-! The original explicit threshold. Smoothing, original-constant local mass,
small-variance clipping, large-variance envelopes, and confinement are all
supplied by actual proofs. No manuscript lemma is an external premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_effective_intervals (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) (U : PublishedNonuniformBound) :
    ManuscriptEffectiveIntervalStabilityInput :=
  manuscript_effective_intervals_of_clusters (manuscript_effective_cluster_stability B I U)

theorem manuscript_effective_interval_stability_support (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : μ.support ⊆ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar ∨
      |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)| < appendixEtaStar)
    (n : ℕ) (hn : appendixNStar ≤ n) : rawNormalizedConstant μ n < cE :=
  manuscript_effective_intervals B I U μ inferInstance hb hp n hn

theorem manuscript_explicit_theorem (H : ClassicalBerryEsseenBounds)
    (E : PublishedEsseenMoment) (B : PublishedBernoulliBound)
    (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (K : PublishedWassersteinDuality) : ExplicitClaim :=
  manuscript_explicit_claim_of_interval_stability H E K U (manuscript_effective_intervals B I U)

end BerryEsseen
