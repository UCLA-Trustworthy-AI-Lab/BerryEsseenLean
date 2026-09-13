import BerryEsseen.EffectiveConfinement

noncomputable section
namespace BerryEsseen

/-- The manuscript's explicit threshold, with only enumerated published inputs.
All confinement and finite-selection conclusions are proved in the project. -/
theorem explicit_theorem (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (U : PublishedNonuniformBound) (K : PublishedWassersteinDuality) : ExplicitClaim :=
  explicit_claim_of_effective_confinement H S B I U (effective_confinement H S E K U)

end BerryEsseen
