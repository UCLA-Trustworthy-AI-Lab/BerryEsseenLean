import BerryEsseen.ManuscriptMain
import BerryEsseen.ManuscriptSmoothingInstance
import BerryEsseen.ManuscriptSharpness
import BerryEsseen.ManuscriptExplicitTheorem

/-! Endpoints whose smoothing input is discharged by the manuscript's own
sinc-fourth-power proof. Only the listed classical published results remain. -/
noncomputable section
namespace BerryEsseen

theorem strict_main_theorem
    (H : ClassicalBerryEsseenBounds) (A : PublishedEsseenFixedLawAsymptotic)
    (E : PublishedEsseenMoment)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (W : PublishedWassersteinThreeTopology) : MainClaim :=
  manuscript_main_theorem H A W manuscriptSignedSmoothing E B I

theorem strict_explicit_theorem
    (H : ClassicalBerryEsseenBounds) (E : PublishedEsseenMoment)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (U : PublishedNonuniformBound) (K : PublishedWassersteinDuality) : ExplicitClaim :=
  manuscript_explicit_theorem H E B I U K

/-- The manuscript's stated optimality argument, using the classical
fixed-law asymptotic formula explicitly cited in the manuscript. -/
theorem strict_sharpness (A : PublishedEsseenFixedLawAsymptotic) :
    ManuscriptSharpnessClaim := original_manuscript_sharpness A

end BerryEsseen
