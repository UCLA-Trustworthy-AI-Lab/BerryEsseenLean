import BerryEsseen.Resonances

/-! Internal interface for the manuscript's signed smoothing lemma.

The historical structure name is retained to keep downstream theorem signatures
stable.  Its concrete instance is now proved from manuscript Lemma 2.1 in
`ManuscriptSmoothingInstance`, rather than supplied as a literature premise.
Both actual first moments required in the manuscript are explicit.  The cutoff
integral retains its integrability condition because a nonintegrable real
Bochner integral in Lean is zero.  Constants are the manuscript's 1/4 and 24.
-/
noncomputable section
open MeasureTheory Set
namespace BerryEsseen

def densityFourier (g : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, (g x : ℂ) * realPhase t x

structure PublishedSignedSmoothing : Prop where
  bound : ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → Integrable (fun x : ℝ => x) μ →
    ∀ (g : ℝ → ℝ), Integrable g → Integrable (fun x : ℝ => x * g x) → (∫ x, g x) = 1 →
    ∀ (M L : ℝ), 0 < M → 0 < L → (∀ x, |g x| ≤ M) →
    IntegrableOn (fun t => ‖charFun μ t - densityFourier g t‖ / |t|) (Icc (-L) L) →
    ∀ x : ℝ, |(μ (Iic x)).toReal - ∫ y in Iic x, g y| ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - densityFourier g t‖ / |t|) +
        (24) * M / L

end BerryEsseen
