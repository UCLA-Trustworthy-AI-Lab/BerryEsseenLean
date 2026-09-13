import BerryEsseen.PublishedWassersteinThreeCore
import BerryEsseen.BoundedMomentLimits

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The standard published Wasserstein convergence characterization, restricted
to probability laws on the real line with finite third moments. No instance is
asserted. The source and version are recorded in the reference directory. -/
structure PublishedWassersteinThreeTopology : Prop where
  tendsto_iff : ∀ (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ),
    (∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μ j : Measure ℝ)) →
    Integrable (fun x : ℝ => |x| ^ 3) (ν : Measure ℝ) →
    (Tendsto (fun j => wassersteinThree (μ j : Measure ℝ) (ν : Measure ℝ)) atTop (𝓝 0) ↔
      Tendsto μ atTop (𝓝 ν) ∧
      Tendsto (fun j => ∫ x, |x| ^ 3 ∂(μ j : Measure ℝ)) atTop
        (𝓝 (∫ x, |x| ^ 3 ∂(ν : Measure ℝ))))

theorem standardized_wassersteinThree_tendsto_iff
    (W : PublishedWassersteinThreeTopology)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw) :
    Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0) ↔
      Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)) := by
  exact W.tendsto_iff (fun j => (P j).toProbabilityMeasure) Q.toProbabilityMeasure
    (fun j => (P j).third_integrable) Q.third_integrable

theorem bounded_weak_wassersteinThree_tendsto
    (W : PublishedWassersteinThreeTopology)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ A) :
    Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0) :=
  (standardized_wassersteinThree_tendsto_iff W P Q).2
    ⟨hw, bounded_thirdMoment_tendsto P Q hw A hA hb⟩

end BerryEsseen
