import BerryEsseen.RawWassersteinThreeMoments
import BerryEsseen.RawAffineWeak

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def rawStandardizedLaw (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) : StandardizedLaw := by
  refine standardizedLaw (μ : Measure ℝ) (rawMean (μ : Measure ℝ)) (rawStdDev (μ : Measure ℝ))
    hσ (raw_first_second_integrable_of_third (μ : Measure ℝ) hi).1
    (raw_shifted_second_integrable (μ : Measure ℝ) hi _)
    (raw_shifted_third_integrable (μ : Measure ℝ) hi _) rfl ?_
  exact (Real.sq_sqrt (integral_nonneg (fun x : ℝ => sq_nonneg (x - rawMean (μ : Measure ℝ))))).symm

theorem rawStandardizedLaw_measure (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) :
    (rawStandardizedLaw μ hi hσ).measure =
      standardizedMeasure (μ : Measure ℝ) (rawMean (μ : Measure ℝ)) (rawStdDev (μ : Measure ℝ)) := rfl

theorem rawStandardizedLaw_thirdMoment (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) :
    thirdMoment (rawStandardizedLaw μ hi hσ) =
      rawThirdAbsoluteMoment (μ : Measure ℝ) / rawStdDev (μ : Measure ℝ) ^ 3 := by
  exact standardizedMeasure_third (μ : Measure ℝ) (rawMean (μ : Measure ℝ))
    (rawStdDev (μ : Measure ℝ)) hσ.le

theorem rawStandardizedLaw_signedThirdMoment (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) :
    signedThirdMoment (rawStandardizedLaw μ hi hσ) =
      (∫ x, (x - rawMean (μ : Measure ℝ)) ^ 3 ∂(μ : Measure ℝ)) /
        rawStdDev (μ : Measure ℝ) ^ 3 := by
  change (∫ x, x ^ 3 ∂standardizedMeasure (μ : Measure ℝ)
    (rawMean (μ : Measure ℝ)) (rawStdDev (μ : Measure ℝ))) = _
  rw [standardizedMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [div_pow]
  exact integral_div _ _

theorem rawStandardizedLaw_toProbabilityMeasure (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) :
    (rawStandardizedLaw μ hi hσ).toProbabilityMeasure =
      μ.map (show Measurable (fun x : ℝ => (rawStdDev (μ : Measure ℝ))⁻¹ * x +
        (-(rawMean (μ : Measure ℝ)) / rawStdDev (μ : Measure ℝ))) by fun_prop).aemeasurable := by
  apply Subtype.ext
  change (μ : Measure ℝ).map (fun x => (x - rawMean (μ : Measure ℝ)) / rawStdDev (μ : Measure ℝ)) = _
  congr 1
  funext x
  dsimp
  ring

theorem raw_standardization_wassersteinThree_tendsto
    (W : PublishedWassersteinThreeTopology)
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hW : Tendsto (fun j => wassersteinThree (μj j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0))
    (hσj : ∀ j, 0 < rawStdDev (μj j : Measure ℝ))
    (hσQ : 0 < rawStdDev (μ : Measure ℝ)) :
    Tendsto (fun j => wassersteinThree (rawStandardizedLaw (μj j) (hi j) (hσj j)).measure
      (rawStandardizedLaw μ hiQ hσQ).measure) atTop (𝓝 0) := by
  obtain ⟨hw, hm⟩ := (W.tendsto_iff μj μ hi hiQ).1 hW
  obtain ⟨hmean, hsd, hthird⟩ := wassersteinThree_raw_moments_tendsto W μj μ hi hiQ hW
  apply (standardized_wassersteinThree_tendsto_iff W
    (fun j => rawStandardizedLaw (μj j) (hi j) (hσj j)) (rawStandardizedLaw μ hiQ hσQ)).2
  constructor
  · have ha := hsd.inv₀ hσQ.ne'
    have hb := hmean.neg.div hsd hσQ.ne'
    have hmap := probabilityMeasure_tendsto_map_affine μj μ
      (fun j => (rawStdDev (μj j : Measure ℝ))⁻¹)
      (fun j => -(rawMean (μj j : Measure ℝ)) / rawStdDev (μj j : Measure ℝ))
      (rawStdDev (μ : Measure ℝ))⁻¹
      (-(rawMean (μ : Measure ℝ)) / rawStdDev (μ : Measure ℝ)) hw ha hb
    simpa only [rawStandardizedLaw_toProbabilityMeasure] using hmap
  · simpa only [rawStandardizedLaw_thirdMoment] using
      hthird.div (hsd.pow 3) (pow_ne_zero 3 hσQ.ne')

theorem rawStdDev_eventually_pos_of_wassersteinThree
    (W : PublishedWassersteinThreeTopology)
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hW : Tendsto (fun j => wassersteinThree (μj j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0))
    (hσQ : 0 < rawStdDev (μ : Measure ℝ)) :
    ∀ᶠ j in atTop, 0 < rawStdDev (μj j : Measure ℝ) := by
  have hsd := (wassersteinThree_raw_moments_tendsto W μj μ hi hiQ hW).2.1
  exact (tendsto_order.1 hsd).1 0 hσQ

theorem rawStandardizedLaw_maximalSpan (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) (d : ℝ)
    (hd : 0 ≤ d ∧ (0 < d → IsLatticeSpan (μ : Measure ℝ) d) ∧
      ∀ h : ℝ, IsLatticeSpan (μ : Measure ℝ) h → h ≤ d) :
    IsMaximalSpan (rawStandardizedLaw μ hi hσ) (d / rawStdDev (μ : Measure ℝ)) := by
  refine ⟨div_nonneg hd.1 hσ.le, ?_, ?_⟩
  · intro hp
    have hdp : 0 < d := (div_pos_iff_of_pos_right hσ).mp hp
    exact latticeSpan_standardized (μ : Measure ℝ) (rawMean (μ : Measure ℝ))
      (rawStdDev (μ : Measure ℝ)) d hσ (hd.2.1 hdp)
  · intro e he
    have hraw := (latticeSpan_standardized_iff (μ : Measure ℝ)
      (rawMean (μ : Measure ℝ)) (rawStdDev (μ : Measure ℝ)) e hσ).1 he
    apply (le_div_iff₀ hσ).2
    simpa only [mul_comm] using hd.2.2 _ hraw

end BerryEsseen
