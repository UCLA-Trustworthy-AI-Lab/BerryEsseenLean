import BerryEsseen.GeneralThirdMomentTails

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

theorem signedThirdMoment_clipped_error (P : StandardizedLaw) (A : ℝ) (hA : 0 ≤ A) :
    |signedThirdMoment P - ∫ x, clippedThirdBCF A hA x ∂P.measure| ≤
      2 * thirdMomentTail P.measure A := by
  let S := {x : ℝ | A < |x|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_abs
  have hi := (clippedThirdBCF A hA).integrable P.measure
  rw [signedThirdMoment, ← integral_sub (signedThirdMoment_integrable P) hi]
  have hnorm := norm_integral_le_integral_norm
    (f := fun x => x ^ 3 - clippedThirdBCF A hA x) (μ := P.measure)
  rw [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  have hbound := integral_mono ((signedThirdMoment_integrable P).sub hi).norm
    ((P.third_integrable.indicator hS).const_mul 2) (fun x => by
      change |x ^ 3 - (clippedReal A x) ^ 3| ≤ 2 * S.indicator (fun y => |y| ^ 3) x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hc : |clippedReal A x| ≤ |x| := (clippedReal_abs_le A x hA).trans hx.le
        have hh := abs_sub_le (x ^ 3) 0 ((clippedReal A x) ^ 3)
        simp only [sub_zero, zero_sub, abs_neg, abs_pow] at hh
        nlinarith [pow_le_pow_left₀ (abs_nonneg _) hc 3]
      · rw [indicator_of_notMem hx, clippedReal_eq_self_of_abs_le A x (le_of_not_gt hx)]
        simp)
  rw [integral_const_mul, integral_indicator hS] at hbound
  exact hbound

theorem weak_thirdMoment_signedThirdMoment_tendsto
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q))) :
    Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 (signedThirdMoment Q)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨R, hR, hPR⟩ := weak_thirdMoment_uniformly_small_tails P Q hw hm (ε / 8) (by positivity)
  obtain ⟨T, hT, hQT⟩ := single_law_small_thirdMoment_tail Q (ε / 8) (by positivity)
  let A := max R T
  have hA : 0 ≤ A := hR.le.trans (le_max_left _ _)
  have hPA (j : ℕ) : thirdMomentTail (P j).measure A ≤ ε / 8 :=
    (thirdMomentTail_antitone (P j) (le_max_left _ _)).trans (hPR j)
  have hQA : thirdMomentTail Q.measure A ≤ ε / 8 :=
    (thirdMomentTail_antitone Q (le_max_right _ _)).trans hQT
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw (clippedThirdBCF A hA)
  filter_upwards [Metric.tendsto_nhds.1 hc (ε / 2) (by positivity)] with j hj
  rw [Real.dist_eq] at hj ⊢
  have hp := signedThirdMoment_clipped_error (P j) A hA
  have hq := signedThirdMoment_clipped_error Q A hA
  have htri := abs_sub_le (signedThirdMoment (P j))
    (∫ x, clippedThirdBCF A hA x ∂(P j).measure) (signedThirdMoment Q)
  have htri' := abs_sub_le (∫ x, clippedThirdBCF A hA x ∂(P j).measure)
    (∫ x, clippedThirdBCF A hA x ∂Q.measure) (signedThirdMoment Q)
  rw [abs_sub_comm (∫ x, clippedThirdBCF A hA x ∂Q.measure) (signedThirdMoment Q)] at htri'
  change |(∫ x, clippedThirdBCF A hA x ∂(P j).measure) -
    ∫ x, clippedThirdBCF A hA x ∂Q.measure| < ε / 2 at hj
  linarith [hPA j]

end BerryEsseen
