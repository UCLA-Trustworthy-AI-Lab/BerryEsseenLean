import BerryEsseen.PublishedWassersteinThree
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

def thirdMomentTail (μ : Measure ℝ) (R : ℝ) : ℝ :=
  ∫ x in {x : ℝ | R < |x|}, |x| ^ 3 ∂μ

def cappedAbsoluteThirdBCF (A : ℝ) (hA : 0 ≤ A) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => min (|x| ^ 3) A) (by fun_prop) A (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) hA)]
      exact min_le_right _ _)

theorem cappedAbsoluteThird_integral_tendsto (P : StandardizedLaw) :
    Tendsto (fun N : ℕ => ∫ x, cappedAbsoluteThirdBCF (N : ℝ) (by positivity) x ∂P.measure)
      atTop (𝓝 (thirdMoment P)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => |x| ^ 3)
  · intro N
    exact (cappedAbsoluteThirdBCF (N : ℝ) (by positivity)).continuous.measurable.aestronglyMeasurable
  · exact P.third_integrable
  · intro N
    filter_upwards [] with x
    change ‖min (|x| ^ 3) (N : ℝ)‖ ≤ |x| ^ 3
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
    exact min_le_left _ _
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually (eventually_ge_atTop (|x| ^ 3))]
      with N hN
    change |x| ^ 3 = min (|x| ^ 3) (N : ℝ)
    exact (min_eq_left hN).symm

theorem thirdMoment_capped_residual_tendsto_zero (P : StandardizedLaw) :
    Tendsto (fun N : ℕ => thirdMoment P -
      ∫ x, cappedAbsoluteThirdBCF (N : ℝ) (by positivity) x ∂P.measure) atTop (𝓝 0) := by
  simpa only [sub_self] using (tendsto_const_nhds (x := thirdMoment P)).sub
    (cappedAbsoluteThird_integral_tendsto P)

theorem weak_thirdMoment_capped_residual_tendsto
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (A : ℝ) (hA : 0 ≤ A) :
    Tendsto (fun j => thirdMoment (P j) - ∫ x, cappedAbsoluteThirdBCF A hA x ∂(P j).measure)
      atTop (𝓝 (thirdMoment Q - ∫ x, cappedAbsoluteThirdBCF A hA x ∂Q.measure)) := by
  exact hm.sub (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw
    (cappedAbsoluteThirdBCF A hA))

theorem thirdMomentTail_le_capped_residual (P : StandardizedLaw) (A : ℝ) (hA : 0 ≤ A) :
    thirdMomentTail P.measure (2 * A + 1) ≤
      2 * (thirdMoment P - ∫ x, cappedAbsoluteThirdBCF A hA x ∂P.measure) := by
  let S := {x : ℝ | 2 * A + 1 < |x|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_abs
  have hi := (cappedAbsoluteThirdBCF A hA).integrable P.measure
  have hbound := integral_mono (P.third_integrable.indicator hS)
    ((P.third_integrable.sub hi).const_mul 2) (fun x => by
      change S.indicator (fun y => |y| ^ 3) x ≤ 2 * (|x| ^ 3 - min (|x| ^ 3) A)
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hx' : 2 * A + 1 < |x| := hx
        have hx1 : 1 ≤ |x| := by linarith
        have hc : |x| ≤ |x| ^ 3 := by
          have h2 : 1 ≤ |x| ^ 2 := by nlinarith [sq_nonneg (|x| - 1)]
          nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr h2)]
        rw [min_eq_right (by linarith : A ≤ |x| ^ 3)]
        linarith
      · rw [indicator_of_notMem hx]
        nlinarith [min_le_left (|x| ^ 3) A])
  rw [integral_indicator hS, integral_const_mul] at hbound
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub P.third_integrable hi] at hbound
  exact hbound

theorem weak_thirdMoment_eventually_small_tails
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ j in atTop, thirdMomentTail (P j).measure R ≤ ε := by
  have hlim := thirdMoment_capped_residual_tendsto_zero Q
  have he := (tendsto_order.1 hlim).2 (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := he.exists
  let A : ℝ := N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2 * A + 1, by positivity, ?_⟩
  have hconv := weak_thirdMoment_capped_residual_tendsto P Q hw hm A hA
  have hsmall : thirdMoment Q - ∫ x, cappedAbsoluteThirdBCF A hA x ∂Q.measure < ε / 2 := by
    exact hN.trans (by linarith)
  filter_upwards [(tendsto_order.1 hconv).2 (ε / 2) hsmall] with j hj
  have ht := thirdMomentTail_le_capped_residual (P j) A hA
  linarith

theorem wassersteinThree_eventually_small_thirdMoment_tails
    (W : PublishedWassersteinThreeTopology) (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ j in atTop, thirdMomentTail (P j).measure R ≤ ε := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  exact weak_thirdMoment_eventually_small_tails P Q hw hm ε hε

theorem thirdMomentTail_antitone (P : StandardizedLaw) :
    Antitone (thirdMomentTail P.measure) := by
  intro R S hRS
  have hS : MeasurableSet {x : ℝ | S < |x|} := measurableSet_lt measurable_const measurable_abs
  have hR : MeasurableSet {x : ℝ | R < |x|} := measurableSet_lt measurable_const measurable_abs
  unfold thirdMomentTail
  rw [← integral_indicator hS, ← integral_indicator hR]
  apply integral_mono (P.third_integrable.indicator hS) (P.third_integrable.indicator hR)
  intro x
  by_cases hx : x ∈ {x : ℝ | S < |x|}
  · have hxR : x ∈ {x : ℝ | R < |x|} := hRS.trans_lt hx
    simp only [indicator_of_mem hx, indicator_of_mem hxR]
    exact le_rfl
  · rw [indicator_of_notMem hx]
    by_cases hxR : x ∈ {x : ℝ | R < |x|}
    · rw [indicator_of_mem hxR]
      positivity
    · rw [indicator_of_notMem hxR]

theorem single_law_small_thirdMoment_tail (P : StandardizedLaw) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ thirdMomentTail P.measure R ≤ ε := by
  obtain ⟨R, hR, he⟩ := weak_thirdMoment_eventually_small_tails (fun _ => P) P
    tendsto_const_nhds tendsto_const_nhds ε hε
  obtain ⟨j, hj⟩ := he.exists
  exact ⟨R, hR, hj⟩

theorem weak_thirdMoment_uniformly_small_tails
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ j, thirdMomentTail (P j).measure R ≤ ε := by
  obtain ⟨R, hR, he⟩ := weak_thirdMoment_eventually_small_tails P Q hw hm ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.1 he
  have hsmall (j : ℕ) := single_law_small_thirdMoment_tail (P j) ε hε
  choose r hr hrtail using hsmall
  let T : ℝ := R + ∑ j ∈ Finset.range J, r j
  have hsum : 0 ≤ ∑ j ∈ Finset.range J, r j := Finset.sum_nonneg (fun j _ => (hr j).le)
  have hRT : R ≤ T := by dsimp [T]; linarith
  refine ⟨T, hR.trans_le hRT, ?_⟩
  intro j
  by_cases hj : J ≤ j
  · exact (thirdMomentTail_antitone (P j) hRT).trans (hJ j hj)
  · have hjJ : j ∈ Finset.range J := Finset.mem_range.mpr (by omega)
    have hrT : r j ≤ T := by
      have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range J) => (hr i).le) hjJ
      dsimp [T]
      linarith
    exact (thirdMomentTail_antitone (P j) hrT).trans (hrtail j)

theorem wassersteinThree_uniformly_small_thirdMoment_tails
    (W : PublishedWassersteinThreeTopology) (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ j, thirdMomentTail (P j).measure R ≤ ε := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  exact weak_thirdMoment_uniformly_small_tails P Q hw hm ε hε

end BerryEsseen
