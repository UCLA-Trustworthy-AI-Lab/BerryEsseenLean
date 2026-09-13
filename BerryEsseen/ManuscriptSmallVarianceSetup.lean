import BerryEsseen.ManuscriptBinomialLimit

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def manuscriptParameterRadius : ℝ := min (pE - 2 / 5) (9 / 20 - pE) / 2

theorem manuscriptParameterRadius_pos : 0 < manuscriptParameterRadius := by
  unfold manuscriptParameterRadius
  exact div_pos (lt_min (sub_pos.mpr pE_bounds.1) (sub_pos.mpr pE_bounds.2)) (by norm_num)

theorem manuscriptParameterRadius_bounds :
    manuscriptParameterRadius ≤ 1 / 40 ∧
    manuscriptParameterRadius ≤ pE - 2 / 5 ∧ manuscriptParameterRadius ≤ 9 / 20 - pE := by
  have hlo := min_le_left (pE - 2 / 5) (9 / 20 - pE)
  have hhi := min_le_right (pE - 2 / 5) (9 / 20 - pE)
  have hp := manuscriptParameterRadius_pos
  unfold manuscriptParameterRadius at *
  constructor
  · linarith
  · constructor <;> linarith

theorem manuscript_small_parameter_bounds (d p : ℝ) (hd : d ≤ manuscriptParameterRadius)
    (hp : |p - pE| ≤ d) :
    p ∈ Icc (2 / 5) (9 / 20) ∧ d ≤ p ∧ d ≤ 1 - p := by
  have hb := manuscriptParameterRadius_bounds
  have hclose := abs_le.mp hp
  have hpcc : p ∈ Icc (2 / 5) (9 / 20) := by
    constructor <;> linarith [hb.2.1, hb.2.2]
  refine ⟨hpcc, ?_, ?_⟩ <;> linarith [hb.1, hpcc.1, hpcc.2]

def manuscriptSmallVarianceGap (d ε lam : ℝ) : ℝ :=
  min (d * lam / Real.sqrt (3 * lam / (2 / 5) + ε ^ 2)) d

theorem manuscriptSmallVarianceGap_nonneg (d ε lam : ℝ) (hd : 0 ≤ d) (hlam : 0 ≤ lam) :
    0 ≤ manuscriptSmallVarianceGap d ε lam := by
  unfold manuscriptSmallVarianceGap
  exact le_min (by positivity) hd

theorem manuscriptSmallVarianceGap_pos (d ε lam : ℝ) (hd : 0 < d) (hlam : 0 < lam) :
    0 < manuscriptSmallVarianceGap d ε lam := by
  unfold manuscriptSmallVarianceGap
  exact lt_min (by positivity) hd

theorem manuscript_small_variance_bad_threshold (P Q : CenteredFourthLaw)
    (p ε d : ℝ) (hp : p ∈ Ioo 0 1) (hd : 0 < d) (n : ℕ) (hn : 1 ≤ n)
    (hbad : rawNormalizedConstant (bernoulliMeasure p) n -
      manuscriptSmallVarianceGap d ε (accumulatedNoiseVariance P Q p n) <
      rawNormalizedConstant (twoClusterMeasure P Q p) n) :
    0 < accumulatedNoiseVariance P Q p n ∧ ∃ (k : ℤ) (u : ℝ), |u| ≤ 1 / 2 ∧
      rawNormalizedConstant (bernoulliMeasure p) n -
        manuscriptSmallVarianceGap d ε (accumulatedNoiseVariance P Q p n) <
      normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n
        (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) := by
  have hlam : 0 < accumulatedNoiseVariance P Q p n := by
    have hz0 := accumulatedNoiseVariance_nonneg P Q p ⟨hp.1.le, hp.2.le⟩ n
    by_contra! h
    have hz : accumulatedNoiseVariance P Q p n = 0 := le_antisymm h hz0
    have he := twoCluster_eq_bernoulli_of_zero_variance P Q p hp n hn hz
    simp only [hz, manuscriptSmallVarianceGap, mul_zero, zero_div, min_eq_left hd.le,
      sub_zero, he, lt_self_iff_false] at hbad
  refine ⟨hlam, ?_⟩
  rw [rawNormalizedConstant_twoCluster P Q p hp n hn] at hbad
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (range_nonempty _) hbad
  let a := Real.sqrt ((n : ℝ) * clusterVariance P Q p)
  have ha : 0 < a := Real.sqrt_pos.mpr
    (mul_pos (by exact_mod_cast (show 0 < n by omega)) (clusterVariance_pos P Q p hp))
  let t := (n : ℝ) * p + a * x
  refine ⟨round t, t - round t, abs_sub_round t, ?_⟩
  have he : ((round t : ℝ) + (t - round t) - n * p) / a = x := by
    dsimp only [t]
    field_simp [ha.ne']
    <;> ring
  change _ < normalizedDiscrepancy _ _ (((round t : ℝ) + (t - round t) - n * p) / a)
  rw [he]
  exact hx

end BerryEsseen
