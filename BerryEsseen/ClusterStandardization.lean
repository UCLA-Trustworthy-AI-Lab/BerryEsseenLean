import BerryEsseen.ClusterMoments
import BerryEsseen.ClassicalBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace BerryEsseen

def clusterVariance (P Q : CenteredFourthLaw) (p : ℝ) : ℝ :=
  p * (1 - p) + (1 - p) * P.secondMoment + p * Q.secondMoment

def clusterThirdAbsoluteMoment (P Q : CenteredFourthLaw) (p : ℝ) : ℝ :=
  ∫ x, |x - p| ^ 3 ∂twoClusterMeasure P Q p

theorem clusterVariance_pos (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    0 < clusterVariance P Q p := by
  have hq : 0 < 1 - p := sub_pos.2 hp.2
  unfold clusterVariance
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (mul_pos hp.1 hq)
    (mul_nonneg hq.le P.secondMoment_nonneg)) (mul_nonneg hp.1.le Q.secondMoment_nonneg)

theorem integrable_twoClusterMeasure (P Q : CenteredFourthLaw) (p : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) (hP : Integrable f P.measure)
    (hQ : Integrable (fun x => f (1 + x)) Q.measure) :
    Integrable f (twoClusterMeasure P Q p) := by
  have hi : Integrable f (Q.measure.map (fun x => 1 + x)) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2 hQ
  exact (hP.smul_measure ENNReal.ofReal_ne_top).add_measure (hi.smul_measure ENNReal.ofReal_ne_top)

theorem twoCluster_first_integrable (P Q : CenteredFourthLaw) (p : ℝ) :
    Integrable (fun x : ℝ => x) (twoClusterMeasure P Q p) :=
  integrable_twoClusterMeasure P Q p (fun x => x) measurable_id P.first_integrable
    ((integrable_const 1).add Q.first_integrable)

theorem twoCluster_centered_second_integrable (P Q : CenteredFourthLaw) (p : ℝ) :
    Integrable (fun x : ℝ => (x - p) ^ 2) (twoClusterMeasure P Q p) := by
  apply integrable_twoClusterMeasure P Q p (fun x => (x - p) ^ 2) (by fun_prop) (P.shifted_square_integrable p)
  convert Q.shifted_square_integrable (p - 1) using 1
  funext x
  ring

theorem twoCluster_centered_third_integrable (P Q : CenteredFourthLaw) (p : ℝ) :
    Integrable (fun x : ℝ => |x - p| ^ 3) (twoClusterMeasure P Q p) := by
  apply integrable_twoClusterMeasure P Q p (fun x => |x - p| ^ 3) (by fun_prop) (P.shifted_abs_cube_integrable p)
  convert Q.shifted_abs_cube_integrable (p - 1) using 1
  funext x
  congr 2
  ring

def standardizedTwoClusterLaw (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) : StandardizedLaw := by
  letI := twoClusterMeasure_probability P Q p ⟨hp.1.le, hp.2.le⟩
  refine standardizedLaw (twoClusterMeasure P Q p) p (Real.sqrt (clusterVariance P Q p))
    (Real.sqrt_pos.2 (clusterVariance_pos P Q p hp))
    (twoCluster_first_integrable P Q p) (twoCluster_centered_second_integrable P Q p)
    (twoCluster_centered_third_integrable P Q p) (twoCluster_mean P Q p ⟨hp.1.le, hp.2.le⟩) ?_
  rw [Real.sq_sqrt (clusterVariance_pos P Q p hp).le]
  exact twoCluster_variance P Q p ⟨hp.1.le, hp.2.le⟩

theorem standardizedTwoClusterLaw_measure (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    (standardizedTwoClusterLaw P Q p hp).measure =
      standardizedMeasure (twoClusterMeasure P Q p) p (Real.sqrt (clusterVariance P Q p)) := rfl

theorem standardizedTwoClusterLaw_third (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    thirdMoment (standardizedTwoClusterLaw P Q p hp) =
      clusterThirdAbsoluteMoment P Q p / Real.sqrt (clusterVariance P Q p) ^ 3 := by
  change (∫ x, |x| ^ 3 ∂standardizedMeasure _ _ _) = _
  exact standardizedMeasure_third _ _ _ (Real.sqrt_nonneg _)

theorem clusterThirdAbsoluteMoment_pos (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    0 < clusterThirdAbsoluteMoment P Q p := by
  have h := thirdMoment_pos (standardizedTwoClusterLaw P Q p hp)
  rw [standardizedTwoClusterLaw_third] at h
  exact (div_pos_iff_of_pos_right (pow_pos (Real.sqrt_pos.2 (clusterVariance_pos P Q p hp)) 3)).1 h

theorem standardizedTwoCluster_discrepancy (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n
      ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) =
      Real.sqrt (n : ℝ) * Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p *
        |cdf (iidSumLaw (twoClusterMeasure P Q p) n) t -
          normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))| := by
  letI := twoClusterMeasure_probability P Q p ⟨hp.1.le, hp.2.le⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv := clusterVariance_pos P Q p hp
  have hs : Real.sqrt (n : ℝ) * ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) =
      (t - (n : ℝ) * p) / Real.sqrt (clusterVariance P Q p) := by
    rw [Real.sqrt_mul hn0.le]
    field_simp [(Real.sqrt_pos.2 hn0).ne', (Real.sqrt_pos.2 hv).ne']
  unfold normalizedDiscrepancy discrepancy
  rw [standardizedTwoClusterLaw_measure]
  rw [hs]
  have he := standardized_sum_cdf (twoClusterMeasure P Q p) p (Real.sqrt (clusterVariance P Q p)) (Real.sqrt_pos.2 hv) n t
  simp only [cdf_eq_real, Measure.real] at he
  rw [he, standardizedTwoClusterLaw_third]
  simp only [cdf_eq_real, Measure.real]
  field_simp [(clusterThirdAbsoluteMoment_pos P Q p hp).ne', (Real.sqrt_pos.2 hv).ne']

end BerryEsseen
