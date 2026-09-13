import BerryEsseen.ClusterStandardization
import BerryEsseen.ExactMomentInterpolation
import BerryEsseen.PublishedBernoulli
import BerryEsseen.EsseenLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem CenteredFourthLaw.zero_second : CenteredFourthLaw.zero.secondMoment = 0 := by
  simp [CenteredFourthLaw.secondMoment, CenteredFourthLaw.zero]

theorem CenteredFourthLaw.zero_third : CenteredFourthLaw.zero.thirdMoment = 0 := by
  simp [CenteredFourthLaw.thirdMoment, CenteredFourthLaw.zero]

theorem twoCluster_eq_bernoulli_of_zero_variance (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) (hz : accumulatedNoiseVariance P Q p n = 0) :
    twoClusterMeasure P Q p = bernoulliMeasure p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1 - p := sub_pos.2 hp.2
  have hzero : (1 - p) * P.secondMoment + p * Q.secondMoment = 0 := by
    unfold accumulatedNoiseVariance at hz
    exact (mul_eq_zero.1 hz).resolve_left hn0.ne'
  have hP0 : P.secondMoment = 0 := by
    have hpv : (1 - p) * P.secondMoment = 0 := by
      nlinarith [mul_nonneg hq.le P.secondMoment_nonneg, mul_nonneg hp.1.le Q.secondMoment_nonneg]
    exact (mul_eq_zero.1 hpv).resolve_left hq.ne'
  have hQ0 : Q.secondMoment = 0 := by
    rw [hP0, mul_zero, zero_add] at hzero
    exact (mul_eq_zero.1 hzero).resolve_left hp.1.ne'
  rw [twoClusterMeasure, P.measure_eq_dirac_of_second_zero hP0, Q.measure_eq_dirac_of_second_zero hQ0,
    Measure.map_dirac (by fun_prop : Measurable (fun x : ℝ => 1 + x))]
  simp only [add_zero, bernoulliMeasure]

def standardizedBernoulliLaw (p : ℝ) (hp : p ∈ Ioo 0 1) : StandardizedLaw :=
  standardizedTwoClusterLaw CenteredFourthLaw.zero CenteredFourthLaw.zero p hp

theorem zero_clusterVariance (p : ℝ) : clusterVariance CenteredFourthLaw.zero CenteredFourthLaw.zero p = p * (1 - p) := by
  simp [clusterVariance, CenteredFourthLaw.zero_second]

theorem zero_clusterThirdAbsoluteMoment (p : ℝ) (hp : p ∈ Icc 0 1) :
    clusterThirdAbsoluteMoment CenteredFourthLaw.zero CenteredFourthLaw.zero p =
      p * (1 - p) * (p ^ 2 + (1 - p) ^ 2) := by
  unfold clusterThirdAbsoluteMoment
  have hb : ∀ᵐ x ∂CenteredFourthLaw.zero.measure, |x| ≤ (0 : ℝ) := by
    simp [CenteredFourthLaw.zero]
  rw [twoCluster_abs_third _ _ p 0 hp hp.1 (sub_nonneg.2 hp.2) hb hb,
    CenteredFourthLaw.zero_second, CenteredFourthLaw.zero_third]
  ring

theorem standardizedBernoulli_discrepancy (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    normalizedDiscrepancy (standardizedBernoulliLaw p hp) n
      ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))) =
      Real.sqrt ((n : ℝ) * p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) *
        |cdf (binomialMeasure p n) t - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| := by
  have h := standardizedTwoCluster_discrepancy CenteredFourthLaw.zero CenteredFourthLaw.zero p hp n hn t
  rw [zero_clusterVariance, zero_clusterThirdAbsoluteMoment p ⟨hp.1.le, hp.2.le⟩,
    twoCluster_zero_noise] at h
  rw [mul_assoc (n : ℝ) p (1 - p)]
  unfold standardizedBernoulliLaw
  rw [h]
  change _ = _ * |cdf (iidSumLaw (bernoulliMeasure p) n) t - _|
  congr 1
  have hv : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.2 hp.2)
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.sqrt_mul hn0.le]
  field_simp [hv.ne', hτ.ne', (Real.sqrt_pos.2 hv).ne']
  rw [Real.sq_sqrt hv.le, div_self hv.ne']

theorem standardizedBernoulli_uniform_strict_bound (S : PublishedBernoulliBound) (p : ℝ)
    (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ r < cE, ∀ x : ℝ, normalizedDiscrepancy (standardizedBernoulliLaw p hp) n x ≤ r := by
  let a := Real.sqrt ((n : ℝ) * p * (1 - p))
  let τ := p ^ 2 + (1 - p) ^ 2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 := hp.1
  have hq0 : 0 < 1 - p := sub_pos.2 hp.2
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hτ : 0 < τ := by dsimp [τ]; nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  refine ⟨a / τ * binomialKolmogorov p n, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_left (S.strict_bound p hp n hn) (div_pos ha hτ)
    change a / τ * binomialKolmogorov p n < a / τ * (cE * τ / a) at h
    convert h using 1
    field_simp
  · intro x
    have he : ((a * x + (n : ℝ) * p) - n * p) / a = x := by field_simp; ring
    have h := standardizedBernoulli_discrepancy p hp n hn (a * x + (n : ℝ) * p)
    change normalizedDiscrepancy _ n (((a * x + n * p) - n * p) / a) = _ at h
    rw [he] at h
    rw [h]
    have hD := binomialDiscrepancy_le_Kolmogorov p ⟨hp.1.le, hp.2.le⟩ n (a * x + (n : ℝ) * p)
    change |cdf (binomialMeasure p n) (a * x + (n : ℝ) * p) - normalCDF (((a * x + (n : ℝ) * p) - n * p) / a)| ≤ _ at hD
    rw [he] at hD
    exact mul_le_mul_of_nonneg_left hD (div_nonneg ha.le hτ.le)

theorem zero_noise_standardizedLaw (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) (hz : accumulatedNoiseVariance P Q p n = 0) :
    standardizedTwoClusterLaw P Q p hp = standardizedBernoulliLaw p hp := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmix : (1 - p) * P.secondMoment + p * Q.secondMoment = 0 := by
    exact (mul_eq_zero.1 hz).resolve_left hn0.ne'
  have hv : clusterVariance P Q p = p * (1 - p) := by unfold clusterVariance; linarith only [hmix]
  apply standardizedLaw_eq_of_measure_eq
  rw [standardizedTwoClusterLaw_measure]
  change _ = (standardizedTwoClusterLaw CenteredFourthLaw.zero CenteredFourthLaw.zero p hp).measure
  rw [standardizedTwoClusterLaw_measure, hv, zero_clusterVariance, twoCluster_zero_noise,
    twoCluster_eq_bernoulli_of_zero_variance P Q p hp n hn hz]

theorem zero_noise_BoundAt (S : PublishedBernoulliBound) (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) (hz : accumulatedNoiseVariance P Q p n = 0) :
    BoundAt (standardizedTwoClusterLaw P Q p hp) n := by
  rw [zero_noise_standardizedLaw P Q p hp n hn hz, BoundAt_iff_normalized _ n hn]
  obtain ⟨r, hr, hbound⟩ := standardizedBernoulli_uniform_strict_bound S p hp n hn
  exact fun x => (hbound x).trans hr.le

end BerryEsseen
