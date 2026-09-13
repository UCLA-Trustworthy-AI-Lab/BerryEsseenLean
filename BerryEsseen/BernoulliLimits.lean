import BerryEsseen.ZeroNoiseBernoulli

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem standardizedBernoulliLaw_measure (p : ℝ) (hp : p ∈ Ioo 0 1) :
    (standardizedBernoulliLaw p hp).measure =
      ENNReal.ofReal (1 - p) • Measure.dirac (-p / Real.sqrt (p * (1 - p))) +
      ENNReal.ofReal p • Measure.dirac ((1 - p) / Real.sqrt (p * (1 - p))) := by
  rw [standardizedBernoulliLaw, standardizedTwoClusterLaw_measure, zero_clusterVariance, twoCluster_zero_noise]
  unfold standardizedMeasure bernoulliMeasure mixtureMeasure
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac (by fun_prop), Measure.map_dirac (by fun_prop)]
  simp only [zero_sub]

theorem integral_standardizedBernoulli (p : ℝ) (hp : p ∈ Ioo 0 1) (f : ℝ → ℝ) :
    (∫ x, f x ∂(standardizedBernoulliLaw p hp).measure) =
      (1 - p) * f (-p / Real.sqrt (p * (1 - p))) + p * f ((1 - p) / Real.sqrt (p * (1 - p))) := by
  rw [standardizedBernoulliLaw_measure]
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal hp.1.le,
    ENNReal.toReal_ofReal (sub_nonneg.2 hp.2.le)]

theorem standardizedBernoulli_pE :
    standardizedBernoulliLaw pE ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩ = esseenLaw := by
  apply standardizedLaw_eq_of_measure_eq
  rw [standardizedBernoulliLaw_measure]
  change _ = esseenMeasure
  simp only [esseenMeasure, aE, bE, sigmaE, qE, neg_div]

theorem standardizedBernoulli_tendsto_pE (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (hlim : Tendsto p atTop (𝓝 pE)) :
    Tendsto (fun j => (standardizedBernoulliLaw (p j) (hp j)).toProbabilityMeasure)
      atTop (𝓝 esseenLaw.toProbabilityMeasure) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun j => ∫ x, f x ∂(standardizedBernoulliLaw (p j) (hp j)).measure)
    atTop (𝓝 (∫ x, f x ∂esseenLaw.measure))
  simp_rw [integral_standardizedBernoulli]
  change Tendsto _ atTop (𝓝 (∫ x, f x ∂esseenMeasure))
  rw [integral_esseen]
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  have hσ := (hlim.mul hq).sqrt
  have hleft := hlim.neg.div hσ (Real.sqrt_pos.2 (mul_pos pE_pos qE_pos)).ne'
  have hright := hq.div hσ (Real.sqrt_pos.2 (mul_pos pE_pos qE_pos)).ne'
  have hfl := f.continuous.continuousAt.tendsto.comp hleft
  have hfr := f.continuous.continuousAt.tendsto.comp hright
  have h := (hq.mul hfl).add (hlim.mul hfr)
  simpa only [esseenLaw, aE, bE, sigmaE, qE, neg_div, Function.comp_apply, Pi.div_apply] using h

theorem standardizedBernoulli_third (p : ℝ) (hp : p ∈ Ioo 0 1) :
    thirdMoment (standardizedBernoulliLaw p hp) =
      (p ^ 2 + (1 - p) ^ 2) / Real.sqrt (p * (1 - p)) := by
  unfold standardizedBernoulliLaw
  rw [standardizedTwoClusterLaw_third, zero_clusterVariance,
    zero_clusterThirdAbsoluteMoment p ⟨hp.1.le, hp.2.le⟩]
  have hv := mul_pos hp.1 (sub_pos.2 hp.2)
  field_simp [(Real.sqrt_pos.2 hv).ne']
  rw [Real.sq_sqrt hv.le]
  ring

theorem bernoulli_central_parameter_bounds (p : ℝ) (hp : p ∈ Icc (2 / 5) (3 / 5)) :
    (2 / 5 : ℝ) ≤ Real.sqrt (p * (1 - p)) ∧ p ^ 2 + (1 - p) ^ 2 ≤ 3 / 5 := by
  have hv : (6 / 25 : ℝ) ≤ p * (1 - p) := by nlinarith [mul_nonneg (sub_nonneg.2 hp.1) (sub_nonneg.2 hp.2)]
  constructor
  · nlinarith [Real.sq_sqrt (by linarith : 0 ≤ p * (1 - p)), Real.sqrt_nonneg (p * (1 - p))]
  · nlinarith

theorem standardizedBernoulli_third_le_two (p : ℝ) (hp : p ∈ Ioo 0 1)
    (hcentral : p ∈ Icc (2 / 5) (3 / 5)) : thirdMoment (standardizedBernoulliLaw p hp) ≤ 2 := by
  rw [standardizedBernoulli_third]
  have h := bernoulli_central_parameter_bounds p hcentral
  apply (div_le_iff₀ (by linarith [h.1] : 0 < Real.sqrt (p * (1 - p)))).2
  linarith

theorem standardizedBernoulli_bounded (p : ℝ) (hp : p ∈ Ioo 0 1)
    (hcentral : p ∈ Icc (2 / 5) (3 / 5)) :
    ∀ᵐ x ∂(standardizedBernoulliLaw p hp).measure, |x| ≤ 10 := by
  have h := bernoulli_central_parameter_bounds p hcentral
  have hσ : 0 < Real.sqrt (p * (1 - p)) := by linarith [h.1]
  have ha : |-p / Real.sqrt (p * (1 - p))| ≤ 10 := by
    rw [abs_div, abs_neg, abs_of_pos hp.1, abs_of_pos hσ]
    apply (div_le_iff₀ hσ).2
    linarith [hcentral.2, h.1]
  have hb : |(1 - p) / Real.sqrt (p * (1 - p))| ≤ 10 := by
    rw [abs_div, abs_of_pos (sub_pos.2 hp.2), abs_of_pos hσ]
    apply (div_le_iff₀ hσ).2
    linarith [hcentral.1, h.1]
  rw [standardizedBernoulliLaw_measure, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure ((ae_dirac_iff (measurableSet_le (by fun_prop) measurable_const)).2 ha) _
  · exact Measure.ae_smul_measure ((ae_dirac_iff (measurableSet_le (by fun_prop) measurable_const)).2 hb) _

end BerryEsseen
