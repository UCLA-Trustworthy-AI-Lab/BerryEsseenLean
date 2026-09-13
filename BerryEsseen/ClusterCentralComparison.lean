import BerryEsseen.BlockLeakage
import BerryEsseen.OneSidedLoss

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem twoClusterMeasure_probability (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) :
    IsProbabilityMeasure (twoClusterMeasure P Q p) := by
  letI : IsProbabilityMeasure (Q.measure.map (fun x => 1 + x)) := Measure.isProbabilityMeasure_map (by fun_prop)
  exact mixtureMeasure_probability _ _ p hp

theorem twoCluster_central_comparison (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n k : ℕ) (hk : k ≤ n) (hb : 0 < binomialWeight p n k)
    (G : ℝ → ℝ)
    (hf : ContinuousOn (fun u => (G u - G 0) / binomialWeight p n k) (Icc (-(3 / 5)) (3 / 5)))
    (hfd : DifferentiableOn ℝ (fun u => (G u - G 0) / binomialWeight p n k) (Ioo (-(3 / 5)) (3 / 5)))
    (hd : ∀ u ∈ Ioo (-(3 / 5)) (3 / 5),
      3 / 4 ≤ deriv (fun u => (G u - G 0) / binomialWeight p n k) u ∧
      deriv (fun u => (G u - G 0) / binomialWeight p n k) u ≤ 5 / 4)
    (u : ℝ) (hu : |u| ≤ 1 / 2) :
    (cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) - G u ≤
      (∑ j ∈ Finset.range k, binomialWeight p n j) + binomialWeight p n k - G 0 -
        3 / 8 * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
        11000 * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment +
        blockLeakageBudget P Q p n k) ∧
    (G u - strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ≤
      G 0 - (∑ j ∈ Finset.range k, binomialWeight p n j) -
        3 / 8 * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
        11000 * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment +
        blockLeakageBudget P Q p n k) := by
  let W := twoNoiseBlock P Q n k
  have hloss := one_sided_loss (μ := W.measure) (W := fun x : ℝ => x)
    measurable_id W.fourth_integrable W.mean_zero hf hfd (by simp) hd hu
  have hright : W.measure.real {x : ℝ | u < x} = 1 - cdf W.measure u := by
    rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic]
    rfl
  change (3 / 8 * W.absoluteMoment - 11000 * W.fourthMoment ≤
    W.measure.real {x : ℝ | u < x} + (G u - G 0) / binomialWeight p n k) ∧
    (3 / 8 * W.absoluteMoment - 11000 * W.fourthMoment ≤
    strictCDF W.measure u - (G u - G 0) / binomialWeight p n k) at hloss
  rw [hright] at hloss
  have ha := mul_le_mul_of_nonneg_left hloss.1 hb.le
  have hb' := mul_le_mul_of_nonneg_left hloss.2 hb.le
  have hdiv : binomialWeight p n k * ((G u - G 0) / binomialWeight p n k) = G u - G 0 :=
    mul_div_cancel₀ _ hb.ne'
  rw [mul_add, hdiv] at ha
  simp only [mul_sub, hdiv] at hb'
  have hF := abs_le.1 (twoCluster_cdf_block_leakage P Q p hp n k u hu)
  have hF' := abs_le.1 (twoCluster_strictCDF_block_leakage P Q p hp n k u hu)
  rw [blockApproximation_central P Q p n k hk u] at hF
  rw [strictBlockApproximation_central P Q p n k hk u] at hF'
  constructor <;> dsimp only [W] at ha hb' <;> push_cast at * <;> nlinarith only [ha, hb', hF.2, hF'.1]

theorem twoCluster_block_cdf_enclosure (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n k : ℕ) (hk : k ≤ n) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    (∑ j ∈ Finset.range k, binomialWeight p n j) - blockLeakageBudget P Q p n k ≤
      strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ∧
    cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ≤
      (∑ j ∈ Finset.range k, binomialWeight p n j) + binomialWeight p n k + blockLeakageBudget P Q p n k := by
  have hF := abs_le.1 (twoCluster_cdf_block_leakage P Q p hp n k u hu)
  have hF' := abs_le.1 (twoCluster_strictCDF_block_leakage P Q p hp n k u hu)
  rw [blockApproximation_central P Q p n k hk u] at hF
  rw [strictBlockApproximation_central P Q p n k hk u] at hF'
  have hp0 := binomialWeight_nonneg p hp n k
  have hl := strictCDF_nonneg (twoNoiseBlock P Q n k).measure u
  have hr := cdf_le_one (twoNoiseBlock P Q n k).measure u
  constructor <;> push_cast at * <;> nlinarith only [hF.2, hF'.1, mul_nonneg hp0 hl,
    mul_le_mul_of_nonneg_left hr hp0]

end BerryEsseen
