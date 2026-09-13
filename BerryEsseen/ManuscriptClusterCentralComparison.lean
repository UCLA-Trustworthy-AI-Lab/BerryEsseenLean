import BerryEsseen.ClusterCentralComparison
import BerryEsseen.ManuscriptOneSidedLoss

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-! Manuscript Lemma 3.3: the clipped one-sided loss applied to the actual conditional block. -/

theorem manuscript_twoCluster_central_comparison (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n k : ℕ) (hk : k ≤ n) (hb : 0 < binomialWeight p n k)
    (hsmall : (twoNoiseBlock P Q n k).fourthMoment ≤ 1 / 160000)
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
        176000 * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment +
        blockLeakageBudget P Q p n k) ∧
    (G u - strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ≤
      G 0 - (∑ j ∈ Finset.range k, binomialWeight p n j) -
        3 / 8 * binomialWeight p n k * (twoNoiseBlock P Q n k).absoluteMoment +
        176000 * binomialWeight p n k * (twoNoiseBlock P Q n k).fourthMoment +
        blockLeakageBudget P Q p n k) := by
  let W := twoNoiseBlock P Q n k
  have hloss := manuscript_one_sided_loss (μ := W.measure) (W := fun x : ℝ => x)
    measurable_id W.fourth_integrable W.mean_zero hsmall hf hfd (by simp) hd hu
  have hright : W.measure.real {x : ℝ | u < x} = 1 - cdf W.measure u := by
    rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic]
    rfl
  change (3 / 8 * W.absoluteMoment - 176000 * W.fourthMoment ≤
    W.measure.real {x : ℝ | u < x} + (G u - G 0) / binomialWeight p n k) ∧
    (3 / 8 * W.absoluteMoment - 176000 * W.fourthMoment ≤
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


end BerryEsseen
