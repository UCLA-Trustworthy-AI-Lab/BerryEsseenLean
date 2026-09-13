import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.GaussianClusterComparison
import BerryEsseen.AppliedClusterBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def bernoulliNormalizationE : ℝ := sigmaE ^ 3 / (pE * qE * (pE ^ 2 + qE ^ 2))

theorem bernoulliNormalizationE_pos : 0 < bernoulliNormalizationE := by
  unfold bernoulliNormalizationE
  have := pE_pos
  have := qE_pos
  have := sigmaE_pos
  positivity

theorem clusterVariance_tendsto (P Q : ℕ → CenteredFourthLaw) (p : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 pE))
    (hs : Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0)) :
    Tendsto (fun j => clusterVariance (P j) (Q j) (p j)) atTop (𝓝 (pE * qE)) := by
  have h := (hp.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).add hs
  simpa only [qE, add_zero, clusterVariance, averageNoiseVariance, add_assoc] using h

theorem clusterThirdAbsoluteMoment_tendsto (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hplim : Tendsto p atTop (𝓝 pE))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j) (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (hs : Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0)) :
    Tendsto (fun j => clusterThirdAbsoluteMoment (P j) (Q j) (p j)) atTop (𝓝 (pE * qE * (pE ^ 2 + qE ^ 2))) := by
  have herror : Tendsto (fun j => clusterThirdAbsoluteMoment (P j) (Q j) (p j) -
      p j * (1 - p j) * ((p j) ^ 2 + (1 - p j) ^ 2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_) (by simpa only [mul_zero] using hs.const_mul 4)
    rw [Real.norm_eq_abs]
    have he := twoCluster_abs_third_error (P j) (Q j) (p j) (ε j) ⟨(hp j).1.le, (hp j).2.le⟩
      (hεp j) (hεq j) (hP j) (hQ j)
    have hε1 : ε j ≤ 1 := (hεp j).trans (hp j).2.le
    have hs0 := averageNoiseVariance_nonneg (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩
    change |_ - _| ≤ (3 + ε j) * averageNoiseVariance (P j) (Q j) (p j) at he
    exact he.trans (mul_le_mul_of_nonneg_right (by linarith) hs0)
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hplim
  have hb := (hplim.mul hq).mul ((hplim.pow 2).add (hq.pow 2))
  simpa only [sub_add_cancel, zero_add, qE] using herror.add hb

theorem clusterNormalization_tendsto (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hplim : Tendsto p atTop (𝓝 pE))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j) (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (hs : Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0)) :
    Tendsto (fun j => Real.sqrt (clusterVariance (P j) (Q j) (p j)) ^ 3 /
      clusterThirdAbsoluteMoment (P j) (Q j) (p j)) atTop (𝓝 bernoulliNormalizationE) := by
  have hρ := clusterThirdAbsoluteMoment_tendsto P Q p ε hp hplim hεp hεq hP hQ hs
  have hnz : pE * qE * (pE ^ 2 + qE ^ 2) ≠ 0 := by have := pE_pos; have := qE_pos; positivity
  exact ((clusterVariance_tendsto P Q p hplim hs).sqrt.pow 3).div hρ hnz

theorem binomial_mass_at_moving_center (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hlim : Tendsto p atTop (𝓝 pE)) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (k : ℕ → ℕ) (hk : ∀ j, k j ≤ n j) (z : ℝ)
    (hz : Tendsto (fun j => binomialZ (p j) (n j) (k j)) atTop (𝓝 z)) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * binomialWeight (p j) (n j) (k j)) atTop (𝓝 (hE * standardNormalDensity z)) := by
  have he : Tendsto (fun j => Real.sqrt (n j : ℝ) * binomialWeight (p j) (n j) (k j) -
      hE * standardNormalDensity (binomialZ (p j) (n j) (k j))) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [binomial_uniform_local_mass_pE W S B p hp hcentral hlim n hn hn2 ε hε] with j hj
    simpa only [Real.dist_eq, sub_zero] using hj (k j) (hk j)
  have hg := (standardNormalDensity_continuous.continuousAt.tendsto.comp hz).const_mul hE
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using he.add hg

theorem eventually_absorption_budget (c e q : ℕ → ℝ) (c0 : ℝ) (hc0 : 0 < c0)
    (hc : Tendsto c atTop (𝓝 c0)) (he : Tendsto e atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 0))
    (hq0 : ∀ j, 0 < q j) : ∀ᶠ j in atTop, 0 < c j ∧ e j ≤ c j / (2 * q j) := by
  filter_upwards [hc.eventually (lt_mem_nhds (by linarith : c0 / 2 < c0)),
    he.eventually (gt_mem_nhds (by linarith : 0 < c0 / 4)),
    hq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with j hjc hje hjq
  refine ⟨by linarith, (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hq0 j))).2 ?_⟩
  have h1 := mul_le_mul_of_nonneg_right hje.le (hq0 j).le
  have h2 := mul_le_mul_of_nonneg_left hjq.le (by linarith : 0 ≤ c0 / 4)
  nlinarith only [h1, h2, hjc.le]

end BerryEsseen
