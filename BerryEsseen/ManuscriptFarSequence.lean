import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptFarComparison
import BerryEsseen.ClusterCoefficientLimits
import BerryEsseen.GeneralClusterLimits
import BerryEsseen.ManuscriptOutsideGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Uniform ordinary binomial expansions and their uniform envelope tails.
This includes every integer k, even outside the support of the binomial law. -/
theorem manuscript_binomial_far_branches (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 pE)) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (k : ℕ → ℤ) (hz : Tendsto (fun j => |binomialZ (p j) (n j) (k j)|) atTop atTop) :
    ∀ δ > 0, ∀ᶠ j in atTop,
      max (binomialUpperBranch (p j) (n j) (k j)) (binomialLowerBranch (p j) (n j) (k j)) < δ := by
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := binomial_envelopes_uniform_tail (δ / 2) (by positivity)
  filter_upwards [general_binomial_branches W S p hp pE
    ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩ hplim n hn hn1 (δ / 2) (by positivity),
    hz.eventually_ge_atTop M] with j hj hzj
  have hu := (abs_lt.mp (hj (k j)).1).2
  have hl := (abs_lt.mp (hj (k j)).2).2
  have ht := htail (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (binomialZ (p j) (n j) (k j)) hzj
  exact max_lt (by linarith [(abs_lt.mp ht.1).2]) (by linarith [(abs_lt.mp ht.2).2])

/-- The manuscript's far-threshold step in sequential form. Inside [0,n],
the normalization, Gaussian cell shift, and leakage errors accompany ordinary
binomial envelopes. Outside [0,n], the separate zero/one baseline and
Gaussian exponential tail from the manuscript are used. -/
theorem manuscript_twoCluster_far_sequence (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hlam : Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0))
    (k : ℕ → ℤ) (hz : Tendsto (fun j => |binomialZ (p j) (n j) (k j)|) atTop atTop) :
    ∃ γ > 0, ∀ᶠ j in atTop, ∀ u : ℝ, |u| ≤ 1 / 2 →
      normalizedDiscrepancy (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)
        (((k j : ℝ) + u - (n j : ℝ) * p j) /
          Real.sqrt ((n j : ℝ) * clusterVariance (P j) (Q j) (p j))) ≤ cE - γ := by
  let s := fun j => averageNoiseVariance (P j) (Q j) (p j)
  let lam := fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)
  let v := fun j => p j * (1 - p j)
  let r := fun j => Real.sqrt (n j : ℝ)
  let A := fun j => Real.sqrt (clusterVariance (P j) (Q j) (p j)) ^ 3 /
    clusterThirdAbsoluteMoment (P j) (Q j) (p j)
  let Enorm := fun j => (56 * cE + 48 * phi0) / (v j) * r j * s j
  let Dshift := fun j => phi0 * clusterVariance (P j) (Q j) (p j) /
    (2 * clusterThirdAbsoluteMoment (P j) (Q j) (p j))
  let Eleak := fun j => 128 * cE * A j / (2 / 5) *
    (3 * (lam j / (2 / 5)) ^ 2 + ε j ^ 2 * (lam j / (2 / 5)))
  have hn1 : ∀ j, 1 ≤ n j := fun j => by have := hn2 j; omega
  have hrpos : ∀ j, 0 < r j := fun j => Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n j by have := hn2 j; omega))
  have hs : Tendsto s atTop (𝓝 0) := averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ
  have hv : Tendsto v atTop (𝓝 (pE * qE)) := hplim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hplim)
  have hvpos : 0 < pE * qE := mul_pos pE_pos qE_pos
  have hr : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hA : Tendsto A atTop (𝓝 bernoulliNormalizationE) :=
    clusterNormalization_tendsto P Q p ε hp hplim hεp hεq hP hQ hs
  have hρ := clusterThirdAbsoluteMoment_tendsto P Q p ε hp hplim hεp hεq hP hQ hs
  have hτ : 1 / 2 ≤ pE ^ 2 + qE ^ 2 := by unfold qE; nlinarith [sq_nonneg (pE - 1 / 2)]
  have hρpos : 0 < pE * qE * (pE ^ 2 + qE ^ 2) := mul_pos hvpos (by linarith)
  have hEnorm : Tendsto Enorm atTop (𝓝 0) := by
    have hcoef := ((tendsto_const_nhds (x := 56 * cE + 48 * phi0)).div hv hvpos.ne').div_atTop hr
    have he := hcoef.mul hlam
    simp only [zero_mul] at he
    apply he.congr'
    apply Eventually.of_forall
    intro j
    change ((56 * cE + 48 * phi0) / v j / r j) * lam j = Enorm j
    have hr2 : r j ^ 2 = (n j : ℝ) := Real.sq_sqrt (Nat.cast_nonneg (n j))
    dsimp only [lam, Enorm, s, accumulatedNoiseVariance, averageNoiseVariance]
    field_simp [(hrpos j).ne']
    rw [← hr2]
  have hEleak : Tendsto Eleak atTop (𝓝 0) := by
    have hb := (((hlam.div_const (2 / 5 : ℝ)).pow 2).const_mul 3).add
      ((hεlim.pow 2).mul (hlam.div_const (2 / 5 : ℝ)))
    have he := ((hA.const_mul (128 * cE)).div_const (2 / 5 : ℝ)).mul hb
    simpa only [Eleak, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_add] using he
  have hDshift : Tendsto Dshift atTop (𝓝 (phi0 / (2 * (pE ^ 2 + qE ^ 2)))) := by
    have hd := ((clusterVariance_tendsto P Q p hplim hs).const_mul phi0).div
      (hρ.const_mul 2) (mul_ne_zero (by norm_num) hρpos.ne')
    have he : phi0 * (pE * qE) / (2 * (pE * qE * (pE ^ 2 + qE ^ 2))) =
        phi0 / (2 * (pE ^ 2 + qE ^ 2)) := by
      field_simp [pE_pos.ne', qE_pos.ne']
      <;> ring
    rw [he] at hd
    exact hd
  have hDlimit : phi0 / (2 * (pE ^ 2 + qE ^ 2)) ≤ phi0 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (pE ^ 2 + qE ^ 2))).2
    nlinarith [phi0_pos]
  have hsmall : ∀ᶠ j in atTop, s j ≤ v j / 16 := by
    have h := (hv.div_const 16).sub hs
    have hpos : 0 < pE * qE / 16 - 0 := by
      simpa only [sub_zero] using div_pos hvpos (by norm_num : (0 : ℝ) < 16)
    filter_upwards [h.eventually (lt_mem_nhds hpos)] with j hj
    change 0 < v j / 16 - s j at hj
    linarith
  have hvariance : ∀ᶠ j in atTop, clusterVariance (P j) (Q j) (p j) ≤ 1 := by
    have hv1 : pE * qE < 1 := by unfold qE; nlinarith [sq_nonneg (pE - 1 / 2)]
    exact ((clusterVariance_tendsto P Q p hplim hs).eventually (gt_mem_nhds hv1)).mono
      (fun j hj => hj.le)
  have hGaussian : Tendsto (fun j => r j * A j * Real.exp (-(2 / 25) * (n j : ℝ)))
      atTop (𝓝 0) := by
    have hg := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (2 / 25)
      (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp hn)
    have hm := hg.mul hA
    simp only [zero_mul] at hm
    convert hm using 1
    funext j
    dsimp only [r, Function.comp_apply]
    rw [Real.sqrt_eq_rpow]
    ring
  have hleakbound (j : ℕ) :
      r j * A j * blockLeakageBudget (P j) (Q j) (p j) (n j) (k j) ≤ Eleak j := by
    have hApos : 0 < A j := div_pos
      (pow_pos (Real.sqrt_pos.mpr (clusterVariance_pos (P j) (Q j) (p j) (hp j))) 3)
      (clusterThirdAbsoluteMoment_pos (P j) (Q j) (p j) (hp j))
    have hqδ : (2 / 5 : ℝ) ≤ 1 - p j := by have := (hcentral j).2; linarith
    have hb := actual_twoCluster_leakage_bound B (P j) (Q j) (p j) (2 / 5) (ε j) (by norm_num)
      (hcentral j).1 hqδ (hε j) (hP j) (hQ j) (n j) (hn1 j) (k j)
    have hm := mul_le_mul_of_nonneg_left hb (mul_pos (hrpos j) hApos).le
    apply hm.trans_eq
    change r j * A j * ((128 * cE / ((2 / 5) * r j)) *
      (3 * (lam j / (2 / 5)) ^ 2 + ε j ^ 2 * (lam j / (2 / 5)))) = Eleak j
    dsimp only [Eleak]
    field_simp [(hrpos j).ne']
    <;> ring
  let γ := (cE - phi0) / 8
  have hγ : 0 < γ := by
    dsimp only [γ]
    have hce := cE_numeric_bounds.1
    have hφ := phi0_lt_two_fifths
    linarith
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [manuscript_binomial_far_branches W S p hp hplim n hn hn1 k hz γ hγ,
    hEnorm.eventually (gt_mem_nhds hγ), hEleak.eventually (gt_mem_nhds hγ),
    hDshift.eventually (gt_mem_nhds (show phi0 / (2 * (pE ^ 2 + qE ^ 2)) < phi0 + γ by linarith)),
    hsmall, hvariance, hn.eventually_ge_atTop 25,
    hGaussian.eventually (gt_mem_nhds hγ)] with j hbj hEj hLj hDj hsj hvj hnj hGj
  intro u hu
  by_cases hk : k j < 0 ∨ (n j : ℤ) < k j
  · have hcomp := manuscript_twoCluster_outside_gaussian_comparison (P j) (Q j) (p j)
      (hp j) (hcentral j) hvj (n j) hnj (k j) hk u hu
    change normalizedDiscrepancy _ _ _ ≤ r j * A j *
      (Real.exp (-(2 / 25) * (n j : ℝ)) + blockLeakageBudget (P j) (Q j) (p j) (n j) (k j)) at hcomp
    have hLb := hleakbound j
    have hφ := phi0_pos
    dsimp only [γ] at hγ hGj hLj ⊢
    nlinarith only [hcomp, hLb, hGj, hLj, hγ, hφ]
  have hcomp := manuscript_twoCluster_far_comparison B (P j) (Q j) (p j) (ε j) (hp j)
    (hεp j) (hεq j) (hP j) (hQ j) hsj (n j) (hn1 j) (k j) u hu
  change normalizedDiscrepancy _ _ _ ≤ max (binomialUpperBranch (p j) (n j) (k j))
    (binomialLowerBranch (p j) (n j) (k j)) + Enorm j + Dshift j +
      r j * A j * blockLeakageBudget (P j) (Q j) (p j) (n j) (k j) at hcomp
  have hLb := hleakbound j
  dsimp only [γ] at hγ ⊢
  dsimp only [γ] at hbj hEj hLj hDj
  linarith

end BerryEsseen
