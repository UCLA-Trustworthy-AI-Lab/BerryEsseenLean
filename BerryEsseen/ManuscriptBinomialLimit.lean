import BerryEsseen.GeneralBinomialConsequences
import BerryEsseen.SmallVarianceNeighborhood
import Mathlib.Algebra.Order.Round

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_binomialCentralLimit_pE : binomialCentralLimit pE = cE := by
  have h := bernoulli_deficit_identity pE
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
  have hτ : 0 < pE ^ 2 + (1 - pE) ^ 2 := by nlinarith [sq_pos_of_pos pE_pos, sq_nonneg (1 - pE)]
  rw [binomialCentralLimit, cE_eq]
  apply (div_eq_iff (mul_ne_zero (by norm_num) hτ.ne')).mpr
  nlinarith only [congrArg (fun x : ℝ => phi0 * x / 6) h]

/-- The original nearest-integer argument shows that the actual binomial
constant approaches the Esseen constant uniformly along p_j -> p_E. -/
theorem manuscript_binomial_constant_tendsto
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1) (hplim : Tendsto p atTop (𝓝 pE))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j) :
    Tendsto (fun j => rawNormalizedConstant (bernoulliMeasure (p j)) (n j)) atTop (𝓝 cE) := by
  let k : ℕ → ℤ := fun j => round ((n j : ℝ) * p j)
  have hk : ∀ j, |(k j : ℝ) - (n j : ℝ) * p j| ≤ 1 / 2 := by
    intro j
    simpa only [k, abs_sub_comm] using abs_sub_round ((n j : ℝ) * p j)
  have hpE : pE ∈ Ioo 0 1 := ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩
  have hbranch := general_binomial_nearest_positive_branch W S p hp pE hpE hplim n hn hn1 k hk
  have hcenter := binomialUpperEnvelope_tendsto p (fun _ => 0) pE 0 hpE hplim tendsto_const_nhds
  simp only [binomialUpperEnvelope_zero, manuscript_binomialCentralLimit_pE] at hcenter
  have hlow : Tendsto (fun j => binomialUpperBranch (p j) (n j) (k j)) atTop (𝓝 cE) := by
    have h := hbranch.add hcenter
    simpa only [sub_add_cancel, zero_add] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro j
    dsimp only
    rw [rawNormalizedConstant_bernoulli (p j) (hp j) (n j) (hn1 j)]
    exact binomialUpperBranch_le_constant (p j) (hp j) (n j) (k j)
  · intro j
    dsimp only
    rw [rawNormalizedConstant_bernoulli (p j) (hp j) (n j) (hn1 j)]
    exact (binomialNormalizedConstant_lt_cE B (p j) (hp j) (n j) (hn1 j)).le

end BerryEsseen
