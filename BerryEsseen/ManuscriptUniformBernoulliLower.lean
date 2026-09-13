import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptSmallVarianceSetup

/-! The uniform Bernoulli lower bound used in the original Lemma 3.3.
First shrink the parameter interval by continuity of g at p_E, then use
the compact nearest-integer branch expansion, and finally include the
actual branch in the actual Kolmogorov supremum. No local stability
conclusion or main theorem is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_binomialCentralLimit_continuous : Continuous binomialCentralLimit := by
  unfold binomialCentralLimit
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro p
  have hp : 0 < p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_nonneg (p - 1 / 2)]
  positivity

/-- The original order of choices: fix the desired loss, shrink I around
p_E by continuity of g, then choose a uniform sample-size bound from the
nearest-integer expansion on that compact I. -/
theorem manuscript_uniform_bernoulli_lower (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ d : ℝ, 0 < d ∧ d < manuscriptParameterRadius ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, |p - pE| ≤ d →
        ∀ n : ℕ, N ≤ n → cE - γ ≤ rawNormalizedConstant (bernoulliMeasure p) n := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    manuscript_binomialCentralLimit_continuous.continuousAt (γ / 2) (by linarith)
  let d : ℝ := min manuscriptParameterRadius δ / 2
  have hd : 0 < d := div_pos (lt_min manuscriptParameterRadius_pos hδ) (by norm_num)
  have hdm : d < manuscriptParameterRadius := by
    have hh := min_le_left manuscriptParameterRadius δ
    dsimp only [d] at *
    linarith
  have hdδ : d < δ := by
    have hh := min_le_right manuscriptParameterRadius δ
    dsimp only [d] at *
    linarith
  let K : Set ℝ := Icc (pE - d) (pE + d)
  have hKI : K ⊆ Ioo (0 : ℝ) 1 := by
    intro p hp
    have hclose : |p - pE| ≤ d := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have hb := (manuscript_small_parameter_bounds d p hdm.le hclose).1
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  obtain ⟨N₀, hN₀⟩ := compact_binomial_nearest_positive_branch W S K isCompact_Icc hKI
    (γ / 2) (by linarith)
  refine ⟨d, hd, hdm, max N₀ 2, le_max_right _ _, ?_⟩
  intro p hp n hn
  have hpK : p ∈ K := ⟨by linarith [(abs_le.mp hp).1], by linarith [(abs_le.mp hp).2]⟩
  have hpI := hKI hpK
  have hg := hcont (show dist p pE < δ by simpa only [Real.dist_eq] using hp.trans_lt hdδ)
  rw [Real.dist_eq, manuscript_binomialCentralLimit_pE] at hg
  let k : ℤ := round ((n : ℝ) * p)
  have hk : |(k : ℝ) - (n : ℝ) * p| ≤ 1 / 2 := by
    simpa only [k, abs_sub_comm] using abs_sub_round ((n : ℝ) * p)
  have hb := hN₀ n ((le_max_left _ _).trans hn) p hpK k hk
  have hn1 : 1 ≤ n := by have h := (le_max_right N₀ 2).trans hn; omega
  rw [rawNormalizedConstant_bernoulli p hpI n hn1]
  have hsup := binomialUpperBranch_le_constant p hpI n k
  linarith [(abs_lt.mp hg).1, (abs_lt.mp hb).1]

end BerryEsseen
