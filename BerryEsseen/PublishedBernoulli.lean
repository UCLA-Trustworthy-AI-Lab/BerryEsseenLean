import BerryEsseen.BinomialMeasure
import BerryEsseen.ManuscriptBinomialFourierCore
import BerryEsseen.Attainment

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def binomialKolmogorov (p : ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (fun t : ℝ => |cdf (binomialMeasure p n) t -
    normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))|))

/-- Schulz (2016), dissertation, Theorem 1, printed p. 1 (PDF p. 11).
The published strict bound is an explicit external premise; no manuscript
local stability result is included in this structure. -/
structure PublishedBernoulliBound : Prop where
  strict_bound : ∀ (p : ℝ), p ∈ Ioo 0 1 → ∀ (n : ℕ), 1 ≤ n →
    binomialKolmogorov p n <
      cE * (p ^ 2 + (1 - p) ^ 2) / Real.sqrt ((n : ℝ) * p * (1 - p))

theorem binomialDiscrepancy_le_one (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    |cdf (binomialMeasure p n) t - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| ≤ 1 := by
  letI := binomialMeasure_probability p hp n
  have hF0 := cdf_nonneg (binomialMeasure p n) t
  have hF1 := cdf_le_one (binomialMeasure p n) t
  have hG0 := cdf_nonneg (gaussianReal 0 1) ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))
  have hG1 := cdf_le_one (gaussianReal 0 1) ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))
  rw [cdf_eq_real] at hG0 hG1
  change 0 ≤ normalCDF _ at hG0
  change normalCDF _ ≤ 1 at hG1
  rw [abs_le]
  constructor <;> linarith

theorem binomialDiscrepancy_le_Kolmogorov (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    |cdf (binomialMeasure p n) t - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| ≤
      binomialKolmogorov p n := by
  apply le_csSup (a := |cdf (binomialMeasure p n) t - _|) ?_ (Set.mem_range_self t)
  exact ⟨1, by rintro _ ⟨x, rfl⟩; exact binomialDiscrepancy_le_one p hp n x⟩

theorem binomialKolmogorov_nonneg (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    0 ≤ binomialKolmogorov p n := (abs_nonneg _).trans (binomialDiscrepancy_le_Kolmogorov p hp n 0)

theorem published_binomial_pointwise_bound (S : PublishedBernoulliBound) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    |cdf (binomialMeasure p n) t - normalCDF ((t - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| <
      cE * (p ^ 2 + (1 - p) ^ 2) / Real.sqrt ((n : ℝ) * p * (1 - p)) :=
  (binomialDiscrepancy_le_Kolmogorov p ⟨hp.1.le, hp.2.le⟩ n t).trans_lt (S.strict_bound p hp n hn)

theorem binomialMeasure_cdf_below_integer (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ)
    (hk : k ≤ n) (r : ℝ) (hr : r ∈ Ioo 0 1) :
    cdf (binomialMeasure p n) ((k : ℝ) - r) = ∑ j ∈ Finset.range k, binomialWeight p n j := by
  rw [binomialMeasure_cdf p hp]
  have he : ∀ j : ℕ, ((j : ℝ) ≤ (k : ℝ) - r) ↔ j < k := by
    intro j
    constructor
    · intro h
      have hlt : (j : ℝ) < k := by linarith [hr.1]
      exact_mod_cast hlt
    · intro h
      have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith [hr.2]
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem binomial_left_branch_le_Kolmogorov (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) (hk : k ≤ n) :
    |(∑ j ∈ Finset.range k, binomialWeight p n j) -
      normalCDF (((k : ℝ) - n * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))| ≤ binomialKolmogorov p n := by
  have hr : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    simpa only [one_div] using hh.inv_tendsto_atTop
  have hg : Tendsto (fun m : ℕ => |(∑ j ∈ Finset.range k, binomialWeight p n j) -
      normalCDF ((((k : ℝ) - 1 / ((m : ℝ) + 2)) - n * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))|)
      atTop (𝓝 (|(∑ j ∈ Finset.range k, binomialWeight p n j) -
      normalCDF (((k : ℝ) - n * p) / Real.sqrt ((n : ℝ) * p * (1 - p)))|)) := by
    have ht := (((tendsto_const_nhds (x := (k : ℝ))).sub hr).sub (tendsto_const_nhds (x := (n : ℝ) * p))).div_const
      (Real.sqrt ((n : ℝ) * p * (1 - p)))
    have hG := normalCDF_continuous.continuousAt.tendsto.comp ht
    simpa only [sub_zero] using ((tendsto_const_nhds (x := ∑ j ∈ Finset.range k, binomialWeight p n j)).sub hG).abs
  apply le_of_tendsto hg
  filter_upwards [] with m
  have hrm : 1 / ((m : ℝ) + 2) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_lt_one (by positivity : (0 : ℝ) < (m : ℝ) + 2)).2
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
  have h := binomialDiscrepancy_le_Kolmogorov p hp n ((k : ℝ) - 1 / ((m : ℝ) + 2))
  rw [binomialMeasure_cdf_below_integer p hp n k hk _ hrm] at h
  exact h

theorem binomialWeight_le_twice_Kolmogorov (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) (hk : k ≤ n) :
    binomialWeight p n k ≤ 2 * binomialKolmogorov p n := by
  have hleft := abs_le.1 (binomial_left_branch_le_Kolmogorov p hp n k hk)
  have hright := abs_le.1 (binomialDiscrepancy_le_Kolmogorov p hp n k)
  rw [binomialMeasure_cdf_integer p hp n k hk, Finset.sum_range_succ] at hright
  linarith

/-- Compatibility bound obtained from the manuscript Fourier atom estimate.
The legacy Bernoulli-bound parameter is unused. -/
theorem binomialWeight_uniform_bound (_S : PublishedBernoulliBound) (p δ : ℝ)
    (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ 1 - p)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    binomialWeight p n k ≤ 2 * cE / (δ * Real.sqrt (n : ℝ)) := by
  have h := manuscript_binomial_uniform_atom_bound p δ hδ hp hq n k hn
  have hc := manuscript_binomial_uniform_atom_coefficient δ hδ
  have hnR : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr
    (by exact_mod_cast (show 0 < n by omega))
  apply (h.trans (div_le_div_of_nonneg_right hc hnR.le)).trans
  have hconst : (3 / 4 : ℝ) ≤ 2 * cE := by linarith [cE_numeric_bounds.1]
  have hdiv := div_le_div_of_nonneg_right hconst (mul_pos hδ hnR).le
  convert hdiv using 1 <;> ring

end BerryEsseen
