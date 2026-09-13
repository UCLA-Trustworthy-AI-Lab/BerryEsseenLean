import BerryEsseen.BinomialJitterEndpoints
import BerryEsseen.ShiftedJitterExpansion

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem binomial_uniform_endpoint_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hlim : Tendsto p atTop (𝓝 pE)) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k : ℤ,
      (|Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j)) k - normalCDF (binomialZ (p j) (n j) k)) -
        edgeworthEnvelope hE (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k)| < ε) ∧
      (|Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j)) ((k : ℝ) - 1) - normalCDF (binomialZ (p j) (n j) k)) -
        edgeworthEnvelope (-hE) (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k)| < ε) := by
  let P : ℕ → StandardizedLaw := fun j => standardizedBernoulliLaw (p j) (hp j)
  have hw := standardizedBernoulli_tendsto_pE p hp hlim
  have hβ : ∀ j, thirdMoment (P j) ≤ 2 := fun j => standardizedBernoulli_third_le_two (p j) (hp j) (hcentral j)
  have hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10 := fun j => standardizedBernoulli_bounded (p j) (hp j) (hcentral j)
  have hu := bounded_jitter_shifted_expansion W S P esseenLaw hw hβ hb n hn hn2 hE hE_pos.le esseen_resonance_multiplier_zero hE
  have hl := bounded_jitter_shifted_expansion W S P esseenLaw hw hβ hb n hn hn2 hE hE_pos.le esseen_resonance_multiplier_zero (-hE)
  let L : ℕ → ℝ := fun j => Real.sqrt (p j * (1 - p j)) * hE
  have hL : Tendsto L atTop (𝓝 (1 : ℝ)) := binomial_jitter_width_tendsto p hlim
  have herror : Tendsto (fun j => (4 * cE / (2 / 5)) * |L j - 1|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero, mul_zero] using ((hL.sub_const 1).abs).const_mul (4 * cE / (2 / 5))
  have hwidth : ∀ᶠ j in atTop, L j ∈ Icc (1 / 2) 2 := by
    filter_upwards [Metric.tendsto_nhds.1 hL (1 / 2) (by norm_num)] with j hj
    rw [Real.dist_eq] at hj
    have hh := abs_lt.1 hj
    constructor <;> linarith
  intro ε hε
  filter_upwards [hu (ε / 2) (by linarith), hl (ε / 2) (by linarith), hwidth,
    herror.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hjU hjL hjwidth hjerror
  intro k
  have hn1 : 1 ≤ n j := by have := hn2 j; omega
  have hs : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by omega))
  have hJ := binomial_jitter_scaled_errors B (p j) (2 / 5) (by norm_num) (hcentral j).1
    (by linarith [(hcentral j).2]) (n j) hn1 k (L j) hjwidth
  have hU := hjU (binomialZ (p j) (n j) k)
  have hLo := hjL (binomialZ (p j) (n j) k)
  simp only [P, spanJitter, if_pos hE_pos] at hU hLo
  rw [binomial_jitter_endpoint_right (p j) (hp j) (n j) hn1 k hE hE_pos] at hU
  rw [show -hE / 2 = -(hE / 2) by ring, ← sub_eq_add_neg,
    binomial_jitter_endpoint_left (p j) (hp j) (n j) hn1 k hE hE_pos] at hLo
  have heU : |Real.sqrt (n j : ℝ) *
      (cdf (binomialMeasure (p j) (n j) ∗ uniformJitter (L j)) ((k : ℝ) + L j / 2) -
        cdf (binomialMeasure (p j) (n j)) k)| < ε / 2 := by
    rw [abs_mul, abs_of_pos hs]
    exact hJ.1.trans_lt hjerror
  have heL : |Real.sqrt (n j : ℝ) *
      (cdf (binomialMeasure (p j) (n j) ∗ uniformJitter (L j)) ((k : ℝ) - L j / 2) -
        cdf (binomialMeasure (p j) (n j)) ((k : ℝ) - 1))| < ε / 2 := by
    rw [abs_mul, abs_of_pos hs]
    exact hJ.2.trans_lt hjerror
  change |Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j) ∗ uniformJitter (L j)) ((k : ℝ) + L j / 2) -
    normalCDF (binomialZ (p j) (n j) k)) - edgeworthEnvelope hE (signedThirdMoment (P j)) (binomialZ (p j) (n j) k)| < ε / 2 at hU
  change |Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j) ∗ uniformJitter (L j)) ((k : ℝ) - L j / 2) -
    normalCDF (binomialZ (p j) (n j) k)) - edgeworthEnvelope (-hE) (signedThirdMoment (P j)) (binomialZ (p j) (n j) k)| < ε / 2 at hLo
  have hu' := abs_lt.1 hU
  have hl' := abs_lt.1 hLo
  have heu := abs_lt.1 heU
  have hel := abs_lt.1 heL
  constructor <;> rw [abs_lt] <;> constructor <;> change _ < _ <;> dsimp only [P] at * <;>
    nlinarith only [hu'.1, hu'.2, hl'.1, hl'.2, heu.1, heu.2, hel.1, hel.2]

theorem binomialMeasure_cdf_before_integer (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) (hk : k ≤ n) :
    cdf (binomialMeasure p n) ((k : ℝ) - 1) = ∑ j ∈ Finset.range k, binomialWeight p n j := by
  rw [binomialMeasure_cdf p hp]
  have he : ∀ j : ℕ, ((j : ℝ) ≤ (k : ℝ) - 1) ↔ j < k := by
    intro j
    constructor
    · intro h
      have hh : (j : ℝ) < k := by linarith
      exact_mod_cast hh
    · intro h
      have hh : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith
  simp_rw [he]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem binomialWeight_eq_cdf_jump (p : ℝ) (hp : p ∈ Icc 0 1) (n k : ℕ) (hk : k ≤ n) :
    binomialWeight p n k = cdf (binomialMeasure p n) k - cdf (binomialMeasure p n) ((k : ℝ) - 1) := by
  rw [binomialMeasure_cdf_integer p hp n k hk, binomialMeasure_cdf_before_integer p hp n k hk,
    Finset.sum_range_succ]
  ring

theorem binomial_uniform_local_mass_pE (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hlim : Tendsto p atTop (𝓝 pE)) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k : ℕ, k ≤ n j →
      |Real.sqrt (n j : ℝ) * binomialWeight (p j) (n j) k -
        hE * standardNormalDensity (binomialZ (p j) (n j) k)| < ε := by
  intro ε hε
  filter_upwards [binomial_uniform_endpoint_expansion W S B p hp hcentral hlim n hn hn2 (ε / 2) (by linarith)] with j hj
  intro k hk
  have h := hj (k : ℤ)
  simp only [Int.cast_natCast] at h
  have hu := abs_lt.1 h.1
  have hl := abs_lt.1 h.2
  rw [binomialWeight_eq_cdf_jump (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j) k hk]
  have he : hE * standardNormalDensity (binomialZ (p j) (n j) k) =
      edgeworthEnvelope hE (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k) -
      edgeworthEnvelope (-hE) (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k) := by
    unfold edgeworthEnvelope
    ring
  rw [he, abs_lt]
  constructor <;> nlinarith only [hu.1, hu.2, hl.1, hl.2]

end BerryEsseen
