import BerryEsseen.ManuscriptBinomialLimit
import BerryEsseen.BernoulliLimits
import BerryEsseen.PublishedEsseenFixedLawAsymptotic
import BerryEsseen.ManuscriptSmoothingInstance

/-! Independent optimality of c_E from the fixed Esseen Bernoulli law.
The `original_manuscript_` endpoints use exactly the manuscript's cited
classical fixed-law asymptotic. The other endpoints provide an additional
proof from this paper's binomial expansion and Schulz's bound. This extra
proof is not claimed to be the manuscript's original proof route.
The sample-size bound/main theorem is not used anywhere in this file. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- Fixed-law convergence, obtained from the original nearest-integer
binomial expansion and Schulz's bound rather than the final main theorem. -/
theorem manuscript_esseen_constant_tendsto
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) :
    Tendsto (fun j : ℕ => sSup (range (normalizedDiscrepancy esseenLaw (j + 1))))
      atTop (𝓝 cE) := by
  have hpE : pE ∈ Ioo (0 : ℝ) 1 := ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩
  have hlim := manuscript_binomial_constant_tendsto W S B (fun _ => pE) (fun _ => hpE)
    tendsto_const_nhds (fun j => j + 1) (tendsto_add_atTop_nat 1) (fun j => by change 1 ≤ j + 1; omega)
  have he (j : ℕ) : rawNormalizedConstant (bernoulliMeasure pE) (j + 1) =
      sSup (range (normalizedDiscrepancy esseenLaw (j + 1))) := by
    rw [rawNormalizedConstant_bernoulli pE hpE (j + 1) (by omega),
      binomialNormalizedConstant_eq_sup pE hpE (j + 1) (by omega), standardizedBernoulli_pE]
  simpa only [he] using hlim

/-- Every smaller coefficient fails on the same fixed Esseen two-point law
at an arbitrarily large positive sample size. -/
def ManuscriptSharpnessClaim : Prop :=
  ∀ c : ℝ, c < cE → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∃ x : ℝ, c < normalizedDiscrepancy esseenLaw n x

/-- The original sharpness argument following eq:esseen-limit and the
introduction: a fixed Esseen law excludes every smaller coefficient,
regardless of how large the lower sample-size threshold is taken. -/
theorem original_manuscript_sharpness (E : PublishedEsseenFixedLawAsymptotic) :
    ManuscriptSharpnessClaim := by
  intro c hc N
  have hlim := original_manuscript_esseen_constant_tendsto E
  have hev : ∀ᶠ n : ℕ in atTop,
      c < sSup (range (normalizedDiscrepancy esseenLaw n)) :=
    hlim.eventually (Ioi_mem_nhds hc)
  obtain ⟨n, hn, hlarge⟩ := (hev.and (eventually_ge_atTop (max N 1))).exists
  obtain ⟨r, hr, hcr⟩ := exists_lt_of_lt_csSup
    (range_nonempty (normalizedDiscrepancy esseenLaw n)) hn
  obtain ⟨x, rfl⟩ := hr
  exact ⟨n, le_trans (le_max_left _ _) hlarge,
    le_trans (le_max_right _ _) hlarge, x, hcr⟩

/-- Original sharpness in the paper's unnormalized discrepancy convention. -/
theorem original_manuscript_sharpness_discrepancy
    (E : PublishedEsseenFixedLawAsymptotic)
    (c : ℝ) (hc : c < cE) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∃ x : ℝ,
      c * thirdMoment esseenLaw / Real.sqrt (n : ℝ) < discrepancy esseenLaw n x := by
  obtain ⟨n, hN, hn, x, hx⟩ := original_manuscript_sharpness E c hc N
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  refine ⟨n, hN, hn, x, ?_⟩
  unfold normalizedDiscrepancy at hx
  have hh := (lt_div_iff₀ (thirdMoment_pos esseenLaw)).mp hx
  apply (div_lt_iff₀ hroot).mpr
  nlinarith only [hh]

/-- Additional independent proof using the paper's binomial expansion. -/
theorem manuscript_sharpness (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) :
    ManuscriptSharpnessClaim := by
  intro c hc N
  have hlim := manuscript_esseen_constant_tendsto W S B
  have hev : ∀ᶠ j : ℕ in atTop,
      c < sSup (range (normalizedDiscrepancy esseenLaw (j + 1))) :=
    hlim.eventually (Ioi_mem_nhds hc)
  obtain ⟨j, hj, hlarge⟩ := (hev.and (eventually_ge_atTop N)).exists
  obtain ⟨r, hr, hcr⟩ := exists_lt_of_lt_csSup
    (range_nonempty (normalizedDiscrepancy esseenLaw (j + 1))) hj
  obtain ⟨x, rfl⟩ := hr
  exact ⟨j + 1, by omega, by omega, x, hcr⟩

/-- The same optimality assertion in the paper's original Berry--Esseen
inequality normalization. -/
theorem manuscript_sharpness_discrepancy
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (c : ℝ) (hc : c < cE) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧ ∃ x : ℝ,
      c * thirdMoment esseenLaw / Real.sqrt (n : ℝ) < discrepancy esseenLaw n x := by
  obtain ⟨n, hN, hn, x, hx⟩ := manuscript_sharpness W S B c hc N
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  refine ⟨n, hN, hn, x, ?_⟩
  unfold normalizedDiscrepancy at hx
  have hh := (lt_div_iff₀ (thirdMoment_pos esseenLaw)).mp hx
  apply (div_lt_iff₀ hroot).mpr
  nlinarith only [hh]

/-- The additional binomial proof with the signed smoothing lemma fully
discharged by its proved sinc-fourth-power implementation. -/
theorem manuscript_sharpness_from_proved_smoothing
    (W : PublishedWassersteinThreeTopology) (B : PublishedBernoulliBound) :
    ManuscriptSharpnessClaim :=
  manuscript_sharpness W manuscriptSignedSmoothing B

end BerryEsseen
