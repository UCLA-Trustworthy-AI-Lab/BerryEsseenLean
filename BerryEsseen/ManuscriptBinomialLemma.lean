import BerryEsseen.ManuscriptBinomialTheorem
import BerryEsseen.GeneralBinomialEnvelopeTails
import BerryEsseen.GeneralBinomialConsequences

/-! All conclusions of manuscript Lemma 2.5, for any compact subset of (0,1).
The atom estimate uses Fourier inversion. The CDF and local expansions use
actual binomial convolutions, exact jitter endpoints, and the proved original
signed smoothing lemma. No published Berry--Esseen input is needed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_binomial_estimates
    (W : PublishedWassersteinThreeTopology)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    (∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      binomialIntegerWeight p n k ≤ C / Real.sqrt (n : ℝ)) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |Real.sqrt (n : ℝ) * binomialIntegerWeight p n k -
        standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))| < ε) ∧
    (∀ M ≥ 0, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |binomialZ p n k| ≤ M →
      |Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
        standardNormalDensity (binomialZ p n k) - 1| < ε) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |binomialUpperBranch p n k - binomialUpperEnvelope p (binomialZ p n k)| < ε ∧
      |binomialLowerBranch p n k - binomialLowerEnvelope p (binomialZ p n k)| < ε) ∧
    (∀ ε > 0, ∃ M ≥ 0, ∀ p ∈ K, ∀ z : ℝ, M ≤ |z| →
      |binomialUpperEnvelope p z| < ε ∧ |binomialLowerEnvelope p z| < ε) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |(k : ℝ) - (n : ℝ) * p| ≤ 1 / 2 →
      |binomialUpperBranch p n k - binomialCentralLimit p| < ε) := by
  refine ⟨manuscript_compact_binomial_integer_mass_bound K hK hKI,
    compact_binomial_local_mass W manuscriptSignedSmoothing K hK hKI,
    (fun M hM => compact_binomial_central_relative_error W manuscriptSignedSmoothing K hK hKI M hM),
    compact_binomial_branches W manuscriptSignedSmoothing K hK hKI, ?_,
    compact_binomial_nearest_positive_branch W manuscriptSignedSmoothing K hK hKI⟩
  intro ε hε
  obtain ⟨M, hM, htail⟩ := binomial_envelopes_uniform_tail ε hε
  refine ⟨M, hM, ?_⟩
  intro p hp z hz
  exact htail p ⟨(hKI hp).1.le, (hKI hp).2.le⟩ z hz

end BerryEsseen
