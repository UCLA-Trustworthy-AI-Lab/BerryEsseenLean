import BerryEsseen.ManuscriptBinomialEffective
import BerryEsseen.ManuscriptSmoothingInstance

/-! The manuscript's effective binomial lemma with its original proof constants
and cutoffs, instantiated with the proved sinc⁴ smoothing theorem. No external
Berry--Esseen or smoothing premise occurs in these conclusions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_binomial_jitter (p T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hT : 10 ≤ T)
    (n : ℕ) (hn : 1000000 ≤ n) (x : ℝ) :
    manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 T :=
  effective_binomial_jitter manuscriptSignedSmoothing p T hp hT n hn x

theorem manuscript_binomial_jitter_twelve (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (x : ℝ) :
    manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 ((10 : ℝ) ^ 12) :=
  manuscript_binomial_jitter p _ hp (by norm_num) n (by omega) x

theorem manuscript_binomial_jitter_exp (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (x : ℝ) :
    manuscriptBinomialJitterError p hp n x ≤ effectiveClusterError n 0 (Real.exp 200) :=
  manuscript_binomial_jitter p _ hp
    (by linarith [Real.add_one_le_exp (200 : ℝ)]) n (by omega) x

theorem manuscript_effective_binomial_central (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (k : ℕ) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    (0.99 : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k /
      standardNormalDensity (binomialZ p n k) ∧
    Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialWeight p n k /
      standardNormalDensity (binomialZ p n k) ≤ 1.01 ∧
    (1 / (10 : ℝ) ^ 6) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k :=
  manuscript_binomial_central_of_jitter p hp n hn
    (manuscript_binomial_jitter_twelve p hp n hn) k hk hz

theorem manuscript_effective_binomial_wide (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (k : ℕ) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 11) :
    Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k :=
  manuscript_binomial_wide_of_jitter p hp n hn
    (manuscript_binomial_jitter_exp p hp n hn) k hk hz

theorem manuscript_effective_binomial_integer_central (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ)
    (hz : |binomialZ p n k| ≤ 5) :
    (0.99 : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) ∧
    Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) ≤ 1.01 ∧
    (1 / (10 : ℝ) ^ 6) / Real.sqrt (n : ℝ) ≤ binomialIntegerWeight p n k :=
  manuscript_binomial_integer_central_of_jitter p hp n hn
    (manuscript_binomial_jitter_twelve p hp n hn) k hz

theorem manuscript_effective_binomial_integer_wide (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ)
    (hz : |binomialZ p n k| ≤ 11) :
    Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialIntegerWeight p n k :=
  manuscript_binomial_integer_wide_of_jitter p hp n hn
    (manuscript_binomial_jitter_exp p hp n hn) k hz

theorem manuscript_effective_binomial_branches (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) (k : ℤ) :
    |binomialUpperBranch p n k - binomialUpperEnvelope p (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10 ∧
    |binomialLowerBranch p n k - binomialLowerEnvelope p (binomialZ p n k)| ≤ 2 / (10 : ℝ) ^ 10 :=
  manuscript_binomial_branches_of_jitter p hp n hn
    (manuscript_binomial_jitter_twelve p hp n hn) k

theorem manuscript_effective_binomial_constant_lower (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 10 ^ 100 ≤ n) :
    binomialCentralLimit p - 3 / (10 : ℝ) ^ 10 ≤ binomialNormalizedConstant p n ∧
    (0.39 : ℝ) < binomialNormalizedConstant p n :=
  manuscript_binomial_constant_lower_of_jitter p hp n hn
    (manuscript_binomial_jitter_twelve p hp n hn)

theorem manuscript_effective_binomial_mass_sup (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n : ℕ) (hn : 1 ≤ n) :
    sSup (Set.range (binomialIntegerWeight p n)) ≤ 2 / Real.sqrt (n : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨k, rfl⟩
  unfold binomialIntegerWeight
  split_ifs with hk
  · exact manuscript_effective_binomial_mass_upper p hp n k.toNat hn
  · positivity

end BerryEsseen
