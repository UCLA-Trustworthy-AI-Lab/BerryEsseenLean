import BerryEsseen.ManuscriptBinomialFourierCore
import BerryEsseen.GeneralBinomialMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem manuscript_compact_binomial_integer_mass_bound
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      binomialIntegerWeight p n k ≤ C / Real.sqrt (n : ℝ) := by
  obtain ⟨δ, hδ, hparams⟩ := compact_bernoulli_parameter_margin K hK hKI
  refine ⟨Real.sqrt (Real.pi ^ 3 / (2 * δ ^ 2)) / (2 * Real.pi), by positivity, ?_⟩
  intro p hp n hn k
  unfold binomialIntegerWeight
  split_ifs with hk
  · exact manuscript_binomial_uniform_atom_bound p δ hδ (hparams p hp).1 (hparams p hp).2 n k.toNat hn
  · positivity

theorem manuscript_compact_binomial_measure_mass_bound
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      (binomialMeasure p n).real {(k : ℝ)} ≤ C / Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := manuscript_compact_binomial_integer_mass_bound K hK hKI
  refine ⟨C, hC, ?_⟩
  intro p hp n hn k
  rw [← binomialIntegerWeight_eq_mass p ⟨(hKI hp).1.le, (hKI hp).2.le⟩ n k]
  exact hbound p hp n hn k

theorem manuscript_compact_binomial_jitter_width_bound
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      ∀ L ∈ Icc (1 / 2 : ℝ) 2,
      (Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) + L / 2) -
        cdf (binomialMeasure p n) k| ≤ C * |L - 1|) ∧
      (Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) - L / 2) -
        cdf (binomialMeasure p n) ((k : ℝ) - 1)| ≤ C * |L - 1|) := by
  obtain ⟨δ, hδ, hparams⟩ := compact_bernoulli_parameter_margin K hK hKI
  let C := Real.sqrt (Real.pi ^ 3 / (2 * δ ^ 2)) / (2 * Real.pi)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨2 * C, by positivity, ?_⟩
  intro p hp n hn k L hL
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have h := binomial_jitter_errors_of_mass_bound p ⟨(hKI hp).1.le, (hKI hp).2.le⟩ n k L hL
    (C / Real.sqrt (n : ℝ)) (by positivity)
    (fun j hj => manuscript_binomial_uniform_atom_bound p δ hδ (hparams p hp).1 (hparams p hp).2 n j hn)
  have he : Real.sqrt (n : ℝ) * (2 * |L - 1| * (C / Real.sqrt (n : ℝ))) =
      2 * C * |L - 1| := by field_simp
  constructor
  · have hm := mul_le_mul_of_nonneg_left h.1 hs.le
    rwa [he] at hm
  · have hm := mul_le_mul_of_nonneg_left h.2 hs.le
    rwa [he] at hm

end BerryEsseen
