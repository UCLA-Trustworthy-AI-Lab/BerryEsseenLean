import BerryEsseen.EffectiveBinomial

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem compact_bernoulli_parameter_margin (K : Set ℝ) (hK : IsCompact K)
    (hKI : K ⊆ Ioo 0 1) :
    ∃ δ > 0, ∀ p ∈ K, δ ≤ p ∧ δ ≤ 1 - p := by
  obtain ⟨δ, hδ, hbound⟩ := hK.exists_forall_le'
    (f := fun p : ℝ => min p (1 - p)) (by fun_prop)
    (a := 0) (by
      intro p hp
      exact lt_min (hKI hp).1 (sub_pos.mpr (hKI hp).2))
  exact ⟨δ, hδ, fun p hp => le_min_iff.mp (hbound p hp)⟩

theorem binomialIntegerWeight_uniform_bound (B : PublishedBernoulliBound) (p δ : ℝ)
    (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ 1 - p)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    binomialIntegerWeight p n k ≤ (2 * cE / δ) / Real.sqrt (n : ℝ) := by
  have hc := cE_pos
  unfold binomialIntegerWeight
  split_ifs with hk
  · by_cases hkn : k.toNat ≤ n
    · convert binomialWeight_uniform_bound B p δ hδ hp hq n k.toNat hn hkn using 1 <;> ring
    · simp only [binomialWeight, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn), Nat.cast_zero, zero_mul]
      positivity
  · positivity

/-- The atom bound in Lemma `binomial-estimates`, with all compact parameter
sets and all integer indices. Its atom estimate is now proved by Fourier
inversion; the legacy published-bound parameter is unused by that proof. -/
theorem compact_binomial_integer_mass_bound (B : PublishedBernoulliBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      binomialIntegerWeight p n k ≤ C / Real.sqrt (n : ℝ) := by
  have hc := cE_pos
  obtain ⟨δ, hδ, hparams⟩ := compact_bernoulli_parameter_margin K hK hKI
  refine ⟨2 * cE / δ, by positivity, ?_⟩
  intro p hp n hn k
  exact binomialIntegerWeight_uniform_bound B p δ hδ (hparams p hp).1 (hparams p hp).2 n hn k

/-- The same uniform bound stated directly for the actual binomial measure. -/
theorem compact_binomial_measure_mass_bound (B : PublishedBernoulliBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      (binomialMeasure p n).real {(k : ℝ)} ≤ C / Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := compact_binomial_integer_mass_bound B K hK hKI
  refine ⟨C, hC, ?_⟩
  intro p hp n hn k
  rw [← binomialIntegerWeight_eq_mass p ⟨(hKI hp).1.le, (hKI hp).2.le⟩ n k]
  exact hbound p hp n hn k

theorem compact_binomial_jitter_width_bound (B : PublishedBernoulliBound)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∃ C > 0, ∀ p ∈ K, ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
      ∀ L ∈ Icc (1 / 2 : ℝ) 2,
      (Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) + L / 2) -
        cdf (binomialMeasure p n) k| ≤ C * |L - 1|) ∧
      (Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) - L / 2) -
        cdf (binomialMeasure p n) ((k : ℝ) - 1)| ≤ C * |L - 1|) := by
  have hc := cE_pos
  obtain ⟨δ, hδ, hparams⟩ := compact_bernoulli_parameter_margin K hK hKI
  refine ⟨4 * cE / δ, by positivity, ?_⟩
  intro p hp n hn k L hL
  exact binomial_jitter_scaled_errors B p δ hδ (hparams p hp).1 (hparams p hp).2 n hn k L hL

theorem gaussian_density_bounded_interval_lower (M : ℝ) (hM : 0 ≤ M) :
    ∃ c > 0, ∀ z : ℝ, |z| ≤ M → c ≤ standardNormalDensity z := by
  refine ⟨phi0 * Real.exp (-M ^ 2 / 2), mul_pos phi0_pos (Real.exp_pos _), ?_⟩
  intro z hz
  rw [standardNormalDensity_formula]
  apply mul_le_mul_of_nonneg_left _ phi0_pos.le
  apply Real.exp_le_exp.mpr
  have hsq := (sq_le_sq₀ (abs_nonneg z) hM).mpr hz
  rw [sq_abs] at hsq
  linarith only [hsq]

end BerryEsseen
