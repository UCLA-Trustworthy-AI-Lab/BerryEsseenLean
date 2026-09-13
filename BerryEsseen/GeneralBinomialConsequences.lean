import BerryEsseen.GeneralBinomialAsymptotics
import BerryEsseen.GeneralBinomialEnvelopeTails

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem bernoulli_normalization_coefficient (p : ℝ) (hp : p ∈ Ioo 0 1) :
    Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) ∈ Ioc 0 1 := by
  have hδ : 0 < min p (1 - p) := lt_min hp.1 (sub_pos.mpr hp.2)
  have hb := bernoulli_general_parameter_bounds p (min p (1 - p)) hδ (min_le_left _ _) (min_le_right _ _)
  have hs : 0 < Real.sqrt (p * (1 - p)) := hδ.trans_le hb.2.1
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by linarith only [hb.2.2.2.1]
  refine ⟨div_pos hs hτ, (div_le_one hτ).mpr ?_⟩
  linarith only [hb.2.2.1, hb.2.2.2.1]

theorem general_binomial_branches (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ k : ℤ,
      |binomialUpperBranch (p j) (n j) k - binomialUpperEnvelope (p j) (binomialZ (p j) (n j) k)| < ε ∧
      |binomialLowerBranch (p j) (n j) k - binomialLowerEnvelope (p j) (binomialZ (p j) (n j) k)| < ε := by
  intro ε hε
  filter_upwards [general_binomial_endpoint_expansion W S p hp p₀ hp₀ hlim n hn hn1 ε hε] with j hj
  intro k
  have hA := bernoulli_normalization_coefficient (p j) (hp j)
  have hE := binomial_branch_envelope_identities (p j) (hp j) (binomialZ (p j) (n j) k)
  have hidU : binomialUpperBranch (p j) (n j) k - binomialUpperEnvelope (p j) (binomialZ (p j) (n j) k) =
      Real.sqrt (p j * (1 - p j)) / (p j ^ 2 + (1 - p j) ^ 2) *
        (Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j)) k - normalCDF (binomialZ (p j) (n j) k)) -
          edgeworthEnvelope (1 / Real.sqrt (p j * (1 - p j)))
            (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k)) := by
    rw [hE.1, binomialUpperBranch]
    simp only [one_div]
    ring
  have hidL : binomialLowerBranch (p j) (n j) k - binomialLowerEnvelope (p j) (binomialZ (p j) (n j) k) =
      -(Real.sqrt (p j * (1 - p j)) / (p j ^ 2 + (1 - p j) ^ 2) *
        (Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j)) ((k : ℝ) - 1) - normalCDF (binomialZ (p j) (n j) k)) -
          edgeworthEnvelope (-(1 / Real.sqrt (p j * (1 - p j))))
            (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k))) := by
    rw [hE.2, binomialLowerBranch]
    simp only [one_div]
    ring
  rw [hidU, hidL, abs_neg, abs_mul, abs_mul, abs_of_pos hA.1]
  constructor
  · exact ((mul_le_mul_of_nonneg_right hA.2 (abs_nonneg _)).trans_eq (one_mul _)).trans_lt (hj k).1
  · exact ((mul_le_mul_of_nonneg_right hA.2 (abs_nonneg _)).trans_eq (one_mul _)).trans_lt (hj k).2

theorem compact_binomial_branches (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |binomialUpperBranch p n k - binomialUpperEnvelope p (binomialZ p n k)| < ε ∧
      |binomialLowerBranch p n k - binomialLowerEnvelope p (binomialZ p n k)| < ε := by
  intro ε hε
  by_contra hbad
  push_neg at hbad
  choose n hn p hp k hk using fun j : ℕ => hbad (j + 1)
  obtain ⟨p₀, hp₀, u, hu, hplim⟩ := hK.tendsto_subseq hp
  have hntop : Tendsto n atTop atTop := tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hn j)) tendsto_id
  have hU := general_binomial_branches W S (p ∘ u) (fun j => hKI (hp (u j))) p₀ (hKI hp₀)
    hplim (n ∘ u) (hntop.comp hu.tendsto_atTop) (fun j => by change 1 ≤ n (u j); have := hn (u j); omega) ε hε
  obtain ⟨j, hj⟩ := hU.exists
  exact (not_lt_of_ge (hk (u j) (hj (k (u j))).1)) (hj (k (u j))).2

theorem compact_binomial_central_relative_error (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ, |binomialZ p n k| ≤ M →
      |Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
        standardNormalDensity (binomialZ p n k) - 1| < ε := by
  intro ε hε
  obtain ⟨c, hc, hgauss⟩ := gaussian_density_bounded_interval_lower M hM
  obtain ⟨N, hN⟩ := compact_binomial_local_mass W S K hK hKI (ε * c) (mul_pos hε hc)
  refine ⟨N, ?_⟩
  intro n hn p hp k hz
  have hpI := hKI hp
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (mul_pos hpI.1 (sub_pos.mpr hpI.2))
  have hs1 : Real.sqrt (p * (1 - p)) ≤ 1 := by
    nlinarith [Real.sq_sqrt (mul_nonneg hpI.1.le (sub_nonneg.mpr hpI.2.le)), sq_nonneg (p - 1 / 2)]
  have hf := standardNormalDensity_pos (binomialZ p n k)
  have he := hN n hn p hp k
  have hg := hgauss _ hz
  have hid : Real.sqrt ((n : ℝ) * p * (1 - p)) * binomialIntegerWeight p n k /
      standardNormalDensity (binomialZ p n k) - 1 =
      Real.sqrt (p * (1 - p)) / standardNormalDensity (binomialZ p n k) *
        (Real.sqrt (n : ℝ) * binomialIntegerWeight p n k -
          standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))) := by
    rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n)]
    field_simp [hs.ne', hf.ne']
    <;> ring
  rw [hid, abs_mul, abs_of_pos (div_pos hs hf), div_mul_eq_mul_div]
  apply (div_lt_iff₀ hf).mpr
  have hm := mul_le_mul_of_nonneg_right hs1 (abs_nonneg (Real.sqrt (n : ℝ) * binomialIntegerWeight p n k -
    standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))))
  have hg' := mul_le_mul_of_nonneg_left hg hε.le
  nlinarith only [hm, he, hg']

def binomialCentralLimit (p : ℝ) : ℝ :=
  phi0 * (2 - p) / (3 * (p ^ 2 + (1 - p) ^ 2))

theorem binomialUpperEnvelope_zero (p : ℝ) :
    binomialUpperEnvelope p 0 = binomialCentralLimit p := by
  unfold binomialUpperEnvelope binomialCentralLimit
  rw [standardNormalDensity_zero]
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero]
  have hτ : p ^ 2 + (1 - p) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (p - 1 / 2)]
  field_simp [hτ]
  <;> ring

theorem binomialUpperEnvelope_tendsto (p z : ℕ → ℝ) (p₀ z₀ : ℝ)
    (hp₀ : p₀ ∈ Ioo 0 1) (hp : Tendsto p atTop (𝓝 p₀)) (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun j => binomialUpperEnvelope (p j) (z j)) atTop (𝓝 (binomialUpperEnvelope p₀ z₀)) := by
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hp
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul 2)
  have hτ := (hp.pow 2).add (hq.pow 2)
  have hτ0 : p₀ ^ 2 + (1 - p₀) ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hp₀.1, sq_nonneg (1 - p₀)]
  have hφ := standardNormalDensity_continuous.continuousAt.tendsto.comp hz
  exact (hφ.div (hτ.const_mul 6) (mul_ne_zero (by norm_num) hτ0)).mul
    (((tendsto_const_nhds (x := (3 : ℝ))).add hd).sub (hd.mul (hz.pow 2)))

theorem general_binomial_nearest_z_tendsto (p : ℕ → ℝ) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (k : ℕ → ℤ) (hk : ∀ j, |(k j : ℝ) - (n j : ℝ) * p j| ≤ 1 / 2) :
    Tendsto (fun j => binomialZ (p j) (n j) (k j)) atTop (𝓝 0) := by
  have hr := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have he : Tendsto (fun j => ((k j : ℝ) - (n j : ℝ) * p j) / Real.sqrt (n j : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_) ((tendsto_const_nhds (x := (1 / 2 : ℝ))).div_atTop hr)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (hk j) (Real.sqrt_nonneg _)
  have hσ := (hplim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hplim)).sqrt
  have hs₀ : Real.sqrt (p₀ * (1 - p₀)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))).ne'
  have hz := he.div hσ hs₀
  simp only [zero_div] at hz
  convert hz using 1
  funext j
  simp only [Pi.div_apply]
  rw [binomialZ, mul_assoc (n j : ℝ) (p j) (1 - p j), Real.sqrt_mul (Nat.cast_nonneg (n j)), div_div]

theorem general_binomial_nearest_positive_branch (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (k : ℕ → ℤ) (hk : ∀ j, |(k j : ℝ) - (n j : ℝ) * p j| ≤ 1 / 2) :
    Tendsto (fun j => binomialUpperBranch (p j) (n j) (k j) - binomialCentralLimit (p j)) atTop (𝓝 0) := by
  have hz := general_binomial_nearest_z_tendsto p p₀ hp₀ hlim n hn k hk
  have henv := binomialUpperEnvelope_tendsto p (fun j => binomialZ (p j) (n j) (k j)) p₀ 0 hp₀ hlim hz
  have hcenter := binomialUpperEnvelope_tendsto p (fun _ => 0) p₀ 0 hp₀ hlim tendsto_const_nhds
  simp only [binomialUpperEnvelope_zero] at hcenter
  have herr := henv.sub hcenter
  rw [binomialUpperEnvelope_zero, sub_self] at herr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [general_binomial_branches W S p hp p₀ hp₀ hlim n hn hn1 (ε / 2) (by linarith),
    Metric.tendsto_nhds.mp herr (ε / 2) (by linarith)] with j hj he
  have hb := (hj (k j)).1
  rw [Real.dist_eq, sub_zero] at he ⊢
  have htri := abs_add_le
    (binomialUpperBranch (p j) (n j) (k j) - binomialUpperEnvelope (p j) (binomialZ (p j) (n j) (k j)))
    (binomialUpperEnvelope (p j) (binomialZ (p j) (n j) (k j)) - binomialCentralLimit (p j))
  rw [sub_add_sub_cancel] at htri
  linarith only [htri, hb, he]

theorem compact_binomial_nearest_positive_branch (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |(k : ℝ) - (n : ℝ) * p| ≤ 1 / 2 →
      |binomialUpperBranch p n k - binomialCentralLimit p| < ε := by
  intro ε hε
  by_contra hbad
  push_neg at hbad
  choose n hn p hp k hk hbadk using fun j : ℕ => hbad (j + 1)
  obtain ⟨p₀, hp₀, u, hu, hplim⟩ := hK.tendsto_subseq hp
  have hntop : Tendsto n atTop atTop := tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hn j)) tendsto_id
  have hU := general_binomial_nearest_positive_branch W S (p ∘ u) (fun j => hKI (hp (u j))) p₀ (hKI hp₀)
    hplim (n ∘ u) (hntop.comp hu.tendsto_atTop) (fun j => by change 1 ≤ n (u j); have := hn (u j); omega)
    (k ∘ u) (fun j => hk (u j))
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hU ε hε).exists
  rw [Real.dist_eq, sub_zero] at hj
  exact (not_lt_of_ge (hbadk (u j))) hj

end BerryEsseen
