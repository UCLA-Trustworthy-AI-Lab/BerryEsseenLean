import BerryEsseen.GeneralBernoulliLimits
import BerryEsseen.GeneralJitterExpansion
import BerryEsseen.GeneralJitterEnvelopes

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem general_jitter_moving_shift_expansion (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (K : ℝ) (hκ : ∀ j, |signedThirdMoment (P j)| ≤ K)
    (w a : ℕ → ℝ) (a₀ : ℝ) (ha : Tendsto a atTop (𝓝 a₀))
    (hU : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) (w j) x)
      (fun _ => 0) atTop) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ x : ℝ,
      |Real.sqrt (n j : ℝ) *
        (cdf (iidSumLaw (P j).measure (n j) ∗ spanJitter (w j))
          (Real.sqrt (n j : ℝ) * x + a j / 2) - normalCDF x) -
        edgeworthEnvelope (a j) (signedThirdMoment (P j)) x| < ε := by
  have hCt : Tendsto (fun j => generalEdgeworthShiftConstant K (a j)) atTop
      (𝓝 (generalEdgeworthShiftConstant K a₀)) := by
    exact (((ha.pow 2).const_mul 3).div_const 8 |>.add ((ha.abs.const_mul (3 * K)).div_const 2)).const_mul phi0
  have hC := hCt.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hU (ε / 2) (by linarith),
    hC.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hjU hjC
  intro x
  have hs : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n j by have := hn1 j; omega))
  have hp := general_edgeworthCDF_shift_remainder (n j) (hn1 j) (signedThirdMoment (P j)) (a j) x K (hκ j)
  have herr : |Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) (w j)
      (x + a j / (2 * Real.sqrt (n j : ℝ)))| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjU (x + a j / (2 * Real.sqrt (n j : ℝ)))
  unfold jitterCDFError at herr
  rw [normalized_jitter_cdf_as_raw (P j) (n j) (hn1 j)] at herr
  have he : Real.sqrt (n j : ℝ) * (x + a j / (2 * Real.sqrt (n j : ℝ))) =
      Real.sqrt (n j : ℝ) * x + a j / 2 := by field_simp [hs.ne']
  rw [he] at herr
  have hsmall := hp.trans_lt hjC
  rcases abs_lt.mp herr with ⟨hl, hu⟩
  rcases abs_lt.mp hsmall with ⟨hl', hu'⟩
  rw [abs_lt]
  constructor <;> linarith only [hl, hu, hl', hu']

theorem binomial_unit_jitter_endpoints (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ) :
    cdf (binomialMeasure p n ∗ uniformJitter 1) ((k : ℝ) + 1 / 2) = cdf (binomialMeasure p n) k ∧
    cdf (binomialMeasure p n ∗ uniformJitter 1) ((k : ℝ) - 1 / 2) = cdf (binomialMeasure p n) ((k : ℝ) - 1) := by
  have hu := binomial_jitter_right_error p hp n k 1 (by norm_num)
  have hl := binomial_jitter_left_error p hp n k 1 (by norm_num)
  simp only [sub_self, abs_zero, zero_div, zero_mul] at hu hl
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hu (abs_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hl (abs_nonneg _)))⟩

theorem general_binomial_endpoint_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ k : ℤ,
      |Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j)) k - normalCDF (binomialZ (p j) (n j) k)) -
        edgeworthEnvelope (1 / Real.sqrt (p j * (1 - p j)))
          (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k)| < ε ∧
      |Real.sqrt (n j : ℝ) * (cdf (binomialMeasure (p j) (n j)) ((k : ℝ) - 1) - normalCDF (binomialZ (p j) (n j) k)) -
        edgeworthEnvelope (-(1 / Real.sqrt (p j * (1 - p j))))
          (signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) (binomialZ (p j) (n j) k)| < ε := by
  let P : ℕ → StandardizedLaw := fun j => standardizedBernoulliLaw (p j) (hp j)
  let Q := standardizedBernoulliLaw p₀ hp₀
  let w : ℕ → ℝ := fun j => 1 / Real.sqrt (p j * (1 - p j))
  let h := 1 / Real.sqrt (p₀ * (1 - p₀))
  have hs (j : ℕ) : 0 < Real.sqrt (p j * (1 - p j)) := Real.sqrt_pos.mpr (mul_pos (hp j).1 (sub_pos.mpr (hp j).2))
  have hs₀ : 0 < Real.sqrt (p₀ * (1 - p₀)) := Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))
  have hw : Tendsto w atTop (𝓝 h) := tendsto_const_nhds.div
    ((hlim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim)).sqrt) hs₀.ne'
  have hκlim := standardizedBernoulli_signed_third_tendsto p hp p₀ hp₀ hlim
  obtain ⟨K, hK⟩ := hκlim.abs.bddAbove_range
  have hκ : ∀ j, |signedThirdMoment (P j)| ≤ K := fun j => hK ⟨j, rfl⟩
  have hJ := general_variable_jitter_uniform_expansion W S P Q
    (standardizedBernoulli_tendsto p hp p₀ hp₀ hlim)
    (standardizedBernoulli_third_tendsto p hp p₀ hp₀ hlim) n hn h (one_div_pos.mpr hs₀).le
    (standardizedBernoulli_resonance_multiplier_zero p₀ hp₀) w (fun j => (one_div_pos.mpr (hs j)).le) hw
  have hu := general_jitter_moving_shift_expansion P n hn hn1 K hκ w w h hw hJ
  have hl := general_jitter_moving_shift_expansion P n hn hn1 K hκ w (fun j => -(w j)) (-h) hw.neg hJ
  intro ε hε
  filter_upwards [hu ε hε, hl ε hε] with j hjU hjL
  intro k
  have hwj : 0 < w j := one_div_pos.mpr (hs j)
  have he : Real.sqrt (p j * (1 - p j)) * w j = 1 := by dsimp [w]; exact mul_one_div_cancel (hs j).ne'
  have hu' := hjU (binomialZ (p j) (n j) k)
  have hl' := hjL (binomialZ (p j) (n j) k)
  simp only [P, spanJitter, if_pos hwj] at hu' hl'
  rw [binomial_jitter_endpoint_right (p j) (hp j) (n j) (hn1 j) k (w j) hwj, he,
    (binomial_unit_jitter_endpoints (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j) k).1] at hu'
  rw [show -(w j) / 2 = -(w j / 2) by ring, ← sub_eq_add_neg,
    binomial_jitter_endpoint_left (p j) (hp j) (n j) (hn1 j) k (w j) hwj, he,
    (binomial_unit_jitter_endpoints (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j) k).2] at hl'
  exact ⟨hu', hl'⟩

theorem binomialIntegerWeight_eq_cdf_jump (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ) :
    binomialIntegerWeight p n k = cdf (binomialMeasure p n) k - cdf (binomialMeasure p n) ((k : ℝ) - 1) := by
  classical
  rw [binomialMeasure_cdf p hp, binomialMeasure_cdf p hp, ← Finset.sum_sub_distrib]
  have he : ∀ j : ℕ, (if (j : ℝ) ≤ (k : ℝ) then binomialWeight p n j else 0) -
      (if (j : ℝ) ≤ (k : ℝ) - 1 then binomialWeight p n j else 0) =
      if (j : ℤ) = k then binomialWeight p n j else 0 := by
    intro j
    have hle (m : ℤ) : ((j : ℝ) ≤ (m : ℝ)) ↔ (j : ℤ) ≤ m := by norm_cast
    rw [show (k : ℝ) - 1 = ((k - 1 : ℤ) : ℝ) by push_cast; rfl]
    simp only [hle]
    by_cases h : (j : ℤ) ≤ k - 1
    · simp [h, show (j : ℤ) ≤ k by omega, show (j : ℤ) ≠ k by omega]
    · by_cases h' : (j : ℤ) = k
      · simp [h, h']
      · simp [h, h', show ¬(j : ℤ) ≤ k by omega]
  simp_rw [he]
  unfold binomialIntegerWeight
  by_cases hk : 0 ≤ k
  · rw [if_pos hk]
    have heq : ∀ j : ℕ, ((j : ℤ) = k) ↔ j = k.toNat := by intro j; omega
    simp_rw [heq]
    by_cases hkn : k.toNat ≤ n
    · simp [hkn, Nat.lt_succ_iff]
    · simp [hkn, Nat.lt_succ_iff, binomialWeight, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn)]
  · rw [if_neg hk]
    have hne : ∀ j : ℕ, (j : ℤ) ≠ k := by intro j; omega
    simp only [hne, if_false, Finset.sum_const_zero]

theorem general_binomial_local_mass (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ k : ℤ,
      |Real.sqrt (n j : ℝ) * binomialIntegerWeight (p j) (n j) k -
        standardNormalDensity (binomialZ (p j) (n j) k) / Real.sqrt (p j * (1 - p j))| < ε := by
  intro ε hε
  filter_upwards [general_binomial_endpoint_expansion W S p hp p₀ hp₀ hlim n hn hn1 (ε / 2) (by linarith)] with j hj
  intro k
  have hu := abs_lt.mp (hj k).1
  have hl := abs_lt.mp (hj k).2
  rw [binomialIntegerWeight_eq_cdf_jump (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j) k]
  unfold edgeworthEnvelope at hu hl
  simp only [div_eq_mul_inv] at hu hl ⊢
  rw [abs_lt]
  constructor <;> nlinarith only [hu.1, hu.2, hl.1, hl.2]

theorem compact_binomial_local_mass (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ K, ∀ k : ℤ,
      |Real.sqrt (n : ℝ) * binomialIntegerWeight p n k -
        standardNormalDensity (binomialZ p n k) / Real.sqrt (p * (1 - p))| < ε := by
  intro ε hε
  by_contra hbad
  push_neg at hbad
  choose n hn p hp k hk using fun j : ℕ => hbad (j + 1)
  obtain ⟨p₀, hp₀, u, hu, hplim⟩ := hK.tendsto_subseq hp
  have hntop : Tendsto n atTop atTop := tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hn j)) tendsto_id
  have hU := general_binomial_local_mass W S (p ∘ u) (fun j => hKI (hp (u j))) p₀ (hKI hp₀)
    hplim (n ∘ u) (hntop.comp hu.tendsto_atTop) (fun j => by change 1 ≤ n (u j); have := hn (u j); omega) ε hε
  obtain ⟨j, hj⟩ := hU.exists
  exact (not_lt_of_ge (hk (u j))) (hj (k (u j)))

theorem compact_binomial_central_lower_bound (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (K : Set ℝ) (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ p ∈ K, ∀ n ≥ N, ∀ k : ℕ, k ≤ n →
      |(k : ℝ) - (n : ℝ) * p| ≤ M * Real.sqrt (n : ℝ) →
      c / Real.sqrt (n : ℝ) ≤ binomialWeight p n k := by
  obtain ⟨δ, hδ, hmargin⟩ := compact_bernoulli_parameter_margin K hK hKI
  obtain ⟨c, hc, hgauss⟩ := gaussian_density_bounded_interval_lower (M / δ) (div_nonneg hM hδ.le)
  obtain ⟨N, hN⟩ := compact_binomial_local_mass W S K hK hKI (c / 2) (by positivity)
  refine ⟨c / 2, by positivity, max N 1, le_max_right _ _, ?_⟩
  intro p hp n hn k hk hcentral
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hpar := bernoulli_general_parameter_bounds p δ hδ (hmargin p hp).1 (hmargin p hp).2
  have hs : 0 < Real.sqrt (p * (1 - p)) := hδ.trans_le hpar.2.1
  have hz : |binomialZ p n (k : ℤ)| ≤ M / δ := by
    rw [binomialZ, Int.cast_natCast, abs_div,
      mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n), abs_of_pos (mul_pos hr hs)]
    apply (div_le_iff₀ (mul_pos hr hs)).mpr
    have hm := mul_le_mul_of_nonneg_left hpar.2.1 (div_nonneg hM hδ.le)
    have hscale : M ≤ (M / δ) * Real.sqrt (p * (1 - p)) := by
      have he : (M / δ) * δ = M := div_mul_cancel₀ M hδ.ne'
      rw [he] at hm
      exact hm
    have hb := mul_le_mul_of_nonneg_right hscale hr.le
    nlinarith only [hcentral, hb]
  have hg := hgauss _ hz
  have he := (abs_lt.mp (hN n ((le_max_left N 1).trans hn) p hp (k : ℤ))).1
  simp only [binomialIntegerWeight, Int.natCast_nonneg, if_true, Int.toNat_natCast] at he
  have hgf : c ≤ standardNormalDensity (binomialZ p n (k : ℤ)) / Real.sqrt (p * (1 - p)) := by
    apply (le_div_iff₀ hs).mpr
    have hm := mul_le_mul_of_nonneg_left hpar.2.2.1 hc.le
    nlinarith only [hm, hg, hc]
  apply (div_le_iff₀ hr).mpr
  nlinarith only [he, hgf]

end BerryEsseen
