import BerryEsseen.GaussianClusterComparison
import BerryEsseen.GeneralBinomialConsequences

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-! The manuscript far-threshold comparison starts from the actual conditional
block enclosure. Integer indices outside [0,n] are retained explicitly. -/

theorem manuscript_block_cdf_enclosure (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    cdf (binomialMeasure p n) ((k : ℝ) - 1) - blockLeakageBudget P Q p n k ≤
      strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ∧
    cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u) ≤
      cdf (binomialMeasure p n) k + blockLeakageBudget P Q p n k := by
  have hlo : cdf (binomialMeasure p n) ((k : ℝ) - 1) ≤
      strictBlockApproximation P Q p n k u := by
    rw [binomialMeasure_cdf p hp]
    unfold strictBlockApproximation
    apply Finset.sum_le_sum
    intro j hj
    have hb := binomialWeight_nonneg p hp n j
    have hl := strictCDF_nonneg (twoNoiseBlock P Q n j).measure u
    by_cases hjk : (j : ℤ) = k
    · have hjr : (j : ℝ) = k := by exact_mod_cast hjk
      simp only [hjk, if_pos, hjr, show ¬ (k : ℝ) ≤ k - 1 by linarith, if_false]
      exact mul_nonneg hb hl
    · by_cases hjlt : (j : ℤ) < k
      · have hjr : (j : ℝ) ≤ (k : ℝ) - 1 := by
          exact_mod_cast (show (j : ℤ) ≤ k - 1 by omega)
        simp only [hjk, if_false, hjlt, if_true, hjr, mul_one]
        exact le_rfl
      · have hjr : ¬ (j : ℝ) ≤ (k : ℝ) - 1 := by
          intro h
          have h' : (j : ℤ) ≤ k - 1 := by exact_mod_cast h
          omega
        simp only [hjk, if_false, hjlt, hjr, mul_zero]
        exact le_rfl
  have hhi : blockApproximation P Q p n k u ≤ cdf (binomialMeasure p n) k := by
    rw [binomialMeasure_cdf p hp]
    unfold blockApproximation
    apply Finset.sum_le_sum
    intro j hj
    have hb := binomialWeight_nonneg p hp n j
    by_cases hjk : (j : ℤ) = k
    · have hjr : (j : ℝ) = k := by exact_mod_cast hjk
      simp only [hjk, if_pos, hjr, le_refl]
      exact mul_le_of_le_one_right hb (cdf_le_one _ _)
    · by_cases hjlt : (j : ℤ) < k
      · have hjr : (j : ℝ) ≤ k := by exact_mod_cast hjlt.le
        simp only [hjk, if_false, hjlt, if_true, hjr, mul_one]
        exact le_rfl
      · have hjr : ¬ (j : ℝ) ≤ k := by
          intro h
          have h' : (j : ℤ) ≤ k := by exact_mod_cast h
          omega
        simp only [hjk, if_false, hjlt, hjr, mul_zero]
        exact le_rfl
  have hF := abs_le.mp (twoCluster_cdf_block_leakage P Q p hp n k u hu)
  have hL := abs_le.mp (twoCluster_strictCDF_block_leakage P Q p hp n k u hu)
  constructor <;> linarith

theorem manuscript_binomial_cdf_below_integer (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (k : ℤ) (r : ℝ) (hr : r ∈ Ioo 0 1) :
    cdf (binomialMeasure p n) ((k : ℝ) - r) =
      cdf (binomialMeasure p n) ((k : ℝ) - 1) := by
  rw [binomialMeasure_cdf p hp, binomialMeasure_cdf p hp]
  apply Finset.sum_congr rfl
  intro j hj
  have he : ((j : ℝ) ≤ (k : ℝ) - r) ↔ (j : ℝ) ≤ (k : ℝ) - 1 := by
    constructor
    · intro h
      have hlt : (j : ℝ) < k := by linarith [hr.1]
      have h' : (j : ℤ) < k := by exact_mod_cast hlt
      exact_mod_cast (show (j : ℤ) ≤ k - 1 by omega)
    · intro h
      linarith [hr.2]
  simp only [he]

theorem manuscript_binomial_left_branch_le_Kolmogorov (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (k : ℤ) :
    |cdf (binomialMeasure p n) ((k : ℝ) - 1) - normalCDF (binomialZ p n k)| ≤
      binomialKolmogorov p n := by
  have hr : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).atTop_add
      (tendsto_const_nhds (x := (2 : ℝ)))
    simpa only [one_div] using hh.inv_tendsto_atTop
  have ht := (((tendsto_const_nhds (x := (k : ℝ))).sub hr).sub
    (tendsto_const_nhds (x := (n : ℝ) * p))).div_const (Real.sqrt ((n : ℝ) * p * (1 - p)))
  have hg := ((tendsto_const_nhds (x := cdf (binomialMeasure p n) ((k : ℝ) - 1))).sub
    (normalCDF_continuous.continuousAt.tendsto.comp ht)).abs
  simp only [sub_zero] at hg
  apply le_of_tendsto hg
  filter_upwards [] with m
  have hm : 1 / ((m : ℝ) + 2) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_lt_one (by positivity : (0 : ℝ) < (m : ℝ) + 2)).mpr
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
  have h := binomialDiscrepancy_le_Kolmogorov p hp n ((k : ℝ) - 1 / ((m : ℝ) + 2))
  rw [manuscript_binomial_cdf_below_integer p hp n k _ hm] at h
  exact h

theorem manuscript_gaussian_shift_bound (a t u : ℝ) (ha : 0 < a) (hu : |u| ≤ 1 / 2) :
    |normalCDF ((t + u) / a) - normalCDF (t / a)| ≤ phi0 / (2 * a) := by
  have h : |normalCDF ((t + u) / a) - normalCDF (t / a)| ≤
      phi0 * |(t + u) / a - t / a| := by
    simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (normalCDF_hasDerivAt x).hasDerivWithinAt)
      (fun x _ => by
        rw [Real.norm_eq_abs, abs_of_pos (standardNormalDensity_pos x)]
        exact standardNormalDensity_le_phi0 x)
      (mem_univ (t / a)) (mem_univ ((t + u) / a))
  rw [← sub_div, add_sub_cancel_left, abs_div, abs_of_pos ha] at h
  calc
    _ ≤ phi0 * (|u| / a) := h
    _ ≤ phi0 * ((1 / 2) / a) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hu ha.le) phi0_pos.le
    _ = _ := by ring

theorem manuscript_binomial_prefactor (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) :
    Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 /
      (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) =
      Real.sqrt (p * (1 - p)) / (p ^ 2 + (1 - p) ^ 2) * Real.sqrt (n : ℝ) := by
  have hv : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hτ : p ^ 2 + (1 - p) ^ 2 ≠ 0 := by nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  rw [pow_succ, Real.sq_sqrt hv.le]
  field_simp [hp.1.ne', (sub_pos.mpr hp.2).ne', hτ]
  <;> ring

/-- The actual far comparison preceding the use of the ordinary uniform
binomial envelopes. The normalization and leakage errors are explicit and
vanish with accumulated variance; no nonuniform Berry--Esseen theorem is used. -/
theorem manuscript_twoCluster_far_comparison (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Ioo 0 1)
    (hεp : ε ≤ p) (hεq : ε ≤ 1 - p)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p hp) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      max (binomialUpperBranch p n k) (binomialLowerBranch p n k) +
      (56 * cE + 48 * phi0) / (p * (1 - p)) * Real.sqrt (n : ℝ) * averageNoiseVariance P Q p +
      phi0 * clusterVariance P Q p / (2 * clusterThirdAbsoluteMoment P Q p) +
      Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
        blockLeakageBudget P Q p n k := by
  let r := Real.sqrt (n : ℝ)
  let σ := Real.sqrt (clusterVariance P Q p)
  let A := σ ^ 3 / clusterThirdAbsoluteMoment P Q p
  let F := cdf (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let Fl := strictCDF (iidSumLaw (twoClusterMeasure P Q p) n) ((k : ℝ) + u)
  let F0 := cdf (binomialMeasure p n) k
  let Fm := cdf (binomialMeasure p n) ((k : ℝ) - 1)
  let G := normalCDF (((k : ℝ) + u - n * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  let G0 := normalCDF (((k : ℝ) - n * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p))
  let J := blockLeakageBudget P Q p n k
  let E := (56 * cE + 48 * phi0) / (p * (1 - p)) * r * averageNoiseVariance P Q p
  let D := phi0 * clusterVariance P Q p / (2 * clusterThirdAbsoluteMoment P Q p)
  have hpI : p ∈ Icc 0 1 := ⟨hp.1.le, hp.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpI
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hσ : 0 < σ := Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp)
  have hρ := clusterThirdAbsoluteMoment_pos P Q p hp
  have hA : 0 < A := div_pos (pow_pos hσ 3) hρ
  have hfac : 0 ≤ r * A := (mul_pos hr hA).le
  have hen := manuscript_block_cdf_enclosure P Q p hpI n k u hu
  change Fm - J ≤ Fl ∧ F ≤ F0 + J at hen
  have hflo : Fl ≤ F := strictCDF_le_cdf _ _
  have hU := actual_cluster_normalization_error P Q p ε hp hεp hεq hP hQ hs n hn k F0
    ((binomialDiscrepancy_le_Kolmogorov p hpI n k).trans (B.strict_bound p hp n hn).le)
  have hL := actual_cluster_normalization_error P Q p ε hp hεp hεq hP hQ hs n hn k Fm
    ((manuscript_binomial_left_branch_le_Kolmogorov p hpI n k).trans (B.strict_bound p hp n hn).le)
  rw [manuscript_binomial_prefactor p hp n] at hU hL
  change |r * A * (F0 - G0) - binomialUpperBranch p n k| ≤ E at hU
  have hL' : |r * A * (Fm - G0) + binomialLowerBranch p n k| ≤ E := by
    convert hL using 1
    unfold binomialLowerBranch binomialZ
    dsimp only [r, A, σ, Fm, G0]
    congr 1
    ring
  have hroot : Real.sqrt ((n : ℝ) * clusterVariance P Q p) = r * σ :=
    Real.sqrt_mul (Nat.cast_nonneg n) _
  have hshift := manuscript_gaussian_shift_bound (r * σ) ((k : ℝ) - n * p) u
    (mul_pos hr hσ) hu
  have hshift' : |G - G0| ≤ phi0 / (2 * (r * σ)) := by
    dsimp only [G, G0]
    rw [hroot]
    convert hshift using 1 <;> congr 2 <;> ring
  have hshiftmul := mul_le_mul_of_nonneg_left hshift' hfac
  have hid : r * A * (phi0 / (2 * (r * σ))) = D := by
    dsimp only [A, D]
    field_simp [hr.ne', hσ.ne', hρ.ne']
    have hσsq : σ ^ 2 = clusterVariance P Q p := Real.sq_sqrt (clusterVariance_pos P Q p hp).le
    rw [hσsq]
    ring
  rw [hid] at hshiftmul
  have hdiffLo := mul_le_mul_of_nonneg_left (neg_abs_le (G - G0)) hfac
  have hdiffHi := mul_le_mul_of_nonneg_left (le_abs_self (G - G0)) hfac
  have hFhi := mul_le_mul_of_nonneg_left hen.2 hfac
  have hFlo := mul_le_mul_of_nonneg_left (hen.1.trans hflo) hfac
  have hUr := (abs_le.mp hU).2
  have hLr := (abs_le.mp hL').1
  have habs : r * A * |F - G| ≤ max (binomialUpperBranch p n k) (binomialLowerBranch p n k) + E + D + r * A * J := by
    conv_lhs => rw [← abs_of_nonneg hfac, ← abs_mul]
    rw [abs_le]
    constructor <;> nlinarith only [hUr, hLr, hFhi, hFlo, hdiffLo, hdiffHi, hshiftmul,
      le_max_left (binomialUpperBranch p n k) (binomialLowerBranch p n k),
      le_max_right (binomialUpperBranch p n k) (binomialLowerBranch p n k)]
  rw [standardizedTwoCluster_discrepancy P Q p hp n hn]
  simpa only [r, A, σ, F, G, E, D, J, mul_div_assoc] using habs

end BerryEsseen
