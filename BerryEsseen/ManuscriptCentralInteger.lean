import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptSmallVarianceSequence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_central_integer_eventually_in_range
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (k : ℕ → ℤ) (z₀ : ℝ)
    (hz : Tendsto (fun j => binomialZ (p j) (n j) (k j)) atTop (𝓝 z₀)) :
    ∀ᶠ j in atTop, 0 ≤ k j ∧ k j ≤ n j := by
  let M : ℝ := |z₀| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hr := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  filter_upwards [Metric.tendsto_nhds.mp hz 1 (by norm_num), hr.eventually_ge_atTop (5 * M)] with j hj hjr
  have hpj := hp j
  have hpI : p j ∈ Ioo 0 1 := by constructor <;> linarith [hpj.1, hpj.2]
  have hn0 : (0 : ℝ) < n j := by exact_mod_cast (show 0 < n j by have := hn1 j; omega)
  have rpos := Real.sqrt_pos.mpr hn0
  have rsq := Real.sq_sqrt hn0.le
  have vpos := mul_pos hpI.1 (sub_pos.mpr hpI.2)
  have spos := Real.sqrt_pos.mpr vpos
  have sone : Real.sqrt (p j * (1 - p j)) ≤ 1 := by
    have hb := (bernoulli_variance_tau_bounds (p j) hpI).1.2
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb
  have hzz : |binomialZ (p j) (n j) (k j)| ≤ M := by
    rw [Real.dist_eq] at hj
    have ht := abs_add_le (binomialZ (p j) (n j) (k j) - z₀) z₀
    rw [sub_add_cancel] at ht
    dsimp only [M]
    linarith
  have he : (k j : ℝ) - n j * p j = Real.sqrt (p j * (1 - p j)) *
      (Real.sqrt (n j : ℝ) * binomialZ (p j) (n j) (k j)) := by
    rw [binomialZ_scaling (p j) hpI (n j) (hn1 j) (k j)]
    exact (mul_div_cancel₀ _ spos.ne').symm
  have hraw : |(k j : ℝ) - n j * p j| ≤ M * Real.sqrt (n j : ℝ) := by
    rw [he, abs_mul, abs_mul, abs_of_pos spos, abs_of_pos rpos]
    have h := mul_le_mul sone (mul_le_mul_of_nonneg_left hzz rpos.le)
      (mul_nonneg rpos.le (abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul, mul_comm M] using h
  have hlo := mul_le_mul_of_nonneg_left hpj.1 hn0.le
  have hhi := mul_le_mul_of_nonneg_left hpj.2 hn0.le
  have hsq := mul_le_mul_of_nonneg_right hjr rpos.le
  change 5 * M * Real.sqrt (n j : ℝ) ≤ Real.sqrt (n j : ℝ) * Real.sqrt (n j : ℝ) at hsq
  rw [← sq, rsq] at hsq
  have hrange : (0 : ℝ) ≤ k j ∧ (k j : ℝ) ≤ n j := by
    rcases abs_le.mp hraw with ⟨hl, hu⟩
    constructor <;> nlinarith only [hl, hu, hlo, hhi, hsq, hn0.le]
  constructor
  · exact_mod_cast hrange.left
  · exact_mod_cast hrange.right

theorem manuscript_small_variance_central_integer_sequence
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j) (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hlam : Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0))
    (hlampos : ∀ j, 0 < accumulatedNoiseVariance (P j) (Q j) (p j) (n j))
    (k : ℕ → ℤ) (z₀ : ℝ)
    (hz : Tendsto (fun j => binomialZ (p j) (n j) (k j)) atTop (𝓝 z₀)) :
    ∃ c > 0, ∀ᶠ j in atTop, ∀ u : ℝ, |u| ≤ 1 / 2 →
      normalizedDiscrepancy (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)
        (((k j : ℝ) + u - (n j : ℝ) * p j) /
          Real.sqrt ((n j : ℝ) * clusterVariance (P j) (Q j) (p j))) ≤
        Real.sqrt (n j : ℝ) * (Real.sqrt (p j * (1 - p j)) ^ 3 /
          (p j * (1 - p j) * ((p j) ^ 2 + (1 - p j) ^ 2))) * binomialKolmogorov (p j) (n j) -
        c * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) /
          Real.sqrt (3 * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) / (2 / 5) + (ε j) ^ 2) := by
  let l : ℕ → ℕ := fun j => min (n j) (k j).toNat
  have hl : ∀ j, l j ≤ n j := fun j => min_le_left _ _
  have he : ∀ᶠ j in atTop, (l j : ℤ) = k j := by
    filter_upwards [manuscript_central_integer_eventually_in_range p hcentral n hn
      (fun j => by have := hn2 j; omega) k z₀ hz] with j hj
    have hkn : (k j).toNat ≤ n j := by omega
    simp only [l, min_eq_right hkn, Int.toNat_of_nonneg hj.1]
  have hzl : Tendsto (fun j => binomialZ (p j) (n j) (l j)) atTop (𝓝 z₀) := by
    apply hz.congr'
    filter_upwards [he] with j hj
    rw [hj]
  obtain ⟨c, hc, hbound⟩ := manuscript_small_variance_central_sequence W S B P Q p ε hp hcentral
    hplim hε hεlim hεp hεq hP hQ n hn hn2 hlam hlampos l hl z₀ hzl
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound, he] with j hj heq
  intro u hu
  have heq' : (l j : ℝ) = k j := by exact_mod_cast heq
  simpa only [heq'] using hj u hu

end BerryEsseen
