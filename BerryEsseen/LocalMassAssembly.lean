import BerryEsseen.IntegerWindow
import BerryEsseen.AppliedClusterBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem strictCDF_sub_cdf_open_interval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a < b) : strictCDF μ b - cdf μ a = μ.real (Ioo a b) := by
  have he : Iio b \ Iic a = Ioo a b := by
    ext x
    simp only [mem_diff, mem_Iio, mem_Iic, not_le, mem_Ioo, and_comm]
  have h := measureReal_diff (μ := μ) (Iic_subset_Iio.2 hab) measurableSet_Iic
  rw [he] at h
  rw [strictCDF, cdf_eq_real]
  exact h.symm

theorem twoCluster_open_interval_decomposition (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (a b : ℝ) (hab : a < b) :
    (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo a b) =
      ∑ k ∈ Finset.range (n + 1), binomialWeight p n k * (twoNoiseBlock P Q n k).measure.real (Ioo (a - k) (b - k)) := by
  letI := twoClusterMeasure_probability P Q p hp
  rw [← strictCDF_sub_cdf_open_interval _ a b hab, iidSumLaw_twoCluster_strictCDF P Q p hp,
    iidSumLaw_twoCluster_cdf P Q p hp]
  change (∑ k ∈ Finset.range (n + 1), binomialWeight p n k * strictCDF (twoNoiseBlock P Q n k).measure (b - k)) -
    (∑ k ∈ Finset.range (n + 1), binomialWeight p n k * cdf (twoNoiseBlock P Q n k).measure (a - k)) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_sub, strictCDF_sub_cdf_open_interval _ _ _ (by linarith)]

theorem twoCluster_open_interval_lower_of_blocks (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (a b : ℝ) (hab : a < b) (K : Finset ℕ) (hK : K ⊆ Finset.range (n + 1))
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ k ∈ K, B ≤ binomialWeight p n k)
    (hprob : ∀ k ∈ K, C ≤ (twoNoiseBlock P Q n k).measure.real (Ioo (a - k) (b - k))) :
    (K.card : ℝ) * B * C ≤ (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo a b) := by
  rw [twoCluster_open_interval_decomposition P Q p hp n a b hab]
  have h1 : (∑ _ ∈ K, B * C) ≤ ∑ k ∈ K, binomialWeight p n k * (twoNoiseBlock P Q n k).measure.real (Ioo (a - k) (b - k)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul (hb k hk) (hprob k hk) hC (binomialWeight_nonneg p hp n k)
  have h2 : (∑ k ∈ K, binomialWeight p n k * (twoNoiseBlock P Q n k).measure.real (Ioo (a - k) (b - k))) ≤
      ∑ k ∈ Finset.range (n + 1), binomialWeight p n k * (twoNoiseBlock P Q n k).measure.real (Ioo (a - k) (b - k)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hK
    intro k hk hkK
    exact mul_nonneg (binomialWeight_nonneg p hp n k) ENNReal.toReal_nonneg
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using h1.trans h2

def localNoiseWindowRadius (Lstar a b : ℝ) : ℝ := 2 + 2 * (1 + |a| + |b|) / Real.sqrt Lstar

theorem localNoiseWindowRadius_pos (Lstar a b : ℝ) (hLstar : 0 < Lstar) :
    0 < localNoiseWindowRadius Lstar a b := by unfold localNoiseWindowRadius; positivity

theorem noise_window_standardized_endpoint (Lstar L t x k a b : ℝ) (hLstar : 0 < Lstar)
    (hL : Lstar ≤ L) (ht : L / 2 ≤ t) (hxk : |k - x| ≤ max 1 (Real.sqrt L)) :
    |(x + a - k) / Real.sqrt t| ≤ localNoiseWindowRadius Lstar a b := by
  have hLpos := hLstar.trans_le hL
  have htpos : 0 < t := by linarith
  have hroot := Real.sqrt_pos.2 htpos
  have hLroot := Real.sqrt_pos.2 hLpos
  have hstarroot := Real.sqrt_pos.2 hLstar
  have hlower : Real.sqrt L / 2 ≤ Real.sqrt t := by
    apply (Real.le_sqrt (by positivity) htpos.le).2
    nlinarith [Real.sq_sqrt hLpos.le]
  have hdist : |x + a - k| ≤ Real.sqrt L + 1 + |a| := by
    have he : x + a - k = -(k - x) + a := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_neg]
    have hmax : max 1 (Real.sqrt L) ≤ Real.sqrt L + 1 := max_le (by linarith [hLroot]) (by linarith)
    linarith [hxk.trans hmax]
  have hratio : (1 : ℝ) ≤ Real.sqrt L / Real.sqrt Lstar := (le_div_iff₀ hstarroot).2 (by simpa using Real.sqrt_le_sqrt hL)
  have hm := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 1 + |a| + |b|)
  have hM := (localNoiseWindowRadius_pos Lstar a b hLstar).le
  have hscale := mul_le_mul_of_nonneg_left hlower hM
  rw [abs_div, abs_of_pos hroot]
  apply (div_le_iff₀ hroot).2
  apply le_trans _ hscale
  dsimp only [localNoiseWindowRadius]
  have he : (2 + 2 * (1 + |a| + |b|) / Real.sqrt Lstar) * (Real.sqrt L / 2) =
      Real.sqrt L + (1 + |a| + |b|) * (Real.sqrt L / Real.sqrt Lstar) := by ring
  rw [he]
  nlinarith only [hdist, hm, abs_nonneg b]

theorem noise_block_window_mass_lower (S : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ᵐ y ∂P.measure, |y| ≤ ε) (hQ : ∀ᵐ y ∂Q.measure, |y| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (Lstar L x a b : ℝ) (hLstar : 0 < Lstar) (hL : Lstar ≤ L)
    (hab : a < b) (htlo : L / 2 ≤ (twoNoiseBlock P Q n k).secondMoment)
    (hthi : (twoNoiseBlock P Q n k).secondMoment ≤ 2 * L)
    (hxk : |(k : ℝ) - x| ≤ max 1 (Real.sqrt L))
    (heps : ε ≤ (b - a) * centralDensityFloor (localNoiseWindowRadius Lstar a b) / 8) :
    (b - a) * centralDensityFloor (localNoiseWindowRadius Lstar a b) / (8 * Real.sqrt L) ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo (x + a - k) (x + b - k)) := by
  let M := localNoiseWindowRadius Lstar a b
  have hLpos := hLstar.trans_le hL
  have ht : 0 < (twoNoiseBlock P Q n k).secondMoment := by linarith
  have hM := (localNoiseWindowRadius_pos Lstar a b hLstar).le
  have ha := noise_window_standardized_endpoint Lstar L _ x k a b hLstar hL htlo hxk
  have hb := noise_window_standardized_endpoint Lstar L _ x k b a hLstar hL htlo hxk
  have hswap : localNoiseWindowRadius Lstar b a = localNoiseWindowRadius Lstar a b := by unfold localNoiseWindowRadius; ring
  rw [hswap] at hb
  have h := twoNoiseBlock_open_interval_lower S P Q ε hε hP hQ n k hn hk ht M _ _ hM (by linarith) ha hb
  have hw : (x + b - (k : ℝ)) - (x + a - k) = b - a := by ring
  rw [hw] at h
  have hnum : (b - a) * centralDensityFloor M / 4 ≤ (b - a) / 2 * centralDensityFloor M - (1.12 : ℝ) * ε := by
    have hpos : 0 ≤ (b - a) * centralDensityFloor M := mul_nonneg (sub_pos.2 hab).le (centralDensityFloor_pos M).le
    nlinarith only [heps, hpos]
  have hroot : Real.sqrt (twoNoiseBlock P Q n k).secondMoment ≤ 2 * Real.sqrt L := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [Real.sq_sqrt hLpos.le]
  have hnum0 : 0 ≤ (b - a) / 2 * centralDensityFloor M - (1.12 : ℝ) * ε :=
    (by have := centralDensityFloor_pos M; have := sub_pos.2 hab; positivity : 0 ≤ (b - a) * centralDensityFloor M / 4).trans hnum
  have hh := div_le_div₀ hnum0 hnum (Real.sqrt_pos.2 ht) hroot
  have he : (b - a) * centralDensityFloor M / (8 * Real.sqrt L) =
      ((b - a) * centralDensityFloor M / 4) / (2 * Real.sqrt L) := by ring
  rw [he]
  exact hh.trans h

end BerryEsseen
