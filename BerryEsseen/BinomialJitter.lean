import BerryEsseen.PublishedBernoulli
import BerryEsseen.UniformJitter

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem binomial_cdf_between_integers (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (s : ℝ) (hs : s ∈ Ico 0 1) :
    cdf (binomialMeasure p n) ((k : ℝ) + s) = cdf (binomialMeasure p n) k := by
  rw [binomialMeasure_cdf p hp, binomialMeasure_cdf p hp]
  apply Finset.sum_congr rfl
  intro j hj
  have he : ((j : ℝ) ≤ (k : ℝ) + s) ↔ (j : ℝ) ≤ k := by
    constructor
    · intro h
      by_contra hnot
      have hk : k < (j : ℤ) := by exact_mod_cast (lt_of_not_ge hnot)
      have hk1 : (k : ℝ) + 1 ≤ j := by exact_mod_cast hk
      linarith [hs.2]
    · intro h
      linarith [hs.1]
  simp only [he]

theorem binomial_cdf_right_integral_short (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Icc 0 1) :
    (∫ s in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) + s)) = L * cdf (binomialMeasure p n) k := by
  have he : (∫ s in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) + s)) =
      ∫ _ in (0 : ℝ)..L, cdf (binomialMeasure p n) k := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (1 : ℝ)] with s hs
    intro hmem
    rw [uIoc_of_le hL.1] at hmem
    exact binomial_cdf_between_integers p hp n k s ⟨hmem.1.le, lt_of_le_of_ne (hmem.2.trans hL.2) hs⟩
  rw [he, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem binomial_cdf_right_integral_long (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Icc 1 2) :
    (∫ s in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) + s)) =
      cdf (binomialMeasure p n) k + (L - 1) * cdf (binomialMeasure p n) ((k : ℝ) + 1) := by
  letI := binomialMeasure_probability p hp n
  have hm : Monotone (fun s : ℝ => cdf (binomialMeasure p n) ((k : ℝ) + s)) :=
    (monotone_cdf _).comp (monotone_const.add monotone_id)
  rw [← intervalIntegral.integral_add_adjacent_intervals hm.intervalIntegrable hm.intervalIntegrable,
    binomial_cdf_right_integral_short p hp n k 1 (by constructor <;> norm_num), one_mul]
  congr 1
  have he : (∫ s in (1 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) + s)) =
      ∫ _ in (1 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) + 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (2 : ℝ)] with s hs
    intro hmem
    rw [uIoc_of_le hL.1] at hmem
    have h := binomial_cdf_between_integers p hp n (k + 1) (s - 1)
      ⟨by linarith [hmem.1], by have hh := lt_of_le_of_ne (hmem.2.trans hL.2) hs; linarith⟩
    convert h using 1 <;> push_cast <;> congr 1 <;> ring
  rw [he, intervalIntegral.integral_const, smul_eq_mul]

theorem binomial_jitter_right_error (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Ioc 0 2) :
    |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) + L / 2) - cdf (binomialMeasure p n) k| ≤
      |L - 1| / L * (cdf (binomialMeasure p n) ((k : ℝ) + 1) - cdf (binomialMeasure p n) k) := by
  letI := binomialMeasure_probability p hp n
  rw [uniformJitter_cdf_average _ hL.1]
  have hmono : 0 ≤ cdf (binomialMeasure p n) ((k : ℝ) + 1) - cdf (binomialMeasure p n) k := by
    have h := monotone_cdf (binomialMeasure p n) (show (k : ℝ) ≤ (k : ℝ) + 1 by linarith)
    linarith
  by_cases hshort : L ≤ 1
  · rw [binomial_cdf_right_integral_short p hp n k L ⟨hL.1.le, hshort⟩,
      mul_div_cancel_left₀ _ hL.1.ne', sub_self, abs_zero]
    exact mul_nonneg (div_nonneg (abs_nonneg _) hL.1.le) hmono
  · rw [binomial_cdf_right_integral_long p hp n k L ⟨by linarith, hL.2⟩]
    have he : (cdf (binomialMeasure p n) k + (L - 1) * cdf (binomialMeasure p n) ((k : ℝ) + 1)) / L - cdf (binomialMeasure p n) k =
      (L - 1) / L * (cdf (binomialMeasure p n) ((k : ℝ) + 1) - cdf (binomialMeasure p n) k) := by field_simp [hL.1.ne']; ring
    rw [he, abs_mul, abs_div, abs_of_pos hL.1, abs_of_nonneg hmono]

theorem uniformJitter_cdf_backward_average (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L : ℝ) (hL : 0 < L) (k : ℝ) :
    cdf (μ ∗ uniformJitter L) (k - L / 2) = (∫ s in (0 : ℝ)..L, cdf μ (k - s)) / L := by
  have h := uniformJitter_cdf_average μ hL (k - L)
  have he : k - L + L / 2 = k - L / 2 := by ring
  rw [he] at h
  rw [h]
  congr 1
  have hf : (fun s : ℝ => cdf μ (k - L + s)) = (fun s => (fun r => cdf μ (k - r)) (L - s)) := by
    funext s
    congr 1
    ring
  rw [hf]
  simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => cdf μ (k - r)) (a := 0) (b := L) L

theorem binomial_cdf_left_integral_short (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Icc 0 1) :
    (∫ s in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) - s)) =
      L * cdf (binomialMeasure p n) ((k : ℝ) - 1) := by
  have he : (∫ s in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) - s)) =
      ∫ _ in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) - 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with s
    intro hmem
    rw [uIoc_of_le hL.1] at hmem
    have h := binomial_cdf_between_integers p hp n (k - 1) (1 - s)
      ⟨by linarith [hmem.2, hL.2], by linarith [hmem.1]⟩
    convert h using 1 <;> push_cast <;> congr 1 <;> ring
  rw [he, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem binomial_cdf_left_integral_long (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Icc 1 2) :
    (∫ s in (0 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) - s)) =
      cdf (binomialMeasure p n) ((k : ℝ) - 1) + (L - 1) * cdf (binomialMeasure p n) ((k : ℝ) - 2) := by
  letI := binomialMeasure_probability p hp n
  have hm : Antitone (fun s : ℝ => cdf (binomialMeasure p n) ((k : ℝ) - s)) := by
    intro a b hab
    exact monotone_cdf _ (by linarith : (k : ℝ) - b ≤ (k : ℝ) - a)
  rw [← intervalIntegral.integral_add_adjacent_intervals hm.intervalIntegrable hm.intervalIntegrable,
    binomial_cdf_left_integral_short p hp n k 1 (by constructor <;> norm_num), one_mul]
  congr 1
  have he : (∫ s in (1 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) - s)) =
      ∫ _ in (1 : ℝ)..L, cdf (binomialMeasure p n) ((k : ℝ) - 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with s
    intro hmem
    rw [uIoc_of_le hL.1] at hmem
    have h := binomial_cdf_between_integers p hp n (k - 2) (2 - s)
      ⟨by linarith [hmem.2, hL.2], by linarith [hmem.1]⟩
    convert h using 1 <;> push_cast <;> congr 1 <;> ring
  rw [he, intervalIntegral.integral_const, smul_eq_mul]

theorem binomial_jitter_left_error (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Ioc 0 2) :
    |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) - L / 2) - cdf (binomialMeasure p n) ((k : ℝ) - 1)| ≤
      |L - 1| / L * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - cdf (binomialMeasure p n) ((k : ℝ) - 2)) := by
  letI := binomialMeasure_probability p hp n
  rw [uniformJitter_cdf_backward_average _ L hL.1]
  have hmono : 0 ≤ cdf (binomialMeasure p n) ((k : ℝ) - 1) - cdf (binomialMeasure p n) ((k : ℝ) - 2) := by
    have h := monotone_cdf (binomialMeasure p n) (show (k : ℝ) - 2 ≤ (k : ℝ) - 1 by linarith)
    linarith
  by_cases hshort : L ≤ 1
  · rw [binomial_cdf_left_integral_short p hp n k L ⟨hL.1.le, hshort⟩,
      mul_div_cancel_left₀ _ hL.1.ne', sub_self, abs_zero]
    exact mul_nonneg (div_nonneg (abs_nonneg _) hL.1.le) hmono
  · rw [binomial_cdf_left_integral_long p hp n k L ⟨by linarith, hL.2⟩]
    have he : (cdf (binomialMeasure p n) ((k : ℝ) - 1) + (L - 1) * cdf (binomialMeasure p n) ((k : ℝ) - 2)) / L - cdf (binomialMeasure p n) ((k : ℝ) - 1) =
      -((L - 1) / L * (cdf (binomialMeasure p n) ((k : ℝ) - 1) - cdf (binomialMeasure p n) ((k : ℝ) - 2))) := by field_simp [hL.1.ne']; ring
    rw [he, abs_neg, abs_mul, abs_div, abs_of_pos hL.1, abs_of_nonneg hmono]

theorem binomial_cdf_integer_jump_bound (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (B : ℝ) (hB : 0 ≤ B) (hw : ∀ j ≤ n, binomialWeight p n j ≤ B) :
    cdf (binomialMeasure p n) ((k : ℝ) + 1) - cdf (binomialMeasure p n) k ≤ B := by
  classical
  rw [binomialMeasure_cdf p hp, binomialMeasure_cdf p hp, ← Finset.sum_sub_distrib]
  have he : ∀ j : ℕ, (if (j : ℝ) ≤ (k : ℝ) + 1 then binomialWeight p n j else 0) -
      (if (j : ℝ) ≤ (k : ℝ) then binomialWeight p n j else 0) =
      if (j : ℤ) = k + 1 then binomialWeight p n j else 0 := by
    intro j
    have hle (m : ℤ) : ((j : ℝ) ≤ (m : ℝ)) ↔ (j : ℤ) ≤ m := by norm_cast
    rw [show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; rfl]
    simp only [hle]
    by_cases h : (j : ℤ) ≤ k
    · simp [h, show (j : ℤ) ≤ k + 1 by omega, show (j : ℤ) ≠ k + 1 by omega]
    · by_cases h' : (j : ℤ) = k + 1
      · simp [h, h']
      · simp [h, h', show ¬(j : ℤ) ≤ k + 1 by omega]
  simp_rw [he]
  by_cases hk : 0 ≤ k + 1
  · have hcast : ((k + 1).toNat : ℤ) = k + 1 := Int.toNat_of_nonneg hk
    have heq : ∀ j : ℕ, ((j : ℤ) = k + 1) ↔ j = (k + 1).toNat := by
      intro j
      constructor <;> intro h <;> omega
    simp_rw [heq]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · exact hw _ (by have := Finset.mem_range.1 h; omega)
    · exact hB
  · have hne : ∀ j : ℕ, (j : ℤ) ≠ k + 1 := by intro j; omega
    simp only [hne, if_false, Finset.sum_const_zero]
    exact hB

theorem binomial_jitter_errors_of_mass_bound (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (L : ℝ) (hL : L ∈ Icc (1 / 2) 2) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ j ≤ n, binomialWeight p n j ≤ B) :
    (|cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) + L / 2) - cdf (binomialMeasure p n) k| ≤ 2 * |L - 1| * B) ∧
    (|cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) - L / 2) - cdf (binomialMeasure p n) ((k : ℝ) - 1)| ≤ 2 * |L - 1| * B) := by
  have hL0 : 0 < L := by linarith [hL.1]
  have hratio : |L - 1| / L ≤ 2 * |L - 1| := by
    apply (div_le_iff₀ hL0).2
    nlinarith [mul_nonneg (show 0 ≤ 2 * L - 1 by linarith [hL.1]) (abs_nonneg (L - 1))]
  have hu := binomial_jitter_right_error p hp n k L ⟨hL0, hL.2⟩
  have hl := binomial_jitter_left_error p hp n k L ⟨hL0, hL.2⟩
  have hub := binomial_cdf_integer_jump_bound p hp n k B hB hw
  have hlb := binomial_cdf_integer_jump_bound p hp n (k - 2) B hB hw
  have hlb' : cdf (binomialMeasure p n) ((k : ℝ) - 1) - cdf (binomialMeasure p n) ((k : ℝ) - 2) ≤ B := by
    convert hlb using 1 <;> push_cast <;> congr 2 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hratio hB
  constructor
  · exact hu.trans ((mul_le_mul_of_nonneg_left hub (div_nonneg (abs_nonneg _) hL0.le)).trans hmul)
  · exact hl.trans ((mul_le_mul_of_nonneg_left hlb' (div_nonneg (abs_nonneg _) hL0.le)).trans hmul)

theorem binomial_jitter_scaled_errors (S : PublishedBernoulliBound) (p δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (L : ℝ) (hL : L ∈ Icc (1 / 2) 2) :
    (Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) + L / 2) - cdf (binomialMeasure p n) k| ≤
      (4 * cE / δ) * |L - 1|) ∧
    (Real.sqrt (n : ℝ) * |cdf (binomialMeasure p n ∗ uniformJitter L) ((k : ℝ) - L / 2) - cdf (binomialMeasure p n) ((k : ℝ) - 1)| ≤
      (4 * cE / δ) * |L - 1|) := by
  have hpI : p ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsn := Real.sqrt_pos.2 hn0
  have hc := cE_pos
  have h := binomial_jitter_errors_of_mass_bound p hpI n k L hL (2 * cE / (δ * Real.sqrt (n : ℝ)))
    (by positivity) (fun j hj => binomialWeight_uniform_bound S p δ hδ hp hq n j hn hj)
  have he : Real.sqrt (n : ℝ) * (2 * |L - 1| * (2 * cE / (δ * Real.sqrt (n : ℝ)))) = (4 * cE / δ) * |L - 1| := by
    field_simp [hδ.ne', hsn.ne']
    ring
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 hsn.le
    rwa [he] at hh
  · have hh := mul_le_mul_of_nonneg_left h.2 hsn.le
    rwa [he] at hh

end BerryEsseen
