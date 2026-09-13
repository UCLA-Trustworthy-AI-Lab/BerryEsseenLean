import BerryEsseen.Selection
import Mathlib.Analysis.PSeries

/-! The manuscript's Lemma 4.2 by its original harmonic-divergence argument.
No dyadic budget, finite_selection, or old harmonic_selection is used.
The convergence assumption is retained in the public endpoint, although
the positive-run contradiction proves the local assertion without it. -/
open Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_exists_small_scaledDrop (a : ℕ → ℝ)
    (hpos : ∀ K : ℕ, ∃ n ≥ K, 0 < a n)
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ n ≥ K, 1 ≤ n ∧ 0 < a n ∧ scaledDrop a n < ε := by
  classical
  by_contra h
  push_neg at h
  let N := max K 1
  have hstep (n : ℕ) (hn : N ≤ n) (hp : 0 < a n) :
      ε / (n : ℝ) ≤ a (n - 1) - a n := by
    have hn1 : 1 ≤ n := (le_max_right K 1).trans hn
    have hnK : K ≤ n := (le_max_left K 1).trans hn
    have hnr : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hb := h n hnK hn1 hp
    unfold scaledDrop at hb
    have hd : 0 < a (n - 1) - a n := by
      by_contra! hd
      rw [max_eq_right hd, mul_zero] at hb
      linarith
    rw [max_eq_left hd.le] at hb
    apply (div_le_iff₀ hnr).mpr
    nlinarith
  -- A positive run cannot start beyond N. Arbitrarily late positive terms
  -- therefore force the entire tail beginning at N to be positive.
  have htail (k : ℕ) (hk : N ≤ k) : 0 < a k := by
    obtain ⟨n, hkn, hpn⟩ := hpos k
    have hback : ∀ m ≤ n, N ≤ m → 0 < a m := by
      intro m hmn
      induction hmn using Nat.decreasingInduction with
      | self => exact fun _ => hpn
      | of_succ m hmn ih =>
        intro hNm
        have hNm1 : N ≤ m + 1 := by omega
        have hp := ih hNm1
        have hd := hstep (m + 1) hNm1 hp
        have he : 0 < ε / (m + 1 : ℕ) := div_pos hε (by positivity)
        simp only [Nat.add_sub_cancel] at hd
        linarith
    exact hback k hkn hk
  -- Summing the forced harmonic decrements gives a bounded harmonic tail.
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, ε * ((i + (N + 1) : ℕ) : ℝ)⁻¹) ≤ a N := by
    have hb : (∑ i ∈ Finset.range n, ε * ((i + (N + 1) : ℕ) : ℝ)⁻¹) ≤
        ∑ i ∈ Finset.range n, (a (N + i) - a (N + (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hd := hstep (N + (i + 1)) (by omega) (htail _ (by omega))
      have he : N + (i + 1) - 1 = N + i := by omega
      have he' : i + (N + 1) = N + (i + 1) := by omega
      simpa only [he, he', div_eq_mul_inv] using hd
    rw [Finset.sum_range_sub' (fun i => a (N + i)) n] at hb
    simp only [Nat.add_zero] at hb
    have hp := htail (N + n) (by omega)
    linarith
  have hs := summable_of_sum_range_le
    (f := fun i : ℕ => ε * ((i + (N + 1) : ℕ) : ℝ)⁻¹)
    (fun i => by positivity) hsum
  have hs' := (summable_mul_left_iff hε.ne').mp hs
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff (N + 1)).mp hs')

/-- Original harmonic proof, followed by successively smaller tolerances
and an increasing subsequence, as in the manuscript. -/
theorem manuscript_harmonic_selection (a : ℕ → ℝ)
    (_ha : Tendsto a atTop (𝓝 0))
    (hpos : ∀ K : ℕ, ∃ n ≥ K, 0 < a n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ 0 < a (u j)) ∧
      Tendsto (fun j => scaledDrop a (u j)) atTop (𝓝 0) := by
  have hex (j : ℕ) := manuscript_exists_small_scaledDrop a hpos (1 / ((j : ℝ) + 1))
    (by positivity) (j + 1)
  choose u hu h1 hp hd using hex
  have hlim : Tendsto (fun j => scaledDrop a (u j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => scaledDrop_nonneg a (u j))
      (fun j => (hd j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, huφ⟩ := strictMono_subseq_of_id_le (u := u) (fun j => by have hh := hu j; omega)
  exact ⟨u ∘ φ, huφ, fun j => ⟨h1 (φ j), hp (φ j)⟩, hlim.comp hφ.tendsto_atTop⟩

end BerryEsseen
