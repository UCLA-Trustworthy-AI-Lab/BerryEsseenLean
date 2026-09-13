import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! Selection of a sequence with small positive downward increments.
The proof uses a finite telescoping argument. In particular it does not
assume monotonicity of the extremal constants. -/
open Filter
open scoped Topology

namespace BerryEsseen

/-- Finite telescoping, propagating positivity backwards from the endpoint. -/
theorem backward_descent (a w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (k : ℕ)
    (hend : 0 < a k)
    (hstep : ∀ i < k, 0 < a (i + 1) → w i < a i - a (i + 1)) :
    0 < a 0 ∧ a k + ∑ i ∈ Finset.range k, w i ≤ a 0 := by
  induction k with
  | zero => simpa using hend
  | succ k ih =>
    have hlast := hstep k (by omega) hend
    have hprev : 0 < a k := by linarith [hw k]
    have hprefix := ih hprev (fun i hi => hstep i (by omega))
    refine ⟨hprefix.1, ?_⟩
    rw [Finset.sum_range_succ]
    linarith [hprefix.2]

/-- A finite quantitative selection principle, useful also for Appendix A. -/
theorem finite_selection (a w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (k : ℕ)
    (hend : 0 < a k) (hbudget : a 0 ≤ ∑ i ∈ Finset.range k, w i) :
    ∃ i < k, 0 < a (i + 1) ∧ a i - a (i + 1) ≤ w i := by
  by_contra h
  push_neg at h
  have htel := backward_descent a w hw k hend h
  linarith [htel.2]

def scaledDrop (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * max (a (n - 1) - a n) 0

theorem scaledDrop_nonneg (a : ℕ → ℝ) (n : ℕ) : 0 ≤ scaledDrop a n :=
  mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

/-- The local selection assertion in Lemma 4.2.
A dyadic finite argument avoids needing an infinite harmonic sum. -/
theorem exists_small_scaledDrop (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0))
    (hpos : ∀ K : ℕ, ∃ n ≥ K, 0 < a n)
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ n ≥ K, 1 ≤ n ∧ 0 < a n ∧ scaledDrop a n < ε := by
  have hevent : ∀ᶠ n in atTop, a n < ε / 4 :=
    ha.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 4))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
  let N := max (max N₀ K) 1
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hNK : K ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN1 : 1 ≤ N := le_max_right _ _
  obtain ⟨n, hn, hpn⟩ := hpos (2 * N)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let b : ℕ → ℝ := fun i => a (N + i)
  let w : ℕ → ℝ := fun _ => ε / (2 * (n : ℝ))
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hend : 0 < b (n - N) := by simpa [b, Nat.add_sub_of_le (by omega : N ≤ n)] using hpn
  have hbudget : b 0 ≤ ∑ i ∈ Finset.range (n - N), w i := by
    have hstart : b 0 < ε / 4 := by simpa [b] using hN₀ N hN0
    have hcast : (n : ℝ) ≤ 2 * ((n - N : ℕ) : ℝ) := by exact_mod_cast (show n ≤ 2 * (n - N) by omega)
    have hlower : ε / 4 ≤ ((n - N : ℕ) : ℝ) * (ε / (2 * (n : ℝ))) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
      nlinarith
    simpa [w, Finset.sum_const, nsmul_eq_mul] using le_trans (le_of_lt hstart) hlower
  obtain ⟨i, hi, hpi, hdi⟩ := finite_selection b w hw (n - N) hend hbudget
  let m := N + (i + 1)
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hmn : m ≤ n := by dsimp [m]; omega
  have hdiff : a (m - 1) - a m ≤ ε / (2 * (n : ℝ)) := by
    simpa [b, w, m, Nat.add_sub_assoc (by omega : 1 ≤ i + 1)] using hdi
  have hmax : max (a (m - 1) - a m) 0 ≤ ε / (2 * (n : ℝ)) :=
    max_le hdiff (by positivity)
  have hbound : scaledDrop a m ≤ ε / 2 := by
    unfold scaledDrop
    calc
      (m : ℝ) * max (a (m - 1) - a m) 0
        ≤ (m : ℝ) * (ε / (2 * (n : ℝ))) := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
      _ ≤ (n : ℝ) * (ε / (2 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (by positivity)
      _ = ε / 2 := by field_simp
  refine ⟨m, by dsimp [m]; omega, hm1, ?_, ?_⟩
  · simpa [m, b] using hpi
  · linarith

/-- Lemma 4.2 of the manuscript, with strict increase of the selected indices. -/
theorem harmonic_selection (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0))
    (hpos : ∀ K : ℕ, ∃ n ≥ K, 0 < a n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ 0 < a (u j)) ∧
      Tendsto (fun j => scaledDrop a (u j)) atTop (𝓝 0) := by
  have hex (j : ℕ) := exists_small_scaledDrop a ha hpos (1 / ((j : ℝ) + 1))
    (by positivity) (j + 1)
  choose u hu h1 hp hd using hex
  have hlim : Tendsto (fun j => scaledDrop a (u j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => scaledDrop_nonneg a (u j))
      (fun j => (hd j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, huφ⟩ := strictMono_subseq_of_id_le (u := u) (fun j => by have hh := hu j; omega)
  exact ⟨u ∘ φ, huφ, fun j => ⟨h1 (φ j), hp (φ j)⟩, hlim.comp hφ.tendsto_atTop⟩

end BerryEsseen
