import BerryEsseen.BlockTailBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem reciprocal_fourth_telescope_bound (x : ℝ) (hx : 0 ≤ x) :
    1 / (x + 1 / 2) ^ 4 ≤ 32 * (1 / (x + 1) - 1 / (x + 2)) := by
  have h1 : 0 < x + 1 := by linarith
  have h2 : 0 < x + 2 := by linarith
  have hh : 0 < x + 1 / 2 := by linarith
  have he : 32 * (1 / (x + 1) - 1 / (x + 2)) = 32 / ((x + 1) * (x + 2)) := by
    field_simp; ring
  rw [he, div_le_div_iff₀ (pow_pos hh 4) (mul_pos h1 h2)]
  have hn : 0 ≤ 32*x^4 + 64*x^3 + 47*x^2 + 13*x := by positivity
  nlinarith

theorem reciprocal_fourth_range_sum_bound (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1 / 2) ^ 4) ≤ 32 := by
  have h := Finset.sum_le_sum (s := Finset.range n)
    (fun j hj => reciprocal_fourth_telescope_bound (j : ℝ) (Nat.cast_nonneg j))
  apply h.trans
  rw [← Finset.mul_sum]
  have ht : (∑ j ∈ Finset.range n, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2))) = 1 - 1 / ((n : ℝ) + 1) := by
    clear h
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [ht]
  have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem reciprocal_fourth_finset_nat_sum_bound (s : Finset ℕ) :
    (∑ j ∈ s, 1 / ((j : ℝ) + 1 / 2) ^ 4) ≤ 32 := by
  have hs : s ⊆ Finset.range (s.sup id + 1) := by
    intro j hj
    have h := Finset.le_sup (f := id) hj
    simp only [id_eq] at h
    exact Finset.mem_range.2 (by omega)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)).trans
    (reciprocal_fourth_range_sum_bound _)

theorem reciprocal_fourth_int_upper_sum_bound (s : Finset ℤ) (k : ℤ)
    (hs : ∀ j ∈ s, k < j) :
    (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 32 := by
  let f : ℤ → ℕ := fun j => (j - k - 1).toNat
  have hcast : ∀ j ∈ s, ((f j : ℕ) : ℤ) = j - k - 1 := by
    intro j hj
    exact Int.toNat_of_nonneg (by have := hs j hj; omega)
  have hinj : Set.InjOn f (↑s : Set ℤ) := by
    intro a ha b hb hab
    have hh : ((f a : ℕ) : ℤ) = (f b : ℕ) := by rw [hab]
    rw [hcast a ha, hcast b hb] at hh
    omega
  have he : (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) =
      ∑ m ∈ s.image f, 1 / ((m : ℝ) + 1 / 2) ^ 4 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro j hj
    have hreal : (f j : ℝ) = (j : ℝ) - k - 1 := by exact_mod_cast hcast j hj
    have hpos : 0 < (j : ℝ) - k := by exact_mod_cast sub_pos.2 (hs j hj)
    rw [abs_of_pos hpos, hreal]
    congr 2 <;> ring
  rw [he]
  exact reciprocal_fourth_finset_nat_sum_bound _

theorem reciprocal_fourth_int_lower_sum_bound (s : Finset ℤ) (k : ℤ)
    (hs : ∀ j ∈ s, j < k) :
    (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 32 := by
  have h := reciprocal_fourth_int_upper_sum_bound (s.image (fun j => -j)) (-k) (by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
    have := hs a ha
    omega)
  rw [Finset.sum_image (by intro a ha b hb hab; exact neg_injective hab)] at h
  have he : (∑ j ∈ s, 1 / (|((-j : ℤ) : ℝ) - (-k : ℤ)| - 1 / 2) ^ 4) =
      ∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4 := by
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    rw [show -(j : ℝ) - -(k : ℝ) = -((j : ℝ) - k) by ring, abs_neg]
  rw [he] at h
  exact h

theorem reciprocal_fourth_int_sum_bound (s : Finset ℤ) (k : ℤ)
    (hs : ∀ j ∈ s, j ≠ k) :
    (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 64 := by
  classical
  have hp := reciprocal_fourth_int_upper_sum_bound (s.filter (fun j => k < j)) k (by
    intro j hj; exact (Finset.mem_filter.1 hj).2)
  have hm := reciprocal_fourth_int_lower_sum_bound (s.filter (fun j => ¬ k < j)) k (by
    intro j hj
    have hmem := Finset.mem_filter.1 hj
    have := hs j hmem.1
    omega)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j => k < j)]
  linarith

end BerryEsseen
