import BerryEsseen.UniformBlockLeakage

/-! The appendix leakage kernel bound, eq:effective-leakage.
The two nearest integers contribute 32. Each remaining half-line is
bounded by the telescoping series 1/(m+1)-1/(m+2), whose sum is 1.
Thus the full kernel sum is at most 34, in particular strictly below
the manuscript's 40. Multiplying actual block weights and fourth
moments gives the manuscript's 40 B M and hence 80 D₄ / sqrt(n). -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_reciprocal_fourth_tail_bound (x : ℝ) (hx : 0 ≤ x) :
    1 / (x + 3 / 2) ^ 4 ≤ 1 / (x + 1) - 1 / (x + 2) := by
  have h1 : 0 < x + 1 := by linarith
  have h2 : 0 < x + 2 := by linarith
  have hh : 0 < x + 3 / 2 := by linarith
  have he : 1 / (x + 1) - 1 / (x + 2) = 1 / ((x + 1) * (x + 2)) := by
    field_simp
    ring
  rw [he, div_le_div_iff₀ (pow_pos hh 4) (mul_pos h1 h2)]
  have hn : 0 ≤ x ^ 4 + 6 * x ^ 3 + (23 / 2) * x ^ 2 + (21 / 2) * x := by
    positivity
  nlinarith

theorem manuscript_reciprocal_fourth_range_sum_bound (n : ℕ) :
    (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1 / 2) ^ 4) ≤ 17 := by
  have hpartial : ∀ m : ℕ,
      (∑ j ∈ Finset.range (m + 1), 1 / ((j : ℝ) + 1 / 2) ^ 4) ≤
        17 - 1 / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have ht := manuscript_reciprocal_fourth_tail_bound (m : ℝ) (Nat.cast_nonneg m)
      have he : ((m + 1 : ℕ) : ℝ) + 1 / 2 = (m : ℝ) + 3 / 2 := by push_cast; ring
      rw [he]
      push_cast
      rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
      linarith
  cases n with
  | zero => simp
  | succ n =>
    have hn : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    exact (hpartial n).trans (by linarith)

theorem manuscript_reciprocal_fourth_finset_nat_sum_bound (s : Finset ℕ) :
    (∑ j ∈ s, 1 / ((j : ℝ) + 1 / 2) ^ 4) ≤ 17 := by
  have hs : s ⊆ Finset.range (s.sup id + 1) := by
    intro j hj
    have h := Finset.le_sup (f := id) hj
    simp only [id_eq] at h
    exact Finset.mem_range.2 (by omega)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)).trans
    (manuscript_reciprocal_fourth_range_sum_bound _)

theorem manuscript_reciprocal_fourth_int_upper_sum_bound (s : Finset ℤ) (k : ℤ)
    (hs : ∀ j ∈ s, k < j) :
    (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 17 := by
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
  exact manuscript_reciprocal_fourth_finset_nat_sum_bound _

theorem manuscript_reciprocal_fourth_int_lower_sum_bound (s : Finset ℤ) (k : ℤ)
    (hs : ∀ j ∈ s, j < k) :
    (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 17 := by
  have h := manuscript_reciprocal_fourth_int_upper_sum_bound
    (s.image (fun j => -j)) (-k) (by
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
  rwa [he] at h

theorem manuscript_reciprocal_fourth_int_sum_bound (s : Finset ℤ) (k : ℤ)
    (hs : ∀ j ∈ s, j ≠ k) :
    (∑ j ∈ s, 1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 34 := by
  classical
  have hp := manuscript_reciprocal_fourth_int_upper_sum_bound
    (s.filter (fun j => k < j)) k (by intro j hj; exact (Finset.mem_filter.1 hj).2)
  have hm := manuscript_reciprocal_fourth_int_lower_sum_bound
    (s.filter (fun j => ¬ k < j)) k (by
      intro j hj
      have hmem := Finset.mem_filter.1 hj
      have := hs j hmem.1
      omega)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j => k < j)]
  linarith

/-- The literal infinite lattice sum in the manuscript is strictly < 40. -/
theorem manuscript_reciprocal_fourth_int_tsum_lt_forty (k : ℤ) :
    (∑' j : ℤ, if j = k then 0 else
      1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) < 40 := by
  classical
  have hsum : ∀ s : Finset ℤ, (∑ j ∈ s, if j = k then (0 : ℝ) else
      1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 34 := by
    intro s
    have h := manuscript_reciprocal_fourth_int_sum_bound (s.filter (fun j => j ≠ k)) k
      (by intro j hj; exact (Finset.mem_filter.1 hj).2)
    simpa only [Finset.sum_filter, ne_eq, ite_not] using h
  have h := Real.tsum_le_of_sum_le (f := fun j : ℤ => if j = k then 0 else
    1 / (|(j : ℝ) - k| - 1 / 2) ^ 4)
    (by intro j; dsimp only [Pi.zero_apply]; split_ifs <;> positivity) hsum
  linarith

theorem manuscript_reciprocal_fourth_nat_filter_sum_bound (s : Finset ℕ) (k : ℤ) :
    (∑ j ∈ s.filter (fun j : ℕ => (j : ℤ) ≠ k),
      1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 40 := by
  classical
  let t := s.filter (fun j : ℕ => (j : ℤ) ≠ k)
  have h := manuscript_reciprocal_fourth_int_sum_bound (t.image (fun j : ℕ => (j : ℤ))) k (by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
    exact (Finset.mem_filter.1 ha).2)
  rw [Finset.sum_image (by intro a ha b hb hab; exact Int.ofNat_inj.1 hab)] at h
  have hh : (∑ j ∈ s.filter (fun j : ℕ => (j : ℤ) ≠ k),
      1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 34 := by
    simpa only [Int.cast_natCast] using h
  linarith

theorem manuscript_uniform_block_leakage_bound (P Q : CenteredFourthLaw)
    (p : ℝ) (_hp : p ∈ Icc 0 1) (n : ℕ) (k : ℤ)
    (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hw : ∀ j ≤ n, binomialWeight p n j ≤ B)
    (hfour : ∀ j ≤ n, (twoNoiseBlock P Q n j).fourthMoment ≤ M) :
    blockLeakageBudget P Q p n k ≤ 40 * B * M := by
  classical
  unfold blockLeakageBudget
  have h : (∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℤ) ≠ k),
      binomialWeight p n j * (twoNoiseBlock P Q n j).fourthMoment /
        (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℤ) ≠ k),
        B * M * (1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.1 (Finset.mem_filter.1 hj).1; omega
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (hw j hjn) (hfour j hjn)
      (by unfold CenteredFourthLaw.fourthMoment; exact integral_nonneg (fun x => by positivity)) hB
  apply h.trans
  rw [← Finset.mul_sum]
  have hm := mul_le_mul_of_nonneg_left
    (manuscript_reciprocal_fourth_nat_filter_sum_bound (Finset.range (n + 1)) k)
    (mul_nonneg hB hM)
  nlinarith only [hm]

end BerryEsseen
