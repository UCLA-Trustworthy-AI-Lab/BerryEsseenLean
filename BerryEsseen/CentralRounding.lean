import BerryEsseen.SmallVarianceSequence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def centralRoundedCell (n : ℕ) (t : ℝ) : ℕ := min n (Nat.floor (t + 1 / 2))

theorem centralRoundedCell_le (n : ℕ) (t : ℝ) : centralRoundedCell n t ≤ n := min_le_left _ _

theorem centralRoundedCell_offset (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t + 1 / 2) (htn : t + 1 / 2 ≤ n) :
    |t - (centralRoundedCell n t : ℝ)| ≤ 1 / 2 := by
  have hf : Nat.floor (t + 1 / 2) ≤ n := Nat.floor_le_of_le htn
  rw [centralRoundedCell, min_eq_right hf]
  have hlo := Nat.floor_le ht0
  have hhi := Nat.lt_floor_add_one (t + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

theorem central_rounding_sequence (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (t : ℕ → ℝ) (ht : Tendsto (fun j => (t j - (n j : ℝ) * p j) / Real.sqrt (n j : ℝ)) atTop (𝓝 0)) :
    (∀ᶠ j in atTop, |t j - (centralRoundedCell (n j) (t j) : ℝ)| ≤ 1 / 2) ∧
    Tendsto (fun j => binomialZ (p j) (n j) (centralRoundedCell (n j) (t j))) atTop (𝓝 0) := by
  let k := fun j => centralRoundedCell (n j) (t j)
  let r := fun j => Real.sqrt (n j : ℝ)
  have hr : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hn0 : ∀ j, (0 : ℝ) < n j := fun j => by exact_mod_cast (show 0 < n j by have := hn1 j; omega)
  have hr0 : ∀ j, 0 < r j := fun j => Real.sqrt_pos.2 (hn0 j)
  have hoff : ∀ᶠ j in atTop, |t j - (k j : ℝ)| ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.1 ht 1 (by norm_num), hr.eventually_ge_atTop 10] with j hj hjr
    have h := hj.le
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hr0 j)] at h
    have hc := abs_le.1 ((div_le_iff₀ (hr0 j)).1 h)
    have hpj := hp j
    have hs : (r j) ^ 2 = (n j : ℝ) := Real.sq_sqrt (hn0 j).le
    have h1 := mul_le_mul_of_nonneg_left hpj.1 (hn0 j).le
    have h2 := mul_le_mul_of_nonneg_left hpj.2 (hn0 j).le
    have hr10 : 10 * r j ≤ (r j) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hjr) (hr0 j).le]
    apply centralRoundedCell_offset
    · nlinarith only [hc.1, h1, hr10, hs, hjr]
    · nlinarith only [hc.2, h2, hr10, hs, hjr]
  refine ⟨hoff, ?_⟩
  have herr : Tendsto (fun j => ((k j : ℝ) - t j) / r j) atTop (𝓝 (0 : ℝ)) := by
    have hbound : Tendsto (fun j => (1 / 2 : ℝ) / r j) atTop (𝓝 (0 : ℝ)) := (tendsto_const_nhds (x := (1 / 2 : ℝ))).div_atTop hr
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hoff, hbound.eventually (gt_mem_nhds hε)] with j hj hjb
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hr0 j), abs_sub_comm]
    exact (div_le_div_of_nonneg_right hj (hr0 j).le).trans_lt hjb
  have hkcenter : Tendsto (fun j => ((k j : ℝ) - (n j : ℝ) * p j) / r j) atTop (𝓝 (0 : ℝ)) := by
    have h := ht.add herr
    simp only [zero_add] at h
    convert h using 1
    funext j
    ring
  have hσ : Tendsto (fun j => Real.sqrt (p j * (1 - p j))) atTop (𝓝 sigmaE) :=
    (hplim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hplim)).sqrt
  have h := hkcenter.div hσ sigmaE_pos.ne'
  simp only [zero_div] at h
  convert h using 1
  funext j
  unfold binomialZ
  simp only [Int.cast_natCast]
  rw [mul_assoc (n j : ℝ), Real.sqrt_mul (hn0 j).le]
  dsimp only [Pi.div_apply, k, r]
  rw [div_div]

end BerryEsseen
