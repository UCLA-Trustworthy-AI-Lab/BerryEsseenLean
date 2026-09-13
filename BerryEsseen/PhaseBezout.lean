import BerryEsseen.FiniteBezout

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem realPhase_sum_chord (x y : ℝ) :
    ‖realPhase (x + y) 1 - 1‖ ≤ ‖realPhase x 1 - 1‖ + ‖realPhase y 1 - 1‖ := by
  rw [realPhase_add]
  have he : realPhase x 1 * realPhase y 1 - 1 =
      realPhase x 1 * (realPhase y 1 - 1) + (realPhase x 1 - 1) := by ring
  rw [he]
  have h := norm_add_le (realPhase x 1 * (realPhase y 1 - 1)) (realPhase x 1 - 1)
  rw [norm_mul, realPhase_norm, one_mul] at h
  linarith only [h]

theorem realPhase_neg_chord (x : ℝ) : ‖realPhase (-x) 1 - 1‖ = ‖realPhase x 1 - 1‖ := by
  have h := realPhase_difference_chord 1 0 x
  simpa only [realPhase, one_mul, mul_one, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, zero_sub, norm_sub_rev (1 : ℂ)] using h

theorem realPhase_nat_mul_chord (n : ℕ) (x : ℝ) :
    ‖realPhase ((n : ℝ) * x) 1 - 1‖ ≤ (n : ℝ) * ‖realPhase x 1 - 1‖ := by
  induction n with
  | zero => simp [realPhase]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    have h := realPhase_sum_chord ((n : ℝ) * x) x
    nlinarith only [h, ih]

theorem realPhase_int_mul_chord (n : ℤ) (x : ℝ) :
    ‖realPhase ((n : ℝ) * x) 1 - 1‖ ≤ |(n : ℝ)| * ‖realPhase x 1 - 1‖ := by
  cases n with
  | ofNat n => simpa using realPhase_nat_mul_chord n x
  | negSucc n =>
    have he : ((Int.negSucc n : ℤ) : ℝ) * x = -(((n + 1 : ℕ) : ℝ) * x) := by push_cast; ring
    rw [he, realPhase_neg_chord]
    have hn : ((Int.negSucc n : ℤ) : ℝ) = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hn, abs_neg, abs_of_nonneg (Nat.cast_nonneg (n + 1))]
    exact realPhase_nat_mul_chord (n + 1) x

theorem realPhase_finset_sum_chord {ι : Type*} (F : Finset ι) (v : ι → ℝ) :
    ‖realPhase (∑ i ∈ F, v i) 1 - 1‖ ≤ ∑ i ∈ F, ‖realPhase (v i) 1 - 1‖ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [realPhase]
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (realPhase_sum_chord _ _).trans (by linarith only [ih])

theorem finite_bezout_phase_chord (F : Finset ℕ) (b : ℕ → ℤ) (t : ℤ) (m : ℕ)
    (heq : (∑ d ∈ F, b d * (d : ℤ)) + t * (m : ℤ) = 1)
    (x C L : ℝ) (hC : 0 ≤ C)
    (hb : ∀ d ∈ F, ‖realPhase ((d : ℝ) * x) 1 - 1‖ ≤ C)
    (hm : ‖realPhase ((m : ℝ) * x) 1 - 1‖ ≤ C)
    (hL : (∑ d ∈ F, |(b d : ℝ)|) + |(t : ℝ)| ≤ L) :
    ‖realPhase x 1 - 1‖ ≤ L * C := by
  have heqR : (∑ d ∈ F, (b d : ℝ) * (d : ℝ)) + (t : ℝ) * (m : ℝ) = 1 := by exact_mod_cast heq
  have hx : x = (∑ d ∈ F, (b d : ℝ) * ((d : ℝ) * x)) + (t : ℝ) * ((m : ℝ) * x) := by
    have h := congrArg (fun y : ℝ => y * x) heqR
    dsimp only at h
    rw [add_mul, Finset.sum_mul, one_mul] at h
    convert h.symm using 1 <;> simp_rw [mul_assoc]
  have hs := realPhase_finset_sum_chord F (fun d => (b d : ℝ) * ((d : ℝ) * x))
  have hsb : (∑ d ∈ F, ‖realPhase ((b d : ℝ) * ((d : ℝ) * x)) 1 - 1‖) ≤
      (∑ d ∈ F, |(b d : ℝ)|) * C := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro d hd
    exact (realPhase_int_mul_chord (b d) ((d : ℝ) * x)).trans
      (mul_le_mul_of_nonneg_left (hb d hd) (abs_nonneg _))
  have htb := (realPhase_int_mul_chord t ((m : ℝ) * x)).trans
    (mul_le_mul_of_nonneg_left hm (abs_nonneg _))
  have hsum := realPhase_sum_chord (∑ d ∈ F, (b d : ℝ) * ((d : ℝ) * x)) ((t : ℝ) * ((m : ℝ) * x))
  rw [← hx] at hsum
  have hbudget := mul_le_mul_of_nonneg_right hL hC
  nlinarith only [hsum, hs, hsb, htb, hbudget]

end BerryEsseen
