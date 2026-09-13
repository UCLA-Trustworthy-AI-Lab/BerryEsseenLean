import BerryEsseen.RawMaximalSpan
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem finite_nat_gcd_bezout (F : Finset ℕ) :
    ∃ c : ℕ → ℤ, (∑ d ∈ F, c d * (d : ℤ)) = ((F.gcd (id : ℕ → ℕ) : ℕ) : ℤ) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨c, hc⟩ := ih
    let A := Nat.gcdA a (F.gcd id)
    let B := Nat.gcdB a (F.gcd id)
    let c' : ℕ → ℤ := fun d => if d = a then A else B * c d
    refine ⟨c', ?_⟩
    rw [Finset.sum_insert ha]
    have htail : (∑ d ∈ F, c' d * (d : ℤ)) = B * ((F.gcd (id : ℕ → ℕ) : ℕ) : ℤ) := by
      calc
        _ = ∑ d ∈ F, B * (c d * (d : ℤ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hda : d ≠ a := by intro he; subst d; exact ha hd
          simp only [c', if_neg hda]
          ring
        _ = _ := by rw [← Finset.mul_sum, hc]
    rw [htail, Finset.gcd_insert]
    have hb := Nat.gcd_eq_gcd_ab a (F.gcd id)
    change c' a * (a : ℤ) + B * ((F.gcd (id : ℕ → ℕ) : ℕ) : ℤ) = (Nat.gcd a (F.gcd id) : ℤ)
    simp only [c', if_pos rfl]
    dsimp [A, B]
    linarith only [hb]

theorem finite_bounded_bezout (F : Finset ℕ) (M m : ℕ)
    (hM : ∀ d ∈ F, d ≤ M) (hm : m ∈ F) (hm0 : 0 < m) (hgcd : F.gcd id = 1) :
    ∃ (b : ℕ → ℤ) (t : ℤ),
      (∑ d ∈ F, b d * (d : ℤ)) + t * (m : ℤ) = 1 ∧
      (∀ d ∈ F, 0 ≤ b d ∧ b d ≤ M) ∧
      (∑ d ∈ F, |b d|) + |t| ≤ 2 * (F.card : ℤ) * (M : ℤ) + 1 := by
  obtain ⟨c, hc⟩ := finite_nat_gcd_bezout F
  rw [hgcd, Nat.cast_one] at hc
  let b : ℕ → ℤ := fun d => c d % (m : ℤ)
  let t : ℤ := ∑ d ∈ F, c d / (m : ℤ) * (d : ℤ)
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm0
  have hmM : (m : ℤ) ≤ M := by exact_mod_cast hM m hm
  have hb0 (d : ℕ) : 0 ≤ b d := Int.emod_nonneg _ hmpos.ne'
  have hbm (d : ℕ) : b d ≤ m := (Int.emod_lt_of_pos (c d) hmpos).le
  have heq : (∑ d ∈ F, b d * (d : ℤ)) + t * (m : ℤ) = 1 := by
    rw [show t * (m : ℤ) = ∑ d ∈ F, (c d / (m : ℤ) * (d : ℤ)) * (m : ℤ) by
      dsimp [t]; rw [Finset.sum_mul], ← Finset.sum_add_distrib]
    calc
      _ = ∑ d ∈ F, c d * (d : ℤ) := by
        apply Finset.sum_congr rfl
        intro d hd
        have h := Int.emod_add_mul_ediv (c d) (m : ℤ)
        change c d % (m : ℤ) * (d : ℤ) + (c d / (m : ℤ) * (d : ℤ)) * (m : ℤ) = _
        nlinarith only [congrArg (fun z : ℤ => z * (d : ℤ)) h]
      _ = 1 := hc
  have hS0 : (0 : ℤ) ≤ ∑ d ∈ F, b d * (d : ℤ) :=
    Finset.sum_nonneg (fun d hd => mul_nonneg (hb0 d) (Nat.cast_nonneg d))
  have hS : (∑ d ∈ F, b d * (d : ℤ)) ≤ (F.card : ℤ) * (m : ℤ) * (M : ℤ) := by
    calc
      _ ≤ ∑ _d ∈ F, (m : ℤ) * (M : ℤ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul (hbm d) (by exact_mod_cast hM d hd) (Nat.cast_nonneg d) hmpos.le
      _ = _ := by simp; ring
  have ht : |t| ≤ (F.card : ℤ) * (M : ℤ) + 1 := by
    rw [abs_le]
    constructor
    · apply le_of_mul_le_mul_left (a := (m : ℤ)) _ hmpos
      nlinarith only [heq, hS, hmpos]
    · apply le_of_mul_le_mul_left (a := (m : ℤ)) _ hmpos
      have hp : 0 ≤ (m : ℤ) * ((F.card : ℤ) * (M : ℤ)) := by positivity
      nlinarith only [heq, hS0, hp, hmpos]
  have hbsum : (∑ d ∈ F, |b d|) ≤ (F.card : ℤ) * (M : ℤ) := by
    calc
      _ ≤ ∑ _d ∈ F, (M : ℤ) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_of_nonneg (hb0 d)]
        exact (hbm d).trans hmM
      _ = _ := by simp
  exact ⟨b, t, heq, (fun d hd => ⟨hb0 d, (hbm d).trans hmM⟩), by nlinarith only [ht, hbsum]⟩

end BerryEsseen
