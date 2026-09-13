import BerryEsseen.ManuscriptCayleyBezout

/-! Extract a simple Cayley path and correct its integer sum by a multiple
of the chosen modulus. This proves the manuscript's actual 4000 budget. -/
noncomputable section
open Set Function
namespace BerryEsseen

theorem manuscript_finite_bezout_four_thousand (D : Finset ℕ)
    (hM : ∀ d ∈ D, d ≤ 2000) (hgcd : D.gcd id = 1) :
    ∃ c : ℕ → ℤ, (∑ d ∈ D, c d * (d : ℤ)) = 1 ∧
      (∑ d ∈ D, |c d|) ≤ 4000 := by
  classical
  obtain ⟨m, hm, hmpos⟩ : ∃ m ∈ D, 0 < m := by
    by_contra! hh
    have hzero : D.gcd id = 0 := Finset.gcd_eq_zero_iff.mpr (fun d hd => by
      have hz := hh d hd
      simpa only [id_eq] using Nat.eq_zero_of_le_zero hz)
    rw [hgcd] at hzero
    norm_num at hzero
  have hmM : m ≤ 2000 := hM m hm
  by_cases hm1 : m = 1
  · subst m
    refine ⟨fun d => if d = 1 then 1 else 0, ?_, ?_⟩
    · simp only [ite_mul, one_mul, zero_mul]
      simp [hm]
    · simp_rw [apply_ite abs]
      norm_num [hm]
  · letI : NeZero m := ⟨by omega⟩
    -- Connectivity is used only to obtain a simple path. Its vertices are
    -- distinct, so it has at most m-1 signed generator edges.
    obtain ⟨p, hp⟩ := (manuscript_cayley_connected D m hgcd).exists_isPath 0 1
    have hplen : p.length < m := by simpa only [ZMod.card] using hp.length_lt
    obtain ⟨b, hbmod, hblength⟩ := manuscript_cayley_walk_coefficients D m p
    let S : ℤ := ∑ d ∈ D, b d * (d : ℤ)
    have hb : (∑ d ∈ D, |b d|) ≤ (m : ℤ) - 1 := by
      have hpz : (p.length : ℤ) < m := by exact_mod_cast hplen
      omega
    have hS : |S| ≤ 2000 * ((m : ℤ) - 1) := by
      calc
        _ ≤ ∑ d ∈ D, |b d * (d : ℤ)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ d ∈ D, |b d| * (d : ℤ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [abs_mul]
          congr 1
          exact abs_of_nonneg (Nat.cast_nonneg d)
        _ ≤ ∑ d ∈ D, |b d| * 2000 := by
          apply Finset.sum_le_sum
          intro d hd
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hM d hd) (abs_nonneg _)
        _ = (∑ d ∈ D, |b d|) * 2000 := by rw [Finset.sum_mul]
        _ ≤ _ := by nlinarith
    have hdiv : (m : ℤ) ∣ S - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (S - 1) m).mp
      have hSmod : (S : ZMod m) = 1 := by simpa only [sub_zero] using hbmod
      rw [Int.cast_sub, Int.cast_one, hSmod, sub_self]
    obtain ⟨q, hq⟩ := hdiv
    have hqbound : |q| ≤ 2000 := by
      have hab : |(m : ℤ) * q| ≤ 2000 * ((m : ℤ) - 1) + 1 := by
        rw [← hq]
        have h := abs_sub S (1 : ℤ)
        rw [abs_one] at h
        linarith
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hab
      have hmp : (0 : ℤ) < m := by exact_mod_cast hmpos
      apply le_of_mul_le_mul_left (a := (m : ℤ)) _ hmp
      nlinarith
    let c : ℕ → ℤ := fun d => b d - if d = m then q else 0
    have heq : (∑ d ∈ D, c d * (d : ℤ)) = S - q * (m : ℤ) := by
      simp only [c, sub_mul, Finset.sum_sub_distrib]
      dsimp only [S]
      congr 1
      simp only [ite_mul, zero_mul]
      simp [hm]
    refine ⟨c, ?_, ?_⟩
    · rw [heq]
      nlinarith only [hq]
    · have hc : (∑ d ∈ D, |c d|) ≤ (∑ d ∈ D, |b d|) + |q| := by
        calc
          _ ≤ ∑ d ∈ D, (|b d| + |if d = m then q else 0|) := by
            apply Finset.sum_le_sum
            intro d hd
            exact abs_sub _ _
          _ = _ := by
            rw [Finset.sum_add_distrib]
            simp_rw [apply_ite abs, abs_zero]
            simp [hm]
      have hmMz : (m : ℤ) ≤ 2000 := by exact_mod_cast hmM
      linarith

end BerryEsseen
