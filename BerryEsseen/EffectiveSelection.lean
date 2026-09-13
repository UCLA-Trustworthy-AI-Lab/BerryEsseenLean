import BerryEsseen.ClassicalBounds
import BerryEsseen.EffectiveSupport
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def finiteHalfIndex (N : ℕ) : ℕ := (N + 1) / 2

theorem finiteHalfIndex_bounds (N : ℕ) (hN : 4 ≤ N) :
    2 ≤ finiteHalfIndex N ∧ finiteHalfIndex N ≤ N ∧
    2 * finiteHalfIndex N ≤ N + 1 ∧ N - 2 ≤ 2 * (finiteHalfIndex N - 1) := by
  unfold finiteHalfIndex
  omega

theorem finite_half_harmonic_lower (N : ℕ) (hN : 4 ≤ N) :
    Real.log 2 ≤ ∑ j ∈ Finset.Icc (finiteHalfIndex N) N, (j : ℝ)⁻¹ := by
  let m := finiteHalfIndex N
  have hm := finiteHalfIndex_bounds N hN
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmb : m ≤ N + 1 := by omega
  have hanti : AntitoneOn (fun x : ℝ => x⁻¹) (Icc (m : ℝ) (N + 1 : ℕ)) :=
    inv_antitoneOn_Icc_right hm0
  have hi := hanti.integral_le_sum_Ico hmb
  rw [integral_inv (by
    rw [Set.uIcc_of_le (by exact_mod_cast hmb)]
    simp only [mem_Icc, not_and]
    intro hh
    linarith), Finset.Ico_add_one_right_eq_Icc] at hi
  have hrat : (2 : ℝ) ≤ (N + 1 : ℕ) / (m : ℝ) := by
    apply (le_div_iff₀ hm0).mpr
    exact_mod_cast hm.2.2.1
  exact (Real.log_le_log (by norm_num) hrat).trans hi

theorem finite_interval_scaled_selection (a : ℕ → ℝ) (m N : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N)
    (A : ℝ) (hA : 0 ≤ A) (hend : 0 < a N) (hstart : a (m - 1) ≤ A)
    (hS : 0 < ∑ j ∈ Finset.Icc m N, (j : ℝ)⁻¹) :
    ∃ j, m ≤ j ∧ j ≤ N ∧ 0 < a j ∧
      scaledDrop a j ≤ A / (∑ k ∈ Finset.Icc m N, (k : ℝ)⁻¹) := by
  let S := ∑ j ∈ Finset.Icc m N, (j : ℝ)⁻¹
  let D := A / S
  let b := fun i => a (m - 1 + i)
  let w := fun i : ℕ => D * ((m + i : ℕ) : ℝ)⁻¹
  have hD : 0 ≤ D := div_nonneg hA hS.le
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp only [w]; positivity
  have hsum : (∑ i ∈ Finset.range (N + 1 - m), ((m + i : ℕ) : ℝ)⁻¹) = S := by
    dsimp only [S]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have hb : 0 < b (N + 1 - m) := by
    dsimp only [b]
    convert hend using 1 <;> congr 1 <;> omega
  have hbudget : b 0 ≤ ∑ i ∈ Finset.range (N + 1 - m), w i := by
    dsimp only [w]
    rw [← Finset.mul_sum, hsum]
    have he : D * S = A := div_mul_cancel₀ A (show S ≠ 0 from hS.ne')
    simpa [b, he] using hstart
  obtain ⟨i, hi, hpos, hdiff⟩ := finite_selection b w hw (N + 1 - m) hb hbudget
  let j := m + i
  have hjm : m ≤ j := by dsimp only [j]; omega
  have hjN : j ≤ N := by dsimp only [j]; omega
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hp : 0 < a j := by
    dsimp only [b] at hpos
    convert hpos using 1 <;> dsimp only [j] <;> congr 1 <;> omega
  have hd : a (j - 1) - a j ≤ D / (j : ℝ) := by
    dsimp only [b, w] at hdiff
    have he1 : m - 1 + i = j - 1 := by dsimp only [j]; omega
    have he2 : m - 1 + (i + 1) = j := by dsimp only [j]; omega
    simpa only [he1, he2, ← div_eq_mul_inv] using hdiff
  refine ⟨j, hjm, hjN, hp, ?_⟩
  change (j : ℝ) * max (a (j - 1) - a j) 0 ≤ D
  calc
    _ ≤ (j : ℝ) * (D / (j : ℝ)) := mul_le_mul_of_nonneg_left (max_le hd (by positivity)) hj0.le
    _ = D := by field_simp

theorem effective_extremal_finite_selection (H : ClassicalBerryEsseenBounds)
    (N : ℕ) (hN : 4 ≤ N) (hviol : cE < extremalConstant N) :
    ∃ n, finiteHalfIndex N ≤ n ∧ n ≤ N ∧ cE < extremalConstant n ∧
      scaledDrop extremalConstant n < 0.086 ∧
      scaledDrop extremalConstant n ≤ 10 / Real.sqrt ((N - 2 : ℕ) : ℝ) := by
  let m := finiteHalfIndex N
  let S := ∑ j ∈ Finset.Icc m N, (j : ℝ)⁻¹
  let A := min ((0.469 : ℝ) - cE) (4.75 / Real.sqrt ((m - 1 : ℕ) : ℝ))
  have hm := finiteHalfIndex_bounds N hN
  have hm2 : 2 ≤ m := hm.1
  have hmN : m ≤ N := hm.2.1
  have hm1pos : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (by omega : 0 < m - 1)
  have hroot1 : 0 < Real.sqrt ((m - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hm1pos
  have hroot2 : 0 < Real.sqrt ((N - 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N - 2))
  have hSlog : Real.log 2 ≤ S := finite_half_harmonic_lower N hN
  have hS69 : (0.69 : ℝ) < S := by linarith [Real.log_two_gt_d9]
  have hS : 0 < S := by linarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact le_min (by linarith [cE_numeric_bounds.2]) (by positivity)
  have hstart : extremalConstant (m - 1) - cE ≤ A := by
    have hc := extremalConstant_bounds H (m - 1) (by omega)
    exact le_min (by linarith [hc.1]) (by linarith [hc.2])
  obtain ⟨n, hnm, hnN, hpos, hd⟩ := finite_interval_scaled_selection
    (fun j => extremalConstant j - cE) m N (by omega) hmN A hA (by linarith) hstart hS
  have hd' : scaledDrop extremalConstant n ≤ A / S := by
    convert hd using 1
    unfold scaledDrop
    congr 2
    ring
  have hnum1 : A ≤ (0.469 : ℝ) - cE := min_le_left _ _
  have hD1 : A / S < 0.086 := (div_lt_iff₀ hS).mpr (by linarith [cE_numeric_bounds.1])
  have hnum2 : A ≤ 4.75 / Real.sqrt ((m - 1 : ℕ) : ℝ) := min_le_right _ _
  have hcast : ((N - 2 : ℕ) : ℝ) ≤ 2 * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hm.2.2.2
  have hrootratio : Real.sqrt ((N - 2 : ℕ) : ℝ) ≤ (1.42 : ℝ) * Real.sqrt ((m - 1 : ℕ) : ℝ) := by
    have hs1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m - 1 : ℕ))
    have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N - 2 : ℕ))
    nlinarith only [hs1, hs2, hcast, hroot1, hroot2, hm1pos]
  have hD2 : A / S ≤ 10 / Real.sqrt ((N - 2 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hS hroot2).mpr
    calc
      _ ≤ (4.75 / Real.sqrt ((m - 1 : ℕ) : ℝ)) * ((1.42 : ℝ) * Real.sqrt ((m - 1 : ℕ) : ℝ)) :=
        mul_le_mul hnum2 hrootratio hroot2.le (by positivity)
      _ = (6.745 : ℝ) := by field_simp; norm_num
      _ ≤ 10 * S := by linarith
  exact ⟨n, hnm, hnN, by linarith, hd'.trans_lt hD1, hd'.trans hD2⟩

theorem finiteHalfIndex_eq_ceil (N : ℕ) (hN : 4 ≤ N) :
    finiteHalfIndex N = Nat.ceil ((N : ℝ) / 2) := by
  have hm := finiteHalfIndex_bounds N hN
  symm
  apply (Nat.ceil_eq_iff (by omega : finiteHalfIndex N ≠ 0)).mpr
  have hlow : 2 * (finiteHalfIndex N - 1) < N := by unfold finiteHalfIndex; omega
  have hupp : N ≤ 2 * finiteHalfIndex N := by unfold finiteHalfIndex; omega
  constructor
  · have h : 2 * ((finiteHalfIndex N - 1 : ℕ) : ℝ) < N := by exact_mod_cast hlow
    linarith
  · have h : (N : ℝ) ≤ 2 * (finiteHalfIndex N : ℝ) := by exact_mod_cast hupp
    linarith

theorem effective_selection_with_support (H : ClassicalBerryEsseenBounds)
    (N : ℕ) (hN : 4 ≤ N) (hviol : cE < extremalConstant N) :
    ∃ n, finiteHalfIndex N ≤ n ∧ n ≤ N ∧ cE < extremalConstant n ∧
      scaledDrop extremalConstant n < 0.086 ∧
      scaledDrop extremalConstant n ≤ 10 / Real.sqrt ((N - 2 : ℕ) : ℝ) ∧
      ∀ (P : StandardizedLaw) (t : ℝ), signedRatio P (n - 1) t = extremalConstant n →
        P.measure.support ⊆ Ioo (-6) 6 := by
  obtain ⟨n, hnm, hnN, hcn, hd1, hd2⟩ := effective_extremal_finite_selection H N hN hviol
  have hn2 : 2 ≤ n := (finiteHalfIndex_bounds N hN).1.trans hnm
  refine ⟨n, hnm, hnN, hcn, hd1, hd2, ?_⟩
  intro P t hattain
  have he : n - 1 + 1 = n := by omega
  apply extremizer_support_subset_six H P (n - 1) (by omega) t
  · simpa only [he] using hattain
  · rwa [hattain]
  · rw [he]
    linarith

theorem effective_selection (H : ClassicalBerryEsseenBounds)
    (N : ℕ) (hN : 4 ≤ N) (hviol : cE < extremalConstant N) :
    ∃ n, Nat.ceil ((N : ℝ) / 2) ≤ n ∧ n ≤ N ∧ cE < extremalConstant n ∧
      scaledDrop extremalConstant n < 0.086 ∧
      scaledDrop extremalConstant n ≤ 10 / Real.sqrt ((N - 2 : ℕ) : ℝ) ∧
      ∀ (P : StandardizedLaw) (t : ℝ), signedRatio P (n - 1) t = extremalConstant n →
        P.measure.support ⊆ Icc (-6) 6 := by
  obtain ⟨n, hnm, hnN, hcn, hd1, hd2, hsupp⟩ := effective_selection_with_support H N hN hviol
  refine ⟨n, ?_, hnN, hcn, hd1, hd2, fun P t hat => (hsupp P t hat).trans Ioo_subset_Icc_self⟩
  rwa [← finiteHalfIndex_eq_ceil N hN]

end BerryEsseen
