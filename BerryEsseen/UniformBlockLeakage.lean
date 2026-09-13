import BerryEsseen.BlockLeakage
import BerryEsseen.ReciprocalFourthSum

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem reciprocal_fourth_nat_filter_sum_bound (s : Finset ℕ) (k : ℤ) :
    (∑ j ∈ s.filter (fun j : ℕ => (j : ℤ) ≠ k),
      1 / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤ 64 := by
  classical
  let t := s.filter (fun j : ℕ => (j : ℤ) ≠ k)
  have h := reciprocal_fourth_int_sum_bound (t.image (fun j : ℕ => (j : ℤ))) k (by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
    exact (Finset.mem_filter.1 ha).2)
  rw [Finset.sum_image (by intro a ha b hb hab; exact Int.ofNat_inj.1 hab)] at h
  simpa only [Int.cast_natCast] using h

theorem uniform_block_leakage_bound (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (k : ℤ) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hw : ∀ j ≤ n, binomialWeight p n j ≤ B)
    (hfour : ∀ j ≤ n, (twoNoiseBlock P Q n j).fourthMoment ≤ M) :
    blockLeakageBudget P Q p n k ≤ 64 * B * M := by
  classical
  unfold blockLeakageBudget
  have h : (∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => (j : ℤ) ≠ k),
      binomialWeight p n j * (twoNoiseBlock P Q n j).fourthMoment / (|(j : ℝ) - k| - 1 / 2) ^ 4) ≤
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
  have hm := mul_le_mul_of_nonneg_left (reciprocal_fourth_nat_filter_sum_bound (Finset.range (n + 1)) k) (mul_nonneg hB hM)
  nlinarith only [hm]

def accumulatedNoiseVariance (P Q : CenteredFourthLaw) (p : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ((1 - p) * P.secondMoment + p * Q.secondMoment)

theorem accumulatedNoiseVariance_nonneg (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) :
    0 ≤ accumulatedNoiseVariance P Q p n := by
  unfold accumulatedNoiseVariance
  exact mul_nonneg (Nat.cast_nonneg n) (add_nonneg
    (mul_nonneg (sub_nonneg.2 hp.2) P.secondMoment_nonneg)
    (mul_nonneg hp.1 Q.secondMoment_nonneg))

theorem noise_variance_uniform_bound (P Q : CenteredFourthLaw) (p δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (n j : ℕ) (hj : j ≤ n) :
    (twoNoiseBlock P Q n j).secondMoment ≤ accumulatedNoiseVariance P Q p n / δ := by
  rw [twoNoiseBlock_variance, Nat.cast_sub hj]
  apply (le_div_iff₀ hδ).2
  unfold accumulatedNoiseVariance
  have hP := P.secondMoment_nonneg
  have hQ := Q.secondMoment_nonneg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hsum : ((n : ℝ) - j) * P.secondMoment + j * Q.secondMoment ≤ n * (P.secondMoment + Q.secondMoment) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hjn) hQ, mul_nonneg hj0 hP]
  have hmix : δ * (P.secondMoment + Q.secondMoment) ≤ (1 - p) * P.secondMoment + p * Q.secondMoment := by
    nlinarith [mul_nonneg (sub_nonneg.2 hp) hQ, mul_nonneg (sub_nonneg.2 hq) hP]
  have ha := mul_le_mul_of_nonneg_right hsum hδ.le
  have hb := mul_le_mul_of_nonneg_left hmix hn
  nlinarith only [ha, hb]

theorem noise_fourth_uniform_bound (P Q : CenteredFourthLaw) (p δ ε : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n j : ℕ) (hj : j ≤ n) :
    (twoNoiseBlock P Q n j).fourthMoment ≤
      3 * (accumulatedNoiseVariance P Q p n / δ) ^ 2 + ε ^ 2 * (accumulatedNoiseVariance P Q p n / δ) := by
  have h := twoNoiseBlock_fourth_bound P Q n j ε hε hP hQ
  rw [← twoNoiseBlock_variance] at h
  apply h.trans
  have hv := noise_variance_uniform_bound P Q p δ hδ hp hq n j hj
  have hv0 := (twoNoiseBlock P Q n j).secondMoment_nonneg
  nlinarith [sq_nonneg (accumulatedNoiseVariance P Q p n / δ - (twoNoiseBlock P Q n j).secondMoment),
    mul_nonneg (sub_nonneg.2 hv) (sq_nonneg ε),
    mul_nonneg (sub_nonneg.2 hv) hv0]

theorem noise_variance_central_identity (P Q : CenteredFourthLaw) (p : ℝ) (n j : ℕ) (hj : j ≤ n) :
    (twoNoiseBlock P Q n j).secondMoment - accumulatedNoiseVariance P Q p n =
      ((j : ℝ) - n * p) * (Q.secondMoment - P.secondMoment) := by
  rw [twoNoiseBlock_variance, Nat.cast_sub hj, accumulatedNoiseVariance]
  ring

end BerryEsseen
