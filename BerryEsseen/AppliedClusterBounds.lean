import BerryEsseen.PublishedBernoulli
import BerryEsseen.UniformBlockLeakage
import BerryEsseen.ExactMomentInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem actual_twoCluster_leakage_bound (S : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p δ ε : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    blockLeakageBudget P Q p n k ≤
      (128 * cE / (δ * Real.sqrt (n : ℝ))) *
        (3 * (accumulatedNoiseVariance P Q p n / δ) ^ 2 + ε ^ 2 * (accumulatedNoiseVariance P Q p n / δ)) := by
  have hpI : p ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
  have hlam := accumulatedNoiseVariance_nonneg P Q p hpI n
  have hc := cE_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := uniform_block_leakage_bound P Q p hpI n k (2 * cE / (δ * Real.sqrt (n : ℝ)))
    (3 * (accumulatedNoiseVariance P Q p n / δ) ^ 2 + ε ^ 2 * (accumulatedNoiseVariance P Q p n / δ))
    (by positivity) (by positivity)
    (fun j hj => binomialWeight_uniform_bound S p δ hδ hp hq n j hn hj)
    (fun j hj => noise_fourth_uniform_bound P Q p δ ε hδ hp hq hε hP hQ n j hj)
  convert h using 1 <;> ring

theorem conditional_variance_sum_bound (P Q : CenteredFourthLaw) (p δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (n : ℕ) (hn : 1 ≤ n) :
    P.secondMoment + Q.secondMoment ≤ accumulatedNoiseVariance P Q p n / ((n : ℝ) * δ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ (mul_pos hn0 hδ)).2
  unfold accumulatedNoiseVariance
  have hmix : δ * (P.secondMoment + Q.secondMoment) ≤ (1 - p) * P.secondMoment + p * Q.secondMoment := by
    nlinarith [mul_nonneg (sub_nonneg.2 hp) Q.secondMoment_nonneg,
      mul_nonneg (sub_nonneg.2 hq) P.secondMoment_nonneg]
  have h := mul_le_mul_of_nonneg_left hmix hn0.le
  nlinarith only [h]

theorem noise_variance_central_bound (P Q : CenteredFourthLaw) (p δ M : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hM : 0 ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (hcentral : |(k : ℝ) - n * p| ≤ M * Real.sqrt (n : ℝ)) :
    |(twoNoiseBlock P Q n k).secondMoment - accumulatedNoiseVariance P Q p n| ≤
      M * accumulatedNoiseVariance P Q p n / (δ * Real.sqrt (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hv := conditional_variance_sum_bound P Q p δ hδ hp hq n hn
  have hdiff : |Q.secondMoment - P.secondMoment| ≤ P.secondMoment + Q.secondMoment := by
    rw [abs_le]
    constructor <;> linarith [P.secondMoment_nonneg, Q.secondMoment_nonneg]
  rw [noise_variance_central_identity P Q p n k hk, abs_mul]
  have h := mul_le_mul hcentral (hdiff.trans hv) (abs_nonneg _) (mul_nonneg hM hs.le)
  apply h.trans_eq
  field_simp [hδ.ne', hs.ne', hn0.ne']
  rw [Real.sq_sqrt hn0.le]
  ring

theorem noise_absoluteMoment_central_lower (P Q : CenteredFourthLaw) (p δ ε M : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hcentral : |(k : ℝ) - n * p| ≤ M * Real.sqrt (n : ℝ))
    (hlarge : 2 * M ≤ δ * Real.sqrt (n : ℝ))
    (hlam : 0 < accumulatedNoiseVariance P Q p n) :
    accumulatedNoiseVariance P Q p n /
      (2 * Real.sqrt (3 * accumulatedNoiseVariance P Q p n / δ + ε ^ 2)) ≤
      (twoNoiseBlock P Q n k).absoluteMoment := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < δ * Real.sqrt (n : ℝ) := mul_pos hδ (Real.sqrt_pos.2 hn0)
  have hclose := noise_variance_central_bound P Q p δ M hδ hp hq hM n k hn hk hcentral
  have herr : M * accumulatedNoiseVariance P Q p n / (δ * Real.sqrt (n : ℝ)) ≤
      accumulatedNoiseVariance P Q p n / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_right hlarge hlam.le]
  have hlower : accumulatedNoiseVariance P Q p n / 2 ≤ (twoNoiseBlock P Q n k).secondMoment := by
    have h := (abs_le.1 (hclose.trans herr)).1
    linarith
  have ht : 0 < (twoNoiseBlock P Q n k).secondMoment := by linarith
  have hfour := twoNoiseBlock_fourth_bound P Q n k ε hε hP hQ
  rw [← twoNoiseBlock_variance] at hfour
  have hA := (twoNoiseBlock P Q n k).absoluteMoment_lower_exact ε ht hfour
  have hv := noise_variance_uniform_bound P Q p δ hδ hp hq n k hk
  have hroot : Real.sqrt (3 * (twoNoiseBlock P Q n k).secondMoment + ε ^ 2) ≤
      Real.sqrt (3 * accumulatedNoiseVariance P Q p n / δ + ε ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [mul_div_assoc]
    linarith only [hv]
  have hs : 0 < Real.sqrt (3 * (twoNoiseBlock P Q n k).secondMoment + ε ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg ε])
  have hd := div_le_div₀ ht.le hlower hs hroot
  have he : accumulatedNoiseVariance P Q p n / (2 * Real.sqrt (3 * accumulatedNoiseVariance P Q p n / δ + ε ^ 2)) =
      (accumulatedNoiseVariance P Q p n / 2) / Real.sqrt (3 * accumulatedNoiseVariance P Q p n / δ + ε ^ 2) := by ring
  rw [he]
  exact hd.trans hA

end BerryEsseen
