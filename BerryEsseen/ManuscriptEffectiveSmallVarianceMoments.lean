import BerryEsseen.EffectiveSmallVariance
import BerryEsseen.ManuscriptBinomialTheorem
import BerryEsseen.ManuscriptLeakageBudget

/-! Original finite block-moment budgets in the effective small-variance lemma. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def manuscriptEffectiveFourthBudget (lam ε : ℝ) : ℝ := 20 * lam * (lam + ε ^ 2)

theorem manuscript_effective_noise_variance_uniform (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (n k : ℕ) (hk : k ≤ n) :
    (twoNoiseBlock P Q n k).secondMoment ≤ (5 / 2) * accumulatedNoiseVariance P Q p n := by
  have h := noise_variance_uniform_bound P Q p (2 / 5) (by norm_num) hp.1
    (by linarith [hp.2]) n k hk
  convert h using 1 <;> ring

theorem manuscript_effective_noise_fourth (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hk : k ≤ n) :
    (twoNoiseBlock P Q n k).fourthMoment ≤
      manuscriptEffectiveFourthBudget (accumulatedNoiseVariance P Q p n) ε := by
  have h := noise_fourth_uniform_bound P Q p (2 / 5) ε (by norm_num) hp.1
    (by linarith [hp.2]) hε hP hQ n k hk
  have hl : 0 ≤ accumulatedNoiseVariance P Q p n :=
    accumulatedNoiseVariance_nonneg P Q p ⟨by linarith [hp.1], by linarith [hp.2]⟩ n
  unfold manuscriptEffectiveFourthBudget
  nlinarith [mul_nonneg hl (sq_nonneg ε), sq_nonneg (accumulatedNoiseVariance P Q p n)]

theorem manuscript_effective_fourth_budget_small (lam ε : ℝ)
    (hlam : lam ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12)) :
    manuscriptEffectiveFourthBudget lam ε < 3 / (10 : ℝ) ^ 23 := by
  have hε2 := pow_le_pow_left₀ hε.1 hε.2 2
  have h := mul_le_mul hlam.2
    (show lam + ε ^ 2 ≤ 1 / (10 : ℝ) ^ 12 + 1 / (10 : ℝ) ^ 24 by norm_num at hε2 ⊢; linarith [hlam.2])
    (by linarith [hlam.1, sq_nonneg ε] : 0 ≤ lam + ε ^ 2) (by positivity : (0 : ℝ) ≤ 1 / 10 ^ 12)
  unfold manuscriptEffectiveFourthBudget
  norm_num at h ⊢
  linarith

theorem manuscript_effective_noise_fourth_small (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hk : k ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ≤ 1 / (10 : ℝ) ^ 12) :
    (twoNoiseBlock P Q n k).fourthMoment ≤ 1 / 160000 := by
  have hf := manuscript_effective_noise_fourth P Q p ε hp hε.1 hP hQ n k hk
  have hb := manuscript_effective_fourth_budget_small (accumulatedNoiseVariance P Q p n) ε
    ⟨accumulatedNoiseVariance_nonneg P Q p ⟨by linarith [hp.1], by linarith [hp.2]⟩ n, hlam⟩ hε
  linarith

theorem manuscript_effective_noise_variance_central_error (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (n k : ℕ)
    (hn : 1 ≤ n) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    |(twoNoiseBlock P Q n k).secondMoment - accumulatedNoiseVariance P Q p n| ≤
      25 * accumulatedNoiseVariance P Q p n / (4 * Real.sqrt (n : ℝ)) := by
  have h := noise_variance_central_bound P Q p (2 / 5) (5 / 2) (by norm_num) hp.1
    (by linarith [hp.2]) (by norm_num) n k hn hk (effective_binomial_raw_distance p hp n k hn hz)
  convert h using 1 <;> ring

theorem manuscript_effective_noise_variance_central (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (n k : ℕ)
    (hn : 10 ^ 100 ≤ n) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    (twoNoiseBlock P Q n k).secondMoment ∈
      Icc (accumulatedNoiseVariance P Q p n / 2) ((3 / 2) * accumulatedNoiseVariance P Q p n) := by
  have he := manuscript_effective_noise_variance_central_error P Q p hp n k (by omega) hk hz
  have hr := effective_binomial_root_lower n hn
  have hr0 : 0 < Real.sqrt (n : ℝ) := by linarith [show (0 : ℝ) < 10 ^ 50 by positivity]
  have hl := accumulatedNoiseVariance_nonneg P Q p ⟨by linarith [hp.1], by linarith [hp.2]⟩ n
  have hcoeff : (25 : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by norm_num at hr; linarith
  have hsmall : 25 * accumulatedNoiseVariance P Q p n / (4 * Real.sqrt (n : ℝ)) ≤
      accumulatedNoiseVariance P Q p n / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hr0)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff hl]
  have hh := abs_le.mp (he.trans hsmall)
  constructor <;> linarith [hh.1, hh.2]

theorem manuscript_effective_noise_absolute_central (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5)
    (hlam : 0 < accumulatedNoiseVariance P Q p n) :
    accumulatedNoiseVariance P Q p n /
      (2 * Real.sqrt (5 * accumulatedNoiseVariance P Q p n + ε ^ 2)) ≤
      (twoNoiseBlock P Q n k).absoluteMoment := by
  have ht := manuscript_effective_noise_variance_central P Q p hp n k hn hk hz
  have ht0 : 0 < (twoNoiseBlock P Q n k).secondMoment := by linarith [ht.1]
  have hfour := twoNoiseBlock_fourth_bound P Q n k ε hε hP hQ
  rw [← twoNoiseBlock_variance] at hfour
  have hA := (twoNoiseBlock P Q n k).absoluteMoment_lower_exact ε ht0 hfour
  have hs : 0 < Real.sqrt (3 * (twoNoiseBlock P Q n k).secondMoment + ε ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hroot : Real.sqrt (3 * (twoNoiseBlock P Q n k).secondMoment + ε ^ 2) ≤
      Real.sqrt (5 * accumulatedNoiseVariance P Q p n + ε ^ 2) := by
    apply Real.sqrt_le_sqrt
    linarith [ht.2]
  have h := div_le_div₀ ht0.le ht.1 hs hroot
  convert h.trans hA using 1 <;> ring

theorem manuscript_effective_leakage_bound (P Q : CenteredFourthLaw)
    (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    blockLeakageBudget P Q p n k ≤
      80 * manuscriptEffectiveFourthBudget (accumulatedNoiseVariance P Q p n) ε /
        Real.sqrt (n : ℝ) := by
  have hpcc : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hlam := accumulatedNoiseVariance_nonneg P Q p hpcc n
  have h := manuscript_uniform_block_leakage_bound P Q p hpcc n k
    (2 / Real.sqrt (n : ℝ)) (manuscriptEffectiveFourthBudget (accumulatedNoiseVariance P Q p n) ε)
    (by positivity) (by unfold manuscriptEffectiveFourthBudget; positivity)
    (fun j _hj => manuscript_effective_binomial_mass_upper p hp n j hn)
    (fun j hj => manuscript_effective_noise_fourth P Q p ε hp hε hP hQ n j hj)
  convert h using 1 <;> ring

end BerryEsseen
