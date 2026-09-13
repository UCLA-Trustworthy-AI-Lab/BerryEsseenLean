import BerryEsseen.NoiseLocalMass
import BerryEsseen.ClusterNormalization

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def integerWindow (x r : ℝ) : Finset ℕ := Finset.Icc (Nat.ceil (x - r)) (Nat.floor (x + r))

theorem integerWindow_distance (x r : ℝ) (hx : 0 ≤ x - r) (hr : 0 ≤ r)
    (k : ℕ) (hk : k ∈ integerWindow x r) : |(k : ℝ) - x| ≤ r := by
  have h := Finset.mem_Icc.1 hk
  have hklo : (Nat.ceil (x - r) : ℝ) ≤ k := by exact_mod_cast h.1
  have hlo := (Nat.le_ceil (x - r)).trans hklo
  have hhi := (show (k : ℝ) ≤ Nat.floor (x + r) by exact_mod_cast h.2).trans
    (Nat.floor_le (by linarith : 0 ≤ x + r))
  rw [abs_le]
  constructor <;> linarith

theorem integerWindow_card_lower (x r : ℝ) (hx : 0 ≤ x - r) (hr : 1 ≤ r) :
    r ≤ (integerWindow x r).card := by
  have hlo := Nat.ceil_lt_add_one hx
  have hhi := Nat.lt_floor_add_one (x + r)
  have hab : Nat.ceil (x - r) ≤ Nat.floor (x + r) + 1 := by
    have h : (Nat.ceil (x - r) : ℝ) ≤ (Nat.floor (x + r) : ℝ) + 1 := by linarith
    exact_mod_cast h
  rw [integerWindow, Nat.card_Icc, Nat.cast_sub hab, Nat.cast_add, Nat.cast_one]
  linarith

theorem integerWindow_le_sample (x r : ℝ) (n : ℕ) (hx : x + r ≤ n)
    (k : ℕ) (hk : k ∈ integerWindow x r) : k ≤ n :=
  (Finset.mem_Icc.1 hk).2.trans (Nat.floor_le_of_le hx)

theorem CenteredFourthLaw.secondMoment_le_sq (P : CenteredFourthLaw) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) : P.secondMoment ≤ ε ^ 2 := by
  have h : (∫ x, x ^ 2 ∂P.measure) ≤ ∫ _ : ℝ, ε ^ 2 ∂P.measure := by
    apply integral_mono_ae (P.integrable_pow 2 (by omega)) (integrable_const _)
    filter_upwards [hP] with x hx
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using h

theorem accumulatedNoiseVariance_le_noise_bound (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc 0 1) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (n : ℕ) :
    accumulatedNoiseVariance P Q p n ≤ (n : ℝ) * ε ^ 2 := by
  have h0 := mul_le_mul_of_nonneg_left (P.secondMoment_le_sq ε hε hP) (sub_nonneg.2 hp.2)
  have h1 := mul_le_mul_of_nonneg_left (Q.secondMoment_le_sq ε hε hQ) hp.1
  have hsum : (1 - p) * P.secondMoment + p * Q.secondMoment ≤ ε ^ 2 := by nlinarith only [h0, h1]
  exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg n)

end BerryEsseen
