import BerryEsseen.GeneralCharacteristicTaylor
import BerryEsseen.GeneralCharacteristicDecay
import BerryEsseen.EffectiveLowFrequency

/-! Principal logarithms and their actual cubic remainder in manuscript Lemma 2.2.
The fourth-order term below is the elementary logarithm error; no fourth
moment of the distribution is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def manuscriptLogRemainder (P : StandardizedLaw) (u : ℝ) : ℂ :=
  Complex.log (charFun P.measure u) - cubicExponent u (signedThirdMoment P)

def manuscriptLogModulus (P : StandardizedLaw) (u : ℝ) : ℝ :=
  characteristicCubicModulus P u + |u|

theorem manuscript_charFun_ne_zero (P : StandardizedLaw) (u : ℝ)
    (hu : |u| ≤ 1 / 2) : charFun P.measure u ≠ 0 := by
  intro he
  have h := charFun_sub_one_quadratic_bound P u
  rw [he] at h
  norm_num at h
  nlinarith [sq_abs u, abs_nonneg u]

theorem manuscript_principal_log_remainder (P : StandardizedLaw) (u : ℝ)
    (hu : |u| ≤ 1 / 2) :
    ‖manuscriptLogRemainder P u‖ ≤ |u| ^ 3 * manuscriptLogModulus P u := by
  let w := charFun P.measure u - 1
  have hw : ‖w‖ ≤ u ^ 2 / 2 := charFun_sub_one_quadratic_bound P u
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hw8 : ‖w‖ ≤ 1 / 8 := by linarith
  have hlog := Complex.norm_log_one_add_sub_self_le (by linarith : ‖w‖ < 1)
  have hlog' : ‖Complex.log (1 + w) - w‖ ≤ |u| ^ 4 := by
    have hw2 : ‖w‖ ^ 2 ≤ |u| ^ 4 / 4 := by
      have h := pow_le_pow_left₀ (norm_nonneg w) hw 2
      nlinarith [show |u| ^ 4 = (u ^ 2) ^ 2 by rw [← sq_abs u]; ring]
    have hdiv := div_le_div₀ (by positivity : 0 ≤ |u| ^ 4) (by nlinarith [pow_nonneg (abs_nonneg u) 4] : ‖w‖ ^ 2 ≤ |u| ^ 4)
      (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ 2 * (1 - ‖w‖))
    apply hlog.trans
    have hne : 1 - ‖w‖ ≠ 0 := by linarith
    convert hdiv using 1 <;> field_simp [hne]
  have he : 1 + w = charFun P.measure u := by dsimp [w]; ring
  rw [he] at hlog'
  have hc := charFun_cubic_modulus_bound P u
  have hid : charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6 =
      w - cubicExponent u (signedThirdMoment P) := by dsimp [w, cubicExponent]; ring
  rw [hid] at hc
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (Complex.log (charFun P.measure u)) w (cubicExponent u (signedThirdMoment P))
  change ‖Complex.log (charFun P.measure u) - cubicExponent u (signedThirdMoment P)‖ ≤ _
  unfold manuscriptLogModulus characteristicCubicModulus
  nlinarith only [ht, hlog', hc]

theorem manuscript_principal_log_smallness (P : StandardizedLaw) (B u : ℝ)
    (hB : 1 ≤ B) (hβ : thirdMoment P ≤ B) (hu : |u| ≤ 1 / (100 * B)) :
    |u| * manuscriptLogModulus P u ≤ 1 / 8 := by
  have hp := general_low_frequency_parameters B u hB hu
  have hρ := (characteristicCubicModulus_le_thirdMoment P u).trans hβ
  have hm := mul_le_mul_of_nonneg_left hρ (abs_nonneg u)
  unfold manuscriptLogModulus
  nlinarith [sq_abs u]

theorem manuscriptLogModulus_diagonal_tendsto
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun j => manuscriptLogModulus (P j) (u j)) atTop (𝓝 0) := by
  simpa [manuscriptLogModulus] using
    (weak_thirdMoment_characteristicCubicModulus_diagonal_tendsto P Q hw hm u hu).add hu.abs

theorem manuscript_complex_exp_sub_one (r : ℂ) :
    ‖Complex.exp r - 1‖ ≤ ‖r‖ * Real.exp ‖r‖ := by
  simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp r 1

/-- This is the manuscript's r = n(log f - cubic) and |r| ≤ n u²/8. -/
theorem manuscript_scaled_log_remainder (P : StandardizedLaw) (u ρ : ℝ) (n : ℕ)
    (hlog : ‖manuscriptLogRemainder P u‖ ≤ |u| ^ 3 * ρ + |u| ^ 4)
    (hsmall : |u| * (ρ + |u|) ≤ 1 / 8) :
    ‖(n : ℂ) * manuscriptLogRemainder P u‖ ≤ (n : ℝ) * u ^ 2 / 8 := by
  rw [norm_mul, Complex.norm_natCast]
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg u)
  have he : |u| ^ 3 * ρ + |u| ^ 4 = u ^ 2 * (|u| * (ρ + |u|)) := by
    rw [← sq_abs u]
    ring
  rw [he] at hlog
  have hb : ‖manuscriptLogRemainder P u‖ ≤ u ^ 2 / 8 := by nlinarith only [hlog, hs]
  convert mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) n) using 1 <;> ring

/-- Expand exp(n log f) using exp(r)-1, not a difference of two powers. -/
theorem manuscript_charFun_power_from_principal_log (P : StandardizedLaw)
    (u ρ : ℝ) (n : ℕ) (hne : charFun P.measure u ≠ 0)
    (hlog : ‖manuscriptLogRemainder P u‖ ≤ |u| ^ 3 * ρ + |u| ^ 4)
    (hsmall : |u| * (ρ + |u|) ≤ 1 / 8) :
    ‖charFun P.measure u ^ n - Complex.exp ((n : ℂ) * cubicExponent u (signedThirdMoment P))‖ ≤
      (n : ℝ) * (|u| ^ 3 * ρ + |u| ^ 4) * Real.exp (-(3 / 8 : ℝ) * n * u ^ 2) := by
  let r := (n : ℂ) * manuscriptLogRemainder P u
  have hr : ‖r‖ ≤ (n : ℝ) * u ^ 2 / 8 :=
    manuscript_scaled_log_remainder P u ρ n hlog hsmall
  have hr' : ‖r‖ ≤ (n : ℝ) * (|u| ^ 3 * ρ + |u| ^ 4) := by
    dsimp [r]
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n)
  have hid : charFun P.measure u ^ n =
      Complex.exp ((n : ℂ) * cubicExponent u (signedThirdMoment P)) * Complex.exp r := by
    rw [← Complex.exp_add]
    have he : (n : ℂ) * cubicExponent u (signedThirdMoment P) + r =
        (n : ℂ) * Complex.log (charFun P.measure u) := by
      dsimp [r, manuscriptLogRemainder]
      ring
    rw [he, Complex.exp_nat_mul, Complex.exp_log hne]
  rw [hid, ← mul_sub_one, norm_mul, Complex.norm_exp]
  have hre : ((n : ℂ) * cubicExponent u (signedThirdMoment P)).re =
      -(n : ℝ) * u ^ 2 / 2 := by simp [cubicExponent_re]; ring
  rw [hre]
  have h := mul_le_mul_of_nonneg_left (manuscript_complex_exp_sub_one r)
    (Real.exp_pos (-(n : ℝ) * u ^ 2 / 2)).le
  have he : Real.exp (-(n : ℝ) * u ^ 2 / 2) * (‖r‖ * Real.exp ‖r‖) =
      ‖r‖ * Real.exp (-(n : ℝ) * u ^ 2 / 2 + ‖r‖) := by rw [Real.exp_add]; ring
  rw [he] at h
  apply h.trans
  apply mul_le_mul hr' (Real.exp_le_exp.mpr (by linarith only [hr]))
    (Real.exp_pos _).le (hr'.trans' (norm_nonneg r))

/-- The Gaussian modulus bound follows from the same principal-log remainder. -/
theorem manuscript_charFun_power_decay_from_log (P : StandardizedLaw)
    (u ρ : ℝ) (n : ℕ) (hne : charFun P.measure u ≠ 0)
    (hlog : ‖manuscriptLogRemainder P u‖ ≤ |u| ^ 3 * ρ + |u| ^ 4)
    (hsmall : |u| * (ρ + |u|) ≤ 1 / 8) :
    ‖charFun P.measure u ^ n‖ ≤ Real.exp (-(3 / 8 : ℝ) * n * u ^ 2) := by
  let r := (n : ℂ) * manuscriptLogRemainder P u
  have hr : ‖r‖ ≤ (n : ℝ) * u ^ 2 / 8 :=
    manuscript_scaled_log_remainder P u ρ n hlog hsmall
  have hid : charFun P.measure u ^ n =
      Complex.exp ((n : ℂ) * cubicExponent u (signedThirdMoment P) + r) := by
    have he : (n : ℂ) * cubicExponent u (signedThirdMoment P) + r =
        (n : ℂ) * Complex.log (charFun P.measure u) := by
      dsimp [r, manuscriptLogRemainder]
      ring
    rw [he, Complex.exp_nat_mul, Complex.exp_log hne]
  rw [hid, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((n : ℂ) * cubicExponent u (signedThirdMoment P)).re =
      -(n : ℝ) * u ^ 2 / 2 := by simp [cubicExponent_re]; ring
  rw [Complex.add_re, hre]
  have hrre := Complex.re_le_norm r
  linarith

end BerryEsseen
