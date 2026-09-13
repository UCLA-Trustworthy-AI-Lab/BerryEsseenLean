import BerryEsseen.NormalizedFourier
import BerryEsseen.JitterLowFrequency
import BerryEsseen.ManuscriptGeneralLog

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The manuscript's principal-log expansion, followed by the purely imaginary
second-order exponential remainder. -/
theorem charFun_power_edgeworth_with_remainder (P : StandardizedLaw) (u ρ : ℝ)
    (hρ : 0 ≤ ρ) (hne : charFun P.measure u ≠ 0)
    (hlog : ‖manuscriptLogRemainder P u‖ ≤ |u| ^ 3 * ρ + |u| ^ 4)
    (hsmall : |u| * (ρ + |u|) ≤ 1 / 8) (k : ℕ) :
    ‖charFun P.measure u ^ (k + 1) -
      (Real.exp (-(k + 1 : ℝ) * u ^ 2 / 2) : ℂ) *
        (1 - (k + 1 : ℂ) * (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6)‖ ≤
      (k + 1 : ℝ) * (|u| ^ 3 * ρ + |u| ^ 4) * Real.exp (-(k : ℝ) * u ^ 2 / 4) +
      Real.exp (-(k + 1 : ℝ) * u ^ 2 / 2) *
        ((k + 1 : ℝ) * u ^ 3 * signedThirdMoment P / 6) ^ 2 := by
  have hp := manuscript_charFun_power_from_principal_log P u ρ (k + 1) hne hlog hsmall
  push_cast at hp
  have hex : Real.exp (-(3 / 8 : ℝ) * (k + 1) * u ^ 2) ≤
      Real.exp (-(k : ℝ) * u ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg u)]
  have hp' := hp.trans (mul_le_mul_of_nonneg_left hex
    (by positivity : 0 ≤ (k + 1 : ℝ) * (|u| ^ 3 * ρ + |u| ^ 4)))
  have hl := cubic_exponential_linear_error_sharp (k + 1) u (signedThirdMoment P)
  simp only [Nat.cast_add, Nat.cast_one] at hl
  have hnon : 0 ≤ Real.exp (-(k + 1 : ℝ) * u ^ 2 / 2) *
      ((k + 1 : ℝ) * u ^ 3 * signedThirdMoment P / 6) ^ 2 := by positivity
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hp' (hl.trans (by linarith only [hnon])))

theorem general_charFun_edgeworth_normalized (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (B t ρ : ℝ) (hB : 0 ≤ B) (hκ : |signedThirdMoment P| ≤ B) (hρ : 0 ≤ ρ)
    (hne : charFun P.measure (t / Real.sqrt (n : ℝ)) ≠ 0)
    (hlog : ‖manuscriptLogRemainder P (t / Real.sqrt (n : ℝ))‖ ≤
      |t / Real.sqrt (n : ℝ)| ^ 3 * ρ + |t / Real.sqrt (n : ℝ)| ^ 4)
    (hsmall : |t / Real.sqrt (n : ℝ)| * (ρ + |t / Real.sqrt (n : ℝ)|) ≤ 1 / 8) :
    ‖charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n - edgeworthChar n (signedThirdMoment P) t‖ ≤
      (|t| ^ 3 * ρ / Real.sqrt (n : ℝ) + |t| ^ 4 / (n : ℝ)) * Real.exp (-t ^ 2 / 8) +
      B ^ 2 * |t| ^ 6 / (36 * (n : ℝ)) * Real.exp (-t ^ 2 / 2) := by
  let s := Real.sqrt (n : ℝ)
  let u := t / s
  let κ := signedThirdMoment P
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < s := Real.sqrt_pos.mpr hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hn1 : n - 1 + 1 = n := by omega
  have hn1r : (n - 1 : ℕ) + (1 : ℝ) = n := by exact_mod_cast hn1
  have hn1c : (n - 1 : ℕ) + (1 : ℂ) = n := by exact_mod_cast hn1
  obtain ⟨hu2, hu3, hu4⟩ := normalized_cubic_scaling (n : ℝ) s t κ hs hs2
  change (n : ℝ) * u ^ 2 = t ^ 2 at hu2
  change (n : ℝ) * u ^ 3 * κ / 6 = κ * t ^ 3 / (6 * s) at hu3
  change (n : ℝ) * |u| ^ 4 = |t| ^ 4 / (n : ℝ) at hu4
  have hscale : (n : ℝ) * |u| ^ 3 = |t| ^ 3 / s := by
    dsimp only [u]
    rw [abs_div, abs_of_pos hs, ← hs2]
    field_simp
  have heq : (Real.exp (-(n : ℝ) * u ^ 2 / 2) : ℂ) *
      (1 - (n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6) = edgeworthChar n κ t := by
    have he : -(n : ℝ) * u ^ 2 / 2 = -t ^ 2 / 2 := by nlinarith only [hu2]
    rw [he, edgeworthChar]
    congr 2
    have h := congrArg Complex.ofReal hu3
    push_cast at h
    change _ = _ / (6 * (s : ℂ))
    calc
      _ = ((n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) / 6) * Complex.I := by ring
      _ = ((κ : ℂ) * (t : ℂ) ^ 3 / (6 * (s : ℂ))) * Complex.I := by rw [h]
      _ = _ := by ring
  have hp := charFun_power_edgeworth_with_remainder P u ρ hρ hne hlog hsmall (n - 1)
  rw [hn1, hn1r, hn1c, heq] at hp
  have hex : Real.exp (-(n - 1 : ℕ) * u ^ 2 / 4) ≤ Real.exp (-t ^ 2 / 8) := by
    rw [Real.exp_le_exp]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hm := mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (sq_nonneg u)
    nlinarith only [hm, hu2, hn1r]
  have he2 : Real.exp (-(n : ℝ) * u ^ 2 / 2) = Real.exp (-t ^ 2 / 2) := by
    congr 1
    nlinarith only [hu2]
  have hk2 : κ ^ 2 ≤ B ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg κ) hκ 2
    simpa only [sq_abs] using h
  have hterm : ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 ≤ B ^ 2 * |t| ^ 6 / (36 * (n : ℝ)) := by
    rw [hu3]
    have he : (κ * t ^ 3 / (6 * s)) ^ 2 = κ ^ 2 * |t| ^ 6 / (36 * (n : ℝ)) := by
      rw [← hs2, div_pow, mul_pow, mul_pow]
      have ha : |t| ^ 6 = t ^ 6 := by calc
        |t| ^ 6 = (|t| ^ 2) ^ 3 := by ring
        _ = (t ^ 2) ^ 3 := by rw [sq_abs]
        _ = t ^ 6 := by ring
      rw [ha]
      ring
    rw [he]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hk2 (pow_nonneg (abs_nonneg t) 6)) (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hex
    (show 0 ≤ (n : ℝ) * (|u| ^ 3 * ρ + |u| ^ 4) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hterm (Real.exp_pos (-t ^ 2 / 2)).le
  have hid : (n : ℝ) * (|u| ^ 3 * ρ + |u| ^ 4) = |t| ^ 3 * ρ / s + |t| ^ 4 / (n : ℝ) := by
    calc
      _ = ((n : ℝ) * |u| ^ 3) * ρ + (n : ℝ) * |u| ^ 4 := by ring
      _ = _ := by rw [hscale, hu4]; ring
  rw [he2] at hp
  rw [hid] at h1 hp
  change ‖charFun P.measure u ^ n - edgeworthChar n κ t‖ ≤ _
  dsimp only [s, κ] at hp h1 h2 ⊢
  nlinarith only [hp, h1, h2]

def generalLowFrequencyBound (B h ρ r t : ℝ) : ℝ :=
  (|t| ^ 2 * ρ + |t| ^ 3 / r) * Real.exp (-t ^ 2 / 8) +
    B ^ 2 * |t| ^ 5 / (36 * r) * Real.exp (-t ^ 2 / 2) +
      h ^ 2 * |t| / (24 * r) * Real.exp (-t ^ 2 / 4)

theorem general_jitter_fourier_scaled_bound (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (B h t ρ : ℝ) (hB : 0 ≤ B) (hh : 0 ≤ h) (hκ : |signedThirdMoment P| ≤ B) (hρ : 0 ≤ ρ)
    (hne : charFun P.measure (t / Real.sqrt (n : ℝ)) ≠ 0)
    (hlog : ‖manuscriptLogRemainder P (t / Real.sqrt (n : ℝ))‖ ≤
      |t / Real.sqrt (n : ℝ)| ^ 3 * ρ + |t / Real.sqrt (n : ℝ)| ^ 4)
    (hsmall : |t / Real.sqrt (n : ℝ)| * (ρ + |t / Real.sqrt (n : ℝ)|) ≤ 1 / 8) :
    Real.sqrt (n : ℝ) * jitterFourierError P n h t ≤
      generalLowFrequencyBound B h ρ (Real.sqrt (n : ℝ)) t := by
  by_cases ht0 : t = 0
  · subst t
    simp [jitterFourierError, generalLowFrequencyBound]
  let r := Real.sqrt (n : ℝ)
  let u := t / r
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hu2 : (n : ℝ) * u ^ 2 = t ^ 2 := (normalized_cubic_scaling (n : ℝ) r t 0 hr hr2).1
  have hf : ‖charFun P.measure u ^ n‖ ≤ Real.exp (-t ^ 2 / 4) := by
    have hd := manuscript_charFun_power_decay_from_log P u ρ n hne hlog hsmall
    apply hd.trans
    apply Real.exp_le_exp.mpr
    nlinarith only [hu2, sq_nonneg t]
  have hsin : |Real.sinc (h * u / 2) - 1| ≤ h ^ 2 * u ^ 2 / 24 := by
    convert sinc_quadratic_error (h * u / 2) using 1
    ring
  have hprod : ‖((Real.sinc (h * u / 2) : ℂ) - 1) * charFun P.measure u ^ n‖ ≤
      h ^ 2 * u ^ 2 / 24 * Real.exp (-t ^ 2 / 4) := by
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hsin hf (norm_nonneg _) (by positivity)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    ((Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n)
    (charFun P.measure u ^ n) (edgeworthChar n (signedThirdMoment P) t)
  rw [show (Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n - charFun P.measure u ^ n =
    ((Real.sinc (h * u / 2) : ℂ) - 1) * charFun P.measure u ^ n by ring] at htri
  have hbase := general_charFun_edgeworth_normalized P n hn B t ρ hB hκ hρ hne hlog hsmall
  have hraw := htri.trans (add_le_add hprod hbase)
  have hdiv := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hraw (abs_nonneg t)) hr.le
  have hJ : jitterFourierError P n h t =
      ‖(Real.sinc (h * u / 2) : ℂ) * charFun P.measure u ^ n - edgeworthChar n (signedThirdMoment P) t‖ / |t| := by
    rw [jitterFourierError, charFun_normalizedJitteredSumLaw P n h hh]
  rw [← hJ] at hdiv
  convert hdiv using 1
  unfold generalLowFrequencyBound
  change _ = r * (_ / |t|)
  dsimp only [u]
  simp only [← hr2, Real.sqrt_sq hr.le]
  field_simp [abs_ne_zero.mpr ht0, hr.ne']
  simp only [← sq_abs t]
  ring

end BerryEsseen
