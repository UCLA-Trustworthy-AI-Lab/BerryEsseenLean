import BerryEsseen.LowFrequencyExpansion

/-! Pointwise low-frequency estimates in the standardized Fourier variable. -/
noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem normalized_cubic_scaling (N s t κ : ℝ) (hs : 0 < s) (hs2 : s ^ 2 = N) :
    N * (t / s) ^ 2 = t ^ 2 ∧
    N * (t / s) ^ 3 * κ / 6 = κ * t ^ 3 / (6 * s) ∧
    N * |t / s| ^ 4 = |t| ^ 4 / N := by
  subst N
  have hsn := hs.ne'
  constructor
  · field_simp
  constructor
  · field_simp
  · rw [abs_div, abs_of_pos hs]
    field_simp

theorem charFun_edgeworth_low_frequency (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : |t| ≤ Real.sqrt (n : ℝ) / 100) :
    ‖charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n - edgeworthChar n (signedThirdMoment P) t‖ ≤
      (3 * |t| ^ 4 * Real.exp (-t ^ 2 / 8) +
        |t| ^ 6 / 9 * Real.exp (-t ^ 2 / 2)) / (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  let u := t / s
  let κ := signedThirdMoment P
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hu : |u| ≤ 1 / 100 := by
    dsimp [u]
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).2
    linarith
  have hn1 : n - 1 + 1 = n := by omega
  have hn1r : (n - 1 : ℕ) + (1 : ℝ) = n := by exact_mod_cast hn1
  have hn1c : (n - 1 : ℕ) + (1 : ℂ) = n := by exact_mod_cast hn1
  obtain ⟨hu2, hu3, hu4⟩ := normalized_cubic_scaling (n : ℝ) s t κ hs hs2
  change (n : ℝ) * u ^ 2 = t ^ 2 at hu2
  change (n : ℝ) * u ^ 3 * κ / 6 = κ * t ^ 3 / (6 * s) at hu3
  change (n : ℝ) * |u| ^ 4 = |t| ^ 4 / (n : ℝ) at hu4
  have heq : (Real.exp (-(n : ℝ) * u ^ 2 / 2) : ℂ) *
        (1 - (n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6) = edgeworthChar n κ t := by
    have hex : -(n : ℝ) * u ^ 2 / 2 = -t ^ 2 / 2 := by nlinarith [hu2]
    rw [hex, edgeworthChar]
    congr 2
    have h := congrArg Complex.ofReal hu3
    push_cast at h
    change _ = _ / (6 * (s : ℂ))
    calc
      _ = ((n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) / 6) * Complex.I := by ring
      _ = ((κ : ℂ) * (t : ℂ) ^ 3 / (6 * (s : ℂ))) * Complex.I := by rw [h]
      _ = _ := by ring
  have hr := charFun_power_edgeworth_raw P hβ hb u hu (n - 1)
  rw [hn1, hn1r, hn1c, heq] at hr
  have hex : Real.exp (-(n - 1 : ℕ) * u ^ 2 / 4) ≤ Real.exp (-t ^ 2 / 8) := by
    rw [Real.exp_le_exp]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hprod := mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (sq_nonneg u)
    nlinarith [hu2]
  have he2 : Real.exp (-(n : ℝ) * u ^ 2 / 2) = Real.exp (-t ^ 2 / 2) := by
    congr 1
    nlinarith [hu2]
  have hκ : |κ| ≤ 2 := (signedThirdMoment_abs_le P).trans hβ
  have hk2 : κ ^ 2 ≤ 4 := by nlinarith [sq_abs κ, abs_nonneg κ]
  have hterm : ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 ≤ |t| ^ 6 / (9 * (n : ℝ)) := by
    rw [hu3]
    have hsq : (κ * t ^ 3 / (6 * s)) ^ 2 = κ ^ 2 * |t| ^ 6 / (36 * (n : ℝ)) := by
      rw [← hs2, div_pow, mul_pow, mul_pow]
      have hab : |t| ^ 6 = t ^ 6 := by
        calc |t| ^ 6 = (|t| ^ 2) ^ 3 := by ring
             _ = (t ^ 2) ^ 3 := by rw [sq_abs]
             _ = t ^ 6 := by ring
      rw [hab]
      ring
    rw [hsq]
    apply (div_le_iff₀ (by positivity : 0 < 36 * (n : ℝ))).2
    have h := mul_le_mul_of_nonneg_right hk2 (pow_nonneg (abs_nonneg t) 6)
    convert h using 1
    field_simp
    ring
  calc
    _ ≤ 3 * (n : ℝ) * |u| ^ 4 * Real.exp (-(n - 1 : ℕ) * u ^ 2 / 4) +
        Real.exp (-(n : ℝ) * u ^ 2 / 2) * ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 := hr
    _ ≤ 3 * (n : ℝ) * |u| ^ 4 * Real.exp (-t ^ 2 / 8) +
        Real.exp (-t ^ 2 / 2) * (|t| ^ 6 / (9 * (n : ℝ))) := by
      rw [he2]
      exact add_le_add (mul_le_mul_of_nonneg_left hex (by positivity))
        (mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le)
    _ = _ := by
      rw [show 3 * (n : ℝ) * |u| ^ 4 = 3 * ((n : ℝ) * |u| ^ 4) by ring, hu4]
      ring

end BerryEsseen
