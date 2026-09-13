import BerryEsseen.CharacteristicDecay

/-! Direct low-frequency Edgeworth estimates, using powers instead of logarithms. -/
noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem complex_pow_difference_bound (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (k : ℕ) :
    ‖a ^ (k + 1) - b ^ (k + 1)‖ ≤ (k + 1 : ℝ) * r ^ k * ‖a - b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
        (a - b) * a ^ (k + 1) + b * (a ^ (k + 1) - b ^ (k + 1)) := by ring
    rw [he]
    calc
      _ ≤ ‖(a - b) * a ^ (k + 1)‖ + ‖b * (a ^ (k + 1) - b ^ (k + 1))‖ := norm_add_le _ _
      _ ≤ ‖a - b‖ * r ^ (k + 1) + r * ((k + 1 : ℝ) * r ^ k * ‖a - b‖) := by
        simp only [norm_mul, norm_pow]
        gcongr
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring

def cubicExponent (u κ : ℝ) : ℂ := -(u : ℂ) ^ 2 / 2 - (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6

theorem cubicExponent_re (u κ : ℝ) : (cubicExponent u κ).re = -u ^ 2 / 2 := by
  simp [cubicExponent, ← Complex.ofReal_pow]

theorem cubicExponent_norm (u κ : ℝ) (hκ : |κ| ≤ 2) (hu : |u| ≤ 1 / 100) :
    ‖cubicExponent u κ‖ ≤ u ^ 2 := by
  have h := norm_sub_le (-(u : ℂ) ^ 2 / 2) ((u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6)
  simp only [norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, Complex.norm_I, mul_one] at h
  norm_num at h
  have hu3 : |u| ^ 3 ≤ u ^ 2 / 100 := by
    have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
    nlinarith [sq_abs u]
  have hk := mul_le_mul_of_nonneg_left hκ (pow_nonneg (abs_nonneg u) 3)
  change ‖cubicExponent u κ‖ ≤ _
  change ‖cubicExponent u κ‖ ≤ _ at h
  nlinarith [sq_abs u, sq_nonneg u]

theorem charFun_cubic_exponential_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (u : ℝ) (hu : |u| ≤ 1 / 100) :
    ‖charFun P.measure u - Complex.exp (cubicExponent u (signedThirdMoment P))‖ ≤
      3 * |u| ^ 4 := by
  let w := cubicExponent u (signedThirdMoment P)
  have hw : ‖w‖ ≤ u ^ 2 := cubicExponent_norm u _ ((signedThirdMoment_abs_le P).trans hβ) hu
  have hu2 : u ^ 2 ≤ 1 / 10000 := by nlinarith [sq_abs u, abs_nonneg u]
  have he := Complex.norm_exp_sub_one_sub_id_le (show ‖w‖ ≤ 1 by linarith)
  have hw2 : ‖w‖ ^ 2 ≤ |u| ^ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg w) hw 2
    convert h using 1
    rw [← sq_abs u]
    ring
  have hf : ‖charFun P.measure u - 1 - w‖ ≤ 2 * |u| ^ 4 := by
    convert charFun_cubic_bound_two P hβ hb u using 1
    congr 1
    dsimp [w, cubicExponent]
    ring
  have ht := norm_sub_le (charFun P.measure u - 1 - w) (Complex.exp w - 1 - w)
  rw [show charFun P.measure u - 1 - w - (Complex.exp w - 1 - w) =
    charFun P.measure u - Complex.exp w by ring] at ht
  linarith

theorem unitExp_linear_remainder_bound (y : ℝ) :
    ‖Complex.exp ((y : ℂ) * Complex.I) - 1 - (y : ℂ) * Complex.I‖ ≤ y ^ 2 := by
  have hc : |Real.cos y - 1| ≤ |y| ^ 2 / 2 := by
    simpa [div_eq_mul_inv, mul_comm] using
      taylor_second_global Real.cos (fun x => -Real.sin x) (fun x => -Real.cos x) 1
        Real.hasDerivAt_cos (fun x => (Real.hasDerivAt_sin x).neg)
        (fun x => by simpa using Real.abs_cos_le_one x) 0 y
  have hs : |Real.sin y - y| ≤ |y| ^ 2 / 2 := by
    simpa [div_eq_mul_inv, mul_comm] using
      taylor_second_global Real.sin Real.cos (fun x => -Real.sin x) 1
        Real.hasDerivAt_sin Real.hasDerivAt_cos
        (fun x => by simpa using Real.abs_sin_le_one x) 0 y
  have h := Complex.norm_le_abs_re_add_abs_im
    (Complex.exp ((y : ℂ) * Complex.I) - 1 - (y : ℂ) * Complex.I)
  simp at h
  nlinarith [sq_abs y]

theorem charFun_power_cubic_exponential_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (u : ℝ) (hu : |u| ≤ 1 / 100) (k : ℕ) :
    ‖charFun P.measure u ^ (k + 1) -
      Complex.exp ((k + 1 : ℂ) * cubicExponent u (signedThirdMoment P))‖ ≤
      3 * (k + 1 : ℝ) * |u| ^ 4 * Real.exp (-(k : ℝ) * u ^ 2 / 4) := by
  have hnorm : ‖Complex.exp (cubicExponent u (signedThirdMoment P))‖ ≤
      Real.exp (-u ^ 2 / 4) := by
    rw [Complex.norm_exp, cubicExponent_re, Real.exp_le_exp]
    nlinarith [sq_nonneg u]
  have h := complex_pow_difference_bound (charFun P.measure u)
    (Complex.exp (cubicExponent u (signedThirdMoment P)))
    (Real.exp (-u ^ 2 / 4)) (Real.exp_pos _).le
    (charFun_low_frequency_decay P hβ hb u hu) hnorm k
  rw [← Complex.exp_nat_mul] at h
  have heq : Real.exp (-u ^ 2 / 4) ^ k = Real.exp (-(k : ℝ) * u ^ 2 / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at h
  have hh := mul_le_mul_of_nonneg_left (charFun_cubic_exponential_bound P hβ hb u hu)
    (show 0 ≤ (k + 1 : ℝ) * Real.exp (-(k : ℝ) * u ^ 2 / 4) by positivity)
  push_cast at h
  nlinarith

def edgeworthChar (n : ℕ) (κ t : ℝ) : ℂ :=
  (Real.exp (-t ^ 2 / 2) : ℂ) *
    (1 - (κ : ℂ) * (t : ℂ) ^ 3 * Complex.I / (6 * Real.sqrt (n : ℝ)))

theorem cubic_exponential_linear_error (n : ℕ) (u κ : ℝ) :
    ‖Complex.exp ((n : ℂ) * cubicExponent u κ) -
      (Real.exp (-(n : ℝ) * u ^ 2 / 2) : ℂ) *
        (1 - (n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6)‖ ≤
      Real.exp (-(n : ℝ) * u ^ 2 / 2) * ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 := by
  let a : ℝ := -(n : ℝ) * u ^ 2 / 2
  let y : ℝ := -(n : ℝ) * u ^ 3 * κ / 6
  have he : (n : ℂ) * cubicExponent u κ = (a : ℂ) + (y : ℂ) * Complex.I := by
    dsimp [cubicExponent, a, y]
    push_cast
    ring
  have hp : 1 - (n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6 =
      1 + (y : ℂ) * Complex.I := by
    dsimp [y]
    push_cast
    ring
  rw [he, hp, Complex.exp_add, ← Complex.ofReal_exp]
  change ‖(Real.exp a : ℂ) * Complex.exp ((y : ℂ) * Complex.I) -
    (Real.exp a : ℂ) * (1 + (y : ℂ) * Complex.I)‖ ≤ _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos a)]
  have h := unitExp_linear_remainder_bound y
  rw [sub_add_eq_sub_sub]
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos a).le
  convert hh using 1
  dsimp [a, y]
  ring

theorem charFun_power_edgeworth_raw (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (u : ℝ) (hu : |u| ≤ 1 / 100) (k : ℕ) :
    ‖charFun P.measure u ^ (k + 1) -
      (Real.exp (-(k + 1 : ℝ) * u ^ 2 / 2) : ℂ) *
        (1 - (k + 1 : ℂ) * (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6)‖ ≤
      3 * (k + 1 : ℝ) * |u| ^ 4 * Real.exp (-(k : ℝ) * u ^ 2 / 4) +
      Real.exp (-(k + 1 : ℝ) * u ^ 2 / 2) *
        ((k + 1 : ℝ) * u ^ 3 * signedThirdMoment P / 6) ^ 2 := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (charFun P.measure u ^ (k + 1))
    (Complex.exp ((k + 1 : ℂ) * cubicExponent u (signedThirdMoment P)))
      ((Real.exp (-(k + 1 : ℝ) * u ^ 2 / 2) : ℂ) *
        (1 - (k + 1 : ℂ) * (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6))
  have he := cubic_exponential_linear_error (k + 1) u (signedThirdMoment P)
  simp only [Nat.cast_add, Nat.cast_one] at he
  exact ht.trans (add_le_add
    (charFun_power_cubic_exponential_bound P hβ hb u hu k) he)

end BerryEsseen
