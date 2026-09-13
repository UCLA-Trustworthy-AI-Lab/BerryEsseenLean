import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Taylor estimates proved by derivative comparison on [0,1]. The affine
path parameter permits either sign of the displacement and retains the
sharp factorial constants. No asymptotic remainder is assumed. -/
open Set
namespace BerryEsseen

theorem derivative_comparison (f f' g g' : ℝ → ℝ)
    (hf : ∀ x ∈ Icc 0 1, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ Icc 0 1, HasDerivAt g (g' x) x)
    (hle : ∀ x ∈ Icc 0 1, f' x ≤ g' x) (h0 : f 0 ≤ g 0) :
    ∀ x ∈ Icc 0 1, f x ≤ g x := by
  have ha : AntitoneOn (fun x => f x - g x) (Icc 0 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun x hx => ((hf x hx).sub (hg x hx)).continuousAt.continuousWithinAt)
      (fun x hx => ((hf x (interior_subset hx)).sub
        (hg x (interior_subset hx))).hasDerivWithinAt)
      (fun x hx => sub_nonpos.2 (hle x (interior_subset hx)))
  intro x hx
  have hh := ha (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hx hx.1
  linarith

theorem taylor_first_upper (f f' : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x ∈ Icc 0 1, HasDerivAt f (f' x) x)
    (hC : ∀ x ∈ Icc 0 1, f' x ≤ C) :
    ∀ x ∈ Icc 0 1, f x ≤ f 0 + C * x := by
  apply derivative_comparison f f' (fun x => f 0 + C * x) (fun _ => C) hf
  · intro x _
    simpa using ((hasDerivAt_id x).const_mul C).const_add (f 0)
  · exact hC
  · simp

theorem taylor_second_upper (f f₁ f₂ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x ∈ Icc 0 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 1, HasDerivAt f₁ (f₂ x) x)
    (hC : ∀ x ∈ Icc 0 1, f₂ x ≤ C) :
    ∀ x ∈ Icc 0 1, f x ≤ f 0 + f₁ 0 * x + C / 2 * x ^ 2 := by
  apply derivative_comparison f f₁ (fun x => f 0 + f₁ 0 * x + C / 2 * x ^ 2)
    (fun x => f₁ 0 + C * x) h₁
  · intro x _
    convert (((hasDerivAt_id x).const_mul (f₁ 0)).const_add (f 0)).add
      (((hasDerivAt_id x).pow 2).const_mul (C / 2)) using 1 <;> (dsimp; ring)
  · exact taylor_first_upper f₁ f₂ C h₂ hC
  · simp

theorem taylor_third_upper (f f₁ f₂ f₃ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x ∈ Icc 0 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 1, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x ∈ Icc 0 1, HasDerivAt f₂ (f₃ x) x)
    (hC : ∀ x ∈ Icc 0 1, f₃ x ≤ C) :
    ∀ x ∈ Icc 0 1, f x ≤ f 0 + f₁ 0 * x + f₂ 0 / 2 * x ^ 2 + C / 6 * x ^ 3 := by
  apply derivative_comparison f f₁
    (fun x => f 0 + f₁ 0 * x + f₂ 0 / 2 * x ^ 2 + C / 6 * x ^ 3)
    (fun x => f₁ 0 + f₂ 0 * x + C / 2 * x ^ 2) h₁
  · intro x _
    convert ((((hasDerivAt_id x).const_mul (f₁ 0)).const_add (f 0)).add
      (((hasDerivAt_id x).pow 2).const_mul (f₂ 0 / 2))).add
      (((hasDerivAt_id x).pow 3).const_mul (C / 6)) using 1 <;> (dsimp; ring)
  · exact taylor_second_upper f₁ f₂ f₃ C h₂ h₃ hC
  · simp

theorem taylor_fourth_upper (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x ∈ Icc 0 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 1, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x ∈ Icc 0 1, HasDerivAt f₂ (f₃ x) x)
    (h₄ : ∀ x ∈ Icc 0 1, HasDerivAt f₃ (f₄ x) x)
    (hC : ∀ x ∈ Icc 0 1, f₄ x ≤ C) :
    ∀ x ∈ Icc 0 1, f x ≤ f 0 + f₁ 0 * x + f₂ 0 / 2 * x ^ 2 +
      f₃ 0 / 6 * x ^ 3 + C / 24 * x ^ 4 := by
  apply derivative_comparison f f₁
    (fun x => f 0 + f₁ 0 * x + f₂ 0 / 2 * x ^ 2 + f₃ 0 / 6 * x ^ 3 + C / 24 * x ^ 4)
    (fun x => f₁ 0 + f₂ 0 * x + f₃ 0 / 2 * x ^ 2 + C / 6 * x ^ 3) h₁
  · intro x _
    convert (((((hasDerivAt_id x).const_mul (f₁ 0)).const_add (f 0)).add
      (((hasDerivAt_id x).pow 2).const_mul (f₂ 0 / 2))).add
      (((hasDerivAt_id x).pow 3).const_mul (f₃ 0 / 6))).add
      (((hasDerivAt_id x).pow 4).const_mul (C / 24)) using 1 <;> (dsimp; ring)
  · exact taylor_third_upper f₁ f₂ f₃ f₄ C h₂ h₃ h₄ hC
  · simp

theorem taylor_second_abs (f f₁ f₂ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x ∈ Icc 0 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 1, HasDerivAt f₁ (f₂ x) x)
    (hC : ∀ x ∈ Icc 0 1, |f₂ x| ≤ C) :
    |f 1 - f 0 - f₁ 0| ≤ C / 2 := by
  have hu := taylor_second_upper f f₁ f₂ C h₁ h₂
    (fun x hx => (le_abs_self _).trans (hC x hx)) 1 (by norm_num)
  have hl := taylor_second_upper (fun x => -f x) (fun x => -f₁ x) (fun x => -f₂ x) C
    (fun x hx => (h₁ x hx).neg) (fun x hx => (h₂ x hx).neg)
    (fun x hx => (neg_le_abs _).trans (hC x hx)) 1 (by norm_num)
  simp only [one_pow, mul_one] at hu hl
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem taylor_third_abs (f f₁ f₂ f₃ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x ∈ Icc 0 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 1, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x ∈ Icc 0 1, HasDerivAt f₂ (f₃ x) x)
    (hC : ∀ x ∈ Icc 0 1, |f₃ x| ≤ C) :
    |f 1 - f 0 - f₁ 0 - f₂ 0 / 2| ≤ C / 6 := by
  have hu := taylor_third_upper f f₁ f₂ f₃ C h₁ h₂ h₃
    (fun x hx => (le_abs_self _).trans (hC x hx)) 1 (by norm_num)
  have hl := taylor_third_upper (fun x => -f x) (fun x => -f₁ x) (fun x => -f₂ x)
    (fun x => -f₃ x) C (fun x hx => (h₁ x hx).neg) (fun x hx => (h₂ x hx).neg)
    (fun x hx => (h₃ x hx).neg)
    (fun x hx => (neg_le_abs _).trans (hC x hx)) 1 (by norm_num)
  simp only [one_pow, mul_one] at hu hl
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem taylor_fourth_abs (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x ∈ Icc 0 1, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc 0 1, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x ∈ Icc 0 1, HasDerivAt f₂ (f₃ x) x)
    (h₄ : ∀ x ∈ Icc 0 1, HasDerivAt f₃ (f₄ x) x)
    (hC : ∀ x ∈ Icc 0 1, |f₄ x| ≤ C) :
    |f 1 - f 0 - f₁ 0 - f₂ 0 / 2 - f₃ 0 / 6| ≤ C / 24 := by
  have hu := taylor_fourth_upper f f₁ f₂ f₃ f₄ C h₁ h₂ h₃ h₄
    (fun x hx => (le_abs_self _).trans (hC x hx)) 1 (by norm_num)
  have hl := taylor_fourth_upper (fun x => -f x) (fun x => -f₁ x) (fun x => -f₂ x)
    (fun x => -f₃ x) (fun x => -f₄ x) C (fun x hx => (h₁ x hx).neg)
    (fun x hx => (h₂ x hx).neg) (fun x hx => (h₃ x hx).neg) (fun x hx => (h₄ x hx).neg)
    (fun x hx => (neg_le_abs _).trans (hC x hx)) 1 (by norm_num)
  simp only [one_pow, mul_one] at hu hl
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem hasDerivAt_scaled_affine_comp (f : ℝ → ℝ) (f' x h t : ℝ) (k : ℕ)
    (hf : HasDerivAt f f' (x + h * t)) :
    HasDerivAt (fun u => h ^ k * f (x + h * u)) (h ^ (k + 1) * f') t := by
  convert (hf.comp t (((hasDerivAt_id t).const_mul h).const_add x)).const_mul (h ^ k)
    using 1 <;> (dsimp; ring)

theorem taylor_second_global (f f₁ f₂ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hC : ∀ x, |f₂ x| ≤ C) (x h : ℝ) :
    |f (x + h) - f x - h * f₁ x| ≤ C / 2 * |h| ^ 2 := by
  have hd₁ (t : ℝ) : HasDerivAt (fun u => f (x + h * u))
      (h * f₁ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f _ x h t 0 (h₁ _)
  have hd₂ (t : ℝ) : HasDerivAt (fun u => h * f₁ (x + h * u))
      (h ^ 2 * f₂ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₁ _ x h t 1 (h₂ _)
  have hb (t : ℝ) : |h ^ 2 * f₂ (x + h * t)| ≤ |h| ^ 2 * C := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hh := taylor_second_abs _ _ _ (|h| ^ 2 * C)
    (fun t _ => hd₁ t) (fun t _ => hd₂ t) (fun t _ => hb t)
  convert hh using 1 <;> (try simp only [mul_one, mul_zero, add_zero]) <;> ring

theorem taylor_third_global (f f₁ f₂ f₃ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hC : ∀ x, |f₃ x| ≤ C) (x h : ℝ) :
    |f (x + h) - f x - h * f₁ x - h ^ 2 * f₂ x / 2| ≤ C / 6 * |h| ^ 3 := by
  have hd₁ (t : ℝ) : HasDerivAt (fun u => f (x + h * u))
      (h * f₁ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f _ x h t 0 (h₁ _)
  have hd₂ (t : ℝ) : HasDerivAt (fun u => h * f₁ (x + h * u))
      (h ^ 2 * f₂ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₁ _ x h t 1 (h₂ _)
  have hd₃ (t : ℝ) : HasDerivAt (fun u => h ^ 2 * f₂ (x + h * u))
      (h ^ 3 * f₃ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₂ _ x h t 2 (h₃ _)
  have hb (t : ℝ) : |h ^ 3 * f₃ (x + h * t)| ≤ |h| ^ 3 * C := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hh := taylor_third_abs _ _ _ _ (|h| ^ 3 * C)
    (fun t _ => hd₁ t) (fun t _ => hd₂ t) (fun t _ => hd₃ t) (fun t _ => hb t)
  convert hh using 1 <;> (try simp only [mul_one, mul_zero, add_zero]) <;> ring

theorem taylor_fourth_global (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (C : ℝ)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (h₃ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (h₄ : ∀ x, HasDerivAt f₃ (f₄ x) x)
    (hC : ∀ x, |f₄ x| ≤ C) (x h : ℝ) :
    |f (x + h) - f x - h * f₁ x - h ^ 2 * f₂ x / 2 - h ^ 3 * f₃ x / 6| ≤
      C / 24 * |h| ^ 4 := by
  have hd₁ (t : ℝ) : HasDerivAt (fun u => f (x + h * u))
      (h * f₁ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f _ x h t 0 (h₁ _)
  have hd₂ (t : ℝ) : HasDerivAt (fun u => h * f₁ (x + h * u))
      (h ^ 2 * f₂ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₁ _ x h t 1 (h₂ _)
  have hd₃ (t : ℝ) : HasDerivAt (fun u => h ^ 2 * f₂ (x + h * u))
      (h ^ 3 * f₃ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₂ _ x h t 2 (h₃ _)
  have hd₄ (t : ℝ) : HasDerivAt (fun u => h ^ 3 * f₃ (x + h * u))
      (h ^ 4 * f₄ (x + h * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₃ _ x h t 3 (h₄ _)
  have hb (t : ℝ) : |h ^ 4 * f₄ (x + h * t)| ≤ |h| ^ 4 * C := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hh := taylor_fourth_abs _ _ _ _ _ (|h| ^ 4 * C)
    (fun t _ => hd₁ t) (fun t _ => hd₂ t) (fun t _ => hd₃ t) (fun t _ => hd₄ t) (fun t _ => hb t)
  convert hh using 1 <;> (try simp only [mul_one, mul_zero, add_zero]) <;> ring

end BerryEsseen
