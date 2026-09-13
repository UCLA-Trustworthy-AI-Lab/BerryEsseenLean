import BerryEsseen.ManuscriptIndependentCopy
import BerryEsseen.NormalizedFourier
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! Appendix effective low-frequency pointwise estimate with the manuscript constants. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem charFun_sub_one_quadratic_bound (P : StandardizedLaw) (u : ℝ) :
    ‖charFun P.measure u - 1‖ ≤ u ^ 2 / 2 := by
  let f := fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1 - (u * x : ℝ) * Complex.I
  have hpoint (x : ℝ) : ‖f x‖ ≤ (u ^ 2 / 2) * x ^ 2 := by
    have h := unitExp_linear_remainder_sharp (u * x)
    convert h using 1 <;> ring
  have hf : Integrable f P.measure := (P.second_integrable.const_mul (u ^ 2 / 2)).mono' (by dsimp only [f]; fun_prop)
    (ae_of_all _ hpoint)
  have he : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I)) P.measure := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  have he0 : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1) P.measure := he.sub (integrable_const _)
  have hlin : Integrable (fun x : ℝ => (x : ℂ) * ((u : ℂ) * Complex.I)) P.measure := P.first_integrable.ofReal.mul_const _
  have hfun : f = fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1 - (x : ℂ) * ((u : ℂ) * Complex.I) := by
    funext x
    dsimp only [f]
    push_cast
    ring
  have hmean : (∫ x : ℝ, (x : ℂ) ∂P.measure) = 0 := by
    simpa only [P.mean_zero, Complex.ofReal_zero] using (integral_complex_ofReal (f := fun x : ℝ => x) (μ := P.measure))
  have hint : (∫ x, f x ∂P.measure) = charFun P.measure u - 1 := by
    rw [hfun]
    dsimp only
    rw [integral_sub he0 hlin, integral_sub he (integrable_const _),
      integral_mul_const, hmean, zero_mul, sub_zero]
    simp only [integral_const, probReal_univ, one_smul]
    rw [charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [← hint]
  calc
    _ ≤ ∫ x, ‖f x‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (u ^ 2 / 2) * x ^ 2 ∂P.measure := integral_mono hf.norm (P.second_integrable.const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, P.second_one, mul_one]

theorem effective_charFun_log_bound (P : StandardizedLaw) (hβ : thirdMoment P ≤ 1.84)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    ‖Complex.log (charFun P.measure u) - cubicExponent u (signedThirdMoment P)‖ ≤ (0.61 : ℝ) * |u| ^ 4 := by
  let w := charFun P.measure u - 1
  have hw : ‖w‖ ≤ u ^ 2 / 2 := charFun_sub_one_quadratic_bound P u
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hw8 : ‖w‖ ≤ 1 / 8 := by linarith
  have hlog := Complex.norm_log_one_add_sub_self_le (by linarith : ‖w‖ < 1)
  have hlog' : ‖Complex.log (1 + w) - w‖ ≤ |u| ^ 4 / 7 := by
    have hw2 : ‖w‖ ^ 2 ≤ |u| ^ 4 / 4 := by
      have h := pow_le_pow_left₀ (norm_nonneg w) hw 2
      nlinarith [show |u| ^ 4 = (u ^ 2) ^ 2 by rw [← sq_abs u]; ring]
    have hdiv := div_le_div₀ (by positivity : 0 ≤ |u| ^ 4 / 4) hw2 (by norm_num : (0 : ℝ) < 7 / 4)
      (by linarith : 7 / 4 ≤ 2 * (1 - ‖w‖))
    apply hlog.trans
    have hne : 1 - ‖w‖ ≠ 0 := by linarith
    convert hdiv using 1 <;> field_simp [hne]
  have h1 : 1 + w = charFun P.measure u := by dsimp only [w]; ring
  rw [h1] at hlog'
  have hc := effective_charFun_cubic_bound P hβ hb u
  have he : charFun P.measure u - 1 + (u : ℂ) ^ 2 / 2 +
      (u : ℂ) ^ 3 * (signedThirdMoment P : ℂ) * Complex.I / 6 = w - cubicExponent u (signedThirdMoment P) := by
    dsimp only [w, cubicExponent]
    ring
  rw [he] at hc
  have htri := norm_sub_le_norm_sub_add_norm_sub (Complex.log (charFun P.measure u)) w (cubicExponent u (signedThirdMoment P))
  have hpow := pow_nonneg (abs_nonneg u) 4
  linarith


theorem cubic_base_norm_bound (u κ : ℝ) (hu : |u| ≤ 1 / 2) (hκ : |κ| ≤ 2) :
    ‖1 + cubicExponent u κ‖ ≤ 1 - (0.48 : ℝ) * u ^ 2 := by
  let a := u ^ 2
  have ha0 : 0 ≤ a := sq_nonneg u
  have ha : a ≤ 1 / 4 := by dsimp only [a]; nlinarith [sq_abs u, abs_nonneg u]
  have ha2 : a ^ 2 ≤ a / 4 := by nlinarith [mul_le_mul_of_nonneg_right ha ha0]
  have ha3 : a ^ 3 ≤ a / 16 := by
    have h := mul_le_mul_of_nonneg_right ha2 ha0
    nlinarith only [h, ha2]
  have hk2 : κ ^ 2 ≤ 4 := by nlinarith [sq_abs κ, abs_nonneg κ]
  have hk3 := mul_le_mul_of_nonneg_right hk2 (pow_nonneg ha0 3)
  have hnorm : ‖1 + cubicExponent u κ‖ ^ 2 = (1 - a / 2) ^ 2 + κ ^ 2 * a ^ 3 / 36 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, cubicExponent, a, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
    ring
  have hpos : 0 ≤ 1 - (0.48 : ℝ) * a := by linarith
  have hsq : ‖1 + cubicExponent u κ‖ ^ 2 ≤ (1 - (0.48 : ℝ) * a) ^ 2 := by
    rw [hnorm]
    nlinarith only [hk3, ha2, ha3, ha0]
  change ‖1 + cubicExponent u κ‖ ≤ 1 - (0.48 : ℝ) * a
  nlinarith [norm_nonneg (1 + cubicExponent u κ)]

/-- Original independent-copy fourth-moment budget. -/
theorem manuscript_effective_difference_fourth (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) :
    (∫ x, x ^ 4 ∂manuscriptDifferenceLaw P.measure P.measure) ≤ 28.08 := by
  have h4 := bounded_fourth_moment P 6 (by norm_num) hb
  have he : (fun x : ℝ => |x| ^ 4) = (fun x => x ^ 4) := by
    funext x
    calc |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
         _ = x ^ 4 := by rw [sq_abs]; ring
  rw [he] at h4
  rw [manuscriptDifferenceLaw_fourth P h4.1]
  linarith [h4.2]

theorem manuscript_effective_difference_fourth_strict (P : StandardizedLaw)
    (hβ : thirdMoment P < 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) :
    (∫ x, x ^ 4 ∂manuscriptDifferenceLaw P.measure P.measure) < 28.08 := by
  have h4 := bounded_fourth_moment P 6 (by norm_num) hb
  have he : (fun x : ℝ => |x| ^ 4) = (fun x => x ^ 4) := by
    funext x
    calc |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
         _ = x ^ 4 := by rw [sq_abs]; ring
  rw [he] at h4
  rw [manuscriptDifferenceLaw_fourth P h4.1]
  linarith [h4.2]

/-- Cosine Taylor applied to the actual independent difference X-X'. -/
theorem manuscript_effective_charFun_square_bound (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) (u : ℝ) :
    ‖charFun P.measure u‖ ^ 2 ≤ 1 - u ^ 2 + (1.17 : ℝ) * u ^ 4 := by
  let ν := manuscriptDifferenceLaw P.measure P.measure
  have h4 := bounded_fourth_moment P 6 (by norm_num) hb
  have he : (fun x : ℝ => |x| ^ 4) = (fun x => x ^ 4) := by
    funext x
    calc |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
         _ = x ^ 4 := by rw [sq_abs]; ring
  rw [he] at h4
  have hi4 := manuscriptDifferenceLaw_fourth_integrable P h4.1
  have hi2 := manuscriptDifferenceLaw_second_integrable P
  have hcos : Integrable (fun x : ℝ => Real.cos (u * x)) ν := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u * x))
  have hpoly : Integrable (fun x : ℝ => 1 - (u ^ 2 / 2) * x ^ 2) ν := (integrable_const (1 : ℝ)).sub (hi2.const_mul (u ^ 2 / 2))
  have hint := integral_mono hcos (hpoly.add (hi4.const_mul (u ^ 4 / 24))) (fun x => ?_)
  · change (∫ x, Real.cos (u * x) ∂ν) ≤ ∫ x, 1 - (u ^ 2 / 2) * x ^ 2 + (u ^ 4 / 24) * x ^ 4 ∂ν at hint
    rw [integral_add hpoly (hi4.const_mul (u ^ 4 / 24)),
      integral_sub (integrable_const _) (hi2.const_mul _), integral_const_mul, integral_const_mul] at hint
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
    rw [manuscriptDifferenceLaw_cos, manuscriptDifferenceLaw_second] at hint
    have hm := mul_le_mul_of_nonneg_left (manuscript_effective_difference_fourth P hβ hb) (show 0 ≤ u ^ 4 / 24 by positivity)
    linarith
  · have h := (abs_le.mp (cos_fourth_remainder (u * x))).2
    have he4 : |u * x| ^ 4 = u ^ 4 * x ^ 4 := by
      calc |u * x| ^ 4 = (|u * x| ^ 2) ^ 2 := by ring
           _ = u ^ 4 * x ^ 4 := by rw [sq_abs]; ring
    rw [he4] at h
    dsimp
    nlinarith only [h]

theorem effective_charFun_decay (P : StandardizedLaw) (hβ : thirdMoment P ≤ 1.84)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    ‖charFun P.measure u‖ ≤ Real.exp (-(0.35 : ℝ) * u ^ 2) := by
  have hcopy := manuscript_effective_charFun_square_bound P hβ hb u
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hu4 : u ^ 4 ≤ u ^ 2 / 4 := by nlinarith [mul_le_mul_of_nonneg_right hu2 (sq_nonneg u)]
  have hsquare : ‖charFun P.measure u‖ ^ 2 ≤ 1 - (0.7 : ℝ) * u ^ 2 := by nlinarith only [hcopy, hu4, sq_nonneg u]
  have he := Real.add_one_le_exp (-(0.7 : ℝ) * u ^ 2)
  have hexp : Real.exp (-(0.7 : ℝ) * u ^ 2) = (Real.exp (-(0.35 : ℝ) * u ^ 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hexp] at he
  nlinarith only [hsquare, he, norm_nonneg (charFun P.measure u), Real.exp_pos (-(0.35 : ℝ) * u ^ 2)]


theorem complex_exp_segment_bound (a b : ℂ) (M : ℝ) (ha : a.re ≤ M) (hb : b.re ≤ M) :
    ‖Complex.exp a - Complex.exp b‖ ≤ Real.exp M * ‖a - b‖ := by
  have hs : Convex ℝ {z : ℂ | z.re ≤ M} :=
    (convex_Iic M).linear_preimage Complex.reLm
  exact hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hz) hb ha

theorem cubic_exponential_linear_error_sharp (n : ℕ) (u κ : ℝ) :
    ‖Complex.exp ((n : ℂ) * cubicExponent u κ) -
      (Real.exp (-(n : ℝ) * u ^ 2 / 2) : ℂ) *
        (1 - (n : ℂ) * (u : ℂ) ^ 3 * (κ : ℂ) * Complex.I / 6)‖ ≤
      Real.exp (-(n : ℝ) * u ^ 2 / 2) * ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 / 2 := by
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
  have h := unitExp_linear_remainder_sharp y
  rw [sub_add_eq_sub_sub]
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos a).le
  convert hh using 1
  dsimp [a, y]
  ring


theorem effective_charFun_power_cubic (P : StandardizedLaw) (hβ : thirdMoment P ≤ 1.84)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6) (u : ℝ) (hu : |u| ≤ 1 / 2) (n : ℕ) :
    ‖charFun P.measure u ^ n - Complex.exp ((n : ℂ) * cubicExponent u (signedThirdMoment P))‖ ≤
      (0.61 : ℝ) * (n : ℝ) * |u| ^ 4 * Real.exp (-(0.35 : ℝ) * (n : ℝ) * u ^ 2) := by
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hne : charFun P.measure u ≠ 0 := by
    intro he
    have h := charFun_sub_one_quadratic_bound P u
    rw [he] at h
    norm_num at h
    linarith
  have hl : Real.log ‖charFun P.measure u‖ ≤ -(0.35 : ℝ) * u ^ 2 :=
    (Real.log_le_iff_le_exp (norm_pos_iff.mpr hne)).mpr (effective_charFun_decay P hβ hb u hu)
  have ha : ((n : ℂ) * Complex.log (charFun P.measure u)).re ≤ -(0.35 : ℝ) * (n : ℝ) * u ^ 2 := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.log_re]
    nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) n)]
  have hb' : ((n : ℂ) * cubicExponent u (signedThirdMoment P)).re ≤ -(0.35 : ℝ) * (n : ℝ) * u ^ 2 := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, cubicExponent_re]
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg u)]
  have he := complex_exp_segment_bound ((n : ℂ) * Complex.log (charFun P.measure u))
    ((n : ℂ) * cubicExponent u (signedThirdMoment P)) (-(0.35 : ℝ) * (n : ℝ) * u ^ 2) ha hb'
  rw [Complex.exp_nat_mul, Complex.exp_log hne, ← mul_sub, norm_mul] at he
  simp only [Complex.norm_natCast] at he
  have hlb := effective_charFun_log_bound P hβ hb u hu
  calc
    _ ≤ Real.exp (-(0.35 : ℝ) * (n : ℝ) * u ^ 2) *
      ((n : ℝ) * ‖Complex.log (charFun P.measure u) - cubicExponent u (signedThirdMoment P)‖) := he
    _ ≤ Real.exp (-(0.35 : ℝ) * (n : ℝ) * u ^ 2) * ((n : ℝ) * ((0.61 : ℝ) * |u| ^ 4)) := by gcongr
    _ = _ := by ring

theorem effective_charFun_edgeworth_low_frequency (P : StandardizedLaw)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht : |t| ≤ Real.sqrt (n : ℝ) / 2) :
    ‖charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n - edgeworthChar n (signedThirdMoment P) t‖ ≤
      ((0.61 : ℝ) * |t| ^ 4 * Real.exp (-(0.35 : ℝ) * t ^ 2) +
        (0.048 : ℝ) * |t| ^ 6 * Real.exp (-t ^ 2 / 2)) / (n : ℝ) := by
  let s := Real.sqrt (n : ℝ)
  let u := t / s
  let κ := signedThirdMoment P
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hu : |u| ≤ 1 / 2 := by
    dsimp [u]
    rw [abs_div, abs_of_pos hs]
    apply (div_le_iff₀ hs).2
    linarith
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
  have hr1 := effective_charFun_power_cubic P hβ hb u hu n
  have hr2 := cubic_exponential_linear_error_sharp n u κ
  rw [heq] at hr2
  have he1 : Real.exp (-(0.35 : ℝ) * (n : ℝ) * u ^ 2) = Real.exp (-(0.35 : ℝ) * t ^ 2) := by
    congr 1
    nlinarith [hu2]
  have he2 : Real.exp (-(n : ℝ) * u ^ 2 / 2) = Real.exp (-t ^ 2 / 2) := by
    congr 1
    nlinarith [hu2]
  have hκ : |κ| ≤ 1.84 := (signedThirdMoment_abs_le P).trans hβ
  have hk2 : κ ^ 2 ≤ (0.048 : ℝ) * 72 := by nlinarith [sq_abs κ, abs_nonneg κ]
  have hterm : ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 / 2 ≤ (0.048 : ℝ) * |t| ^ 6 / (n : ℝ) := by
    rw [hu3]
    have hsq : (κ * t ^ 3 / (6 * s)) ^ 2 / 2 = κ ^ 2 * |t| ^ 6 / (72 * (n : ℝ)) := by
      rw [← hs2, div_pow, mul_pow, mul_pow]
      have hab : |t| ^ 6 = t ^ 6 := by
        calc |t| ^ 6 = (|t| ^ 2) ^ 3 := by ring
             _ = (t ^ 2) ^ 3 := by rw [sq_abs]
             _ = t ^ 6 := by ring
      rw [hab]
      ring
    rw [hsq]
    apply (div_le_iff₀ (by positivity : 0 < 72 * (n : ℝ))).2
    have h := mul_le_mul_of_nonneg_right hk2 (pow_nonneg (abs_nonneg t) 6)
    convert h using 1
    field_simp
  have htri := norm_sub_le_norm_sub_add_norm_sub (charFun P.measure u ^ n)
    (Complex.exp ((n : ℂ) * cubicExponent u κ)) (edgeworthChar n κ t)
  calc
    _ ≤ (0.61 : ℝ) * (n : ℝ) * |u| ^ 4 * Real.exp (-(0.35 : ℝ) * (n : ℝ) * u ^ 2) +
      Real.exp (-(n : ℝ) * u ^ 2 / 2) * ((n : ℝ) * u ^ 3 * κ / 6) ^ 2 / 2 := htri.trans (add_le_add hr1 hr2)
    _ ≤ (0.61 : ℝ) * (n : ℝ) * |u| ^ 4 * Real.exp (-(0.35 : ℝ) * t ^ 2) +
      Real.exp (-t ^ 2 / 2) * ((0.048 : ℝ) * |t| ^ 6 / (n : ℝ)) := by
      rw [he1, he2, mul_div_assoc]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le) _
    _ = _ := by
      rw [show (0.61 : ℝ) * (n : ℝ) * |u| ^ 4 = (0.61 : ℝ) * ((n : ℝ) * |u| ^ 4) by ring, hu4]
      ring

end BerryEsseen
