import BerryEsseen.GaussianOddIntegrals
import BerryEsseen.EdgeworthTails

/-! Gaussian comparison tails with the explicit manuscript constant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem gaussian_nat_pow_integrable (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) := by
  apply (gaussian_abs_pow_integrable k b hb).mono' (by fun_prop)
  exact ae_of_all _ (fun x => by simp [Real.norm_eq_abs, abs_mul, abs_pow, (Real.exp_pos _).le])

theorem gaussian_linear_tail_integral (a : ℝ) :
    (∫ x : ℝ in Ioi a, x * Real.exp (-x ^ 2 / 2)) = Real.exp (-a ^ 2 / 2) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -Real.exp (-y ^ 2 / 2))
      (x * Real.exp (-x ^ 2 / 2)) x := by
    convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp).neg using 1
    dsimp only [Pi.neg_apply, Pi.sub_apply, id_eq]
    ring
  have hi : Integrable (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) := by
    convert gaussian_nat_pow_integrable 1 (1 / 2) (by norm_num) using 1
    funext x
    simp only [pow_one]
    congr 2
    ring
  have ht : Tendsto (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h := (gaussian_polynomial_tendsto_zero 0 (1 / 2) (by norm_num)).neg
    convert h using 1 <;> simp only [pow_zero, one_mul, neg_zero]
    funext x
    congr 2
    ring
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi.integrableOn ht

theorem gaussian_tail_integral_le (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ in Ioi a, Real.exp (-x ^ 2 / 2)) ≤ Real.exp (-a ^ 2 / 2) / a := by
  have h0 : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2)) := by
    convert gaussian_nat_pow_integrable 0 (1 / 2) (by norm_num) using 1
    funext x
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have h1 : Integrable (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) := by
    convert gaussian_nat_pow_integrable 1 (1 / 2) (by norm_num) using 1
    funext x
    simp only [pow_one]
    congr 1
    ring
  calc
    _ ≤ ∫ x : ℝ in Ioi a, (x * Real.exp (-x ^ 2 / 2)) / a := by
      apply integral_mono_ae h0.integrableOn (h1.div_const a).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      apply (le_div_iff₀ ha).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hx.le (Real.exp_pos (-x ^ 2 / 2)).le]
    _ = _ := by rw [integral_div, gaussian_linear_tail_integral]

theorem gaussian_quadratic_tail_integral_le (a : ℝ) (ha : 0 < a) :
    (∫ x : ℝ in Ioi a, x ^ 2 * Real.exp (-x ^ 2 / 2)) ≤
      (a + 1 / a) * Real.exp (-a ^ 2 / 2) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -y * Real.exp (-y ^ 2 / 2))
      ((x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) x := by
    convert ((hasDerivAt_id x).neg.mul (((hasDerivAt_pow 2 x).neg.div_const 2).exp)) using 1
    dsimp only [Pi.neg_apply, Pi.sub_apply, id_eq]
    ring
  have h0 : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2)) := by
    convert gaussian_nat_pow_integrable 0 (1 / 2) (by norm_num) using 1
    funext x
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have h2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / 2)) := by
    convert gaussian_nat_pow_integrable 2 (1 / 2) (by norm_num) using 1
    funext x
    congr 2
    ring
  have hi : Integrable (fun x : ℝ => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) := by
    convert h2.sub h0 using 1
    funext x
    dsimp only [Pi.sub_apply]
    ring
  have ht : Tendsto (fun x : ℝ => -x * Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h := (gaussian_polynomial_tendsto_zero 1 (1 / 2) (by norm_num)).neg
    convert h using 1
    · funext x
      simp only [pow_one, neg_mul]
      congr 2
      ring
    · simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := a) (fun x _ => hd x) hi.integrableOn ht
  have he : (fun x : ℝ => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) =
      (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / 2) - Real.exp (-x ^ 2 / 2)) := by funext x; ring
  rw [he, integral_sub h2.integrableOn h0.integrableOn] at h
  have hl := gaussian_tail_integral_le a ha
  calc
    _ ≤ a * Real.exp (-a ^ 2 / 2) + Real.exp (-a ^ 2 / 2) / a := by linarith only [h, hl]
    _ = _ := by ring

theorem even_function_tail_integral (f : ℝ → ℝ) (hf : ∀ t, f (-t) = f t) (a : ℝ) (ha : 0 < a) :
    (∫ t in {t : ℝ | a ≤ |t|}, f t) = 2 * ∫ t in Ici a, f t := by
  have hfabs (t : ℝ) : f |t| = f t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht), hf]
  have hset : MeasurableSet {t : ℝ | a ≤ |t|} := measurableSet_le measurable_const measurable_abs
  have hfun : ({t : ℝ | a ≤ |t|}).indicator f = fun t => (Ici a).indicator f |t| := by
    funext t
    simp only [Set.indicator_apply, mem_setOf_eq, mem_Ici, hfabs]
  rw [← integral_indicator hset, hfun, integral_comp_abs,
    integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  rw [show Ici a ∩ Ioi 0 = Ici a from inter_eq_left.mpr (fun t ht => lt_of_lt_of_le ha ht)]

def edgeworthTailIntegrand (n : ℕ) (κ t : ℝ) : ℝ := ‖edgeworthChar n κ t‖ / |t|

theorem edgeworthTailIntegrand_nonneg (n : ℕ) (κ t : ℝ) : 0 ≤ edgeworthTailIntegrand n κ t := by
  unfold edgeworthTailIntegrand
  positivity

theorem edgeworthTailIntegrand_measurable (n : ℕ) (κ : ℝ) : Measurable (edgeworthTailIntegrand n κ) := by
  unfold edgeworthTailIntegrand edgeworthChar
  fun_prop

theorem edgeworthTailIntegrand_even (n : ℕ) (κ t : ℝ) :
    edgeworthTailIntegrand n κ (-t) = edgeworthTailIntegrand n κ t := by
  have he : edgeworthChar n κ (-t) = conj (edgeworthChar n κ t) := by
    unfold edgeworthChar
    rw [neg_sq]
    simp only [Complex.ofReal_neg, map_mul, map_sub, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_I, map_one, map_ofNat]
    ring
  simp only [edgeworthTailIntegrand, he, Complex.norm_conj, abs_neg]

theorem edgeworthTailIntegrand_positive_bound (n : ℕ) (κ a t : ℝ) (ha : 0 < a) (ht : a ≤ t) :
    edgeworthTailIntegrand n κ t ≤
      t * Real.exp (-t ^ 2 / 2) / a ^ 2 +
        (|κ| / (6 * Real.sqrt (n : ℝ))) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
  have ht0 : 0 < t := ha.trans_le ht
  have hb := div_le_div_of_nonneg_right (edgeworthChar_norm_bound n κ t) ht0.le
  rw [abs_of_pos ht0] at hb
  change edgeworthTailIntegrand n κ t ≤ _
  have hsplit : Real.exp (-t ^ 2 / 2) * (1 + |κ| * t ^ 3 / (6 * Real.sqrt (n : ℝ))) / t =
      Real.exp (-t ^ 2 / 2) / t + (|κ| / (6 * Real.sqrt (n : ℝ))) * (t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
    field_simp
  have hfirst : Real.exp (-t ^ 2 / 2) / t ≤ t * Real.exp (-t ^ 2 / 2) / a ^ 2 := by
    apply (div_le_div_iff₀ ht0 (sq_pos_of_pos ha)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (show a ^ 2 ≤ t ^ 2 by nlinarith)
      (Real.exp_pos (-t ^ 2 / 2)).le]
  have he : edgeworthTailIntegrand n κ t = ‖edgeworthChar n κ t‖ / t := by
    rw [edgeworthTailIntegrand, abs_of_pos ht0]
  rw [← he, hsplit] at hb
  exact hb.trans (add_le_add_left hfirst _)

theorem gaussian_half_pow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x ^ 2 / 2)) := by
  convert gaussian_nat_pow_integrable k (1 / 2) (by norm_num) using 1
  funext x
  congr 2
  ring

theorem edgeworthTailIntegrand_integrableOn (n : ℕ) (κ a : ℝ) (ha : 0 < a) :
    IntegrableOn (edgeworthTailIntegrand n κ) (Ici a) := by
  have h1 : Integrable (fun t : ℝ => t * Real.exp (-t ^ 2 / 2) / a ^ 2) := by
    simpa only [pow_one] using (gaussian_half_pow_integrable 1).div_const (a ^ 2)
  have h2 := (gaussian_half_pow_integrable 2).const_mul (|κ| / (6 * Real.sqrt (n : ℝ)))
  apply (h1.add h2).integrableOn.mono' (edgeworthTailIntegrand_measurable n κ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (edgeworthTailIntegrand_nonneg n κ t)]
  exact edgeworthTailIntegrand_positive_bound n κ a t ha ht

theorem edgeworthTailIntegrand_integrable_tail (n : ℕ) (κ a : ℝ) (ha : 0 < a) :
    IntegrableOn (edgeworthTailIntegrand n κ) {t : ℝ | a ≤ |t|} := by
  have hr := edgeworthTailIntegrand_integrableOn n κ a ha
  have hl : IntegrableOn (edgeworthTailIntegrand n κ) (Iic (-a)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, edgeworthTailIntegrand_even, neg_preimage, neg_Iic, neg_neg]
    exact hr
  have he : {t : ℝ | a ≤ |t|} = Iic (-a) ∪ Ici a := by
    ext t
    simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici]
    constructor
    · intro ht
      rcases le_abs.mp ht with ht | ht
      · exact Or.inr ht
      · exact Or.inl (by linarith)
    · rintro (ht | ht)
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl ht)
  rw [he]
  exact integrableOn_union.mpr ⟨hl, hr⟩

theorem edgeworth_positive_tail_integral_bound (n : ℕ) (κ a : ℝ) (ha : 0 < a) :
    (∫ t in Ici a, edgeworthTailIntegrand n κ t) ≤
      Real.exp (-a ^ 2 / 2) / a ^ 2 +
        (|κ| / (6 * Real.sqrt (n : ℝ))) * ((a + 1 / a) * Real.exp (-a ^ 2 / 2)) := by
  have h1 : Integrable (fun t : ℝ => t * Real.exp (-t ^ 2 / 2) / a ^ 2) := by
    simpa only [pow_one] using (gaussian_half_pow_integrable 1).div_const (a ^ 2)
  have h2 := (gaussian_half_pow_integrable 2).const_mul (|κ| / (6 * Real.sqrt (n : ℝ)))
  calc
    _ ≤ ∫ t in Ici a, (t * Real.exp (-t ^ 2 / 2) / a ^ 2 +
      (|κ| / (6 * Real.sqrt (n : ℝ))) * (t ^ 2 * Real.exp (-t ^ 2 / 2))) := by
      apply integral_mono_ae (edgeworthTailIntegrand_integrableOn n κ a ha) (h1.add h2).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact edgeworthTailIntegrand_positive_bound n κ a t ha ht
    _ = ∫ t in Ioi a, (t * Real.exp (-t ^ 2 / 2) / a ^ 2 +
      (|κ| / (6 * Real.sqrt (n : ℝ))) * (t ^ 2 * Real.exp (-t ^ 2 / 2))) := integral_Ici_eq_integral_Ioi
    _ = Real.exp (-a ^ 2 / 2) / a ^ 2 +
      (|κ| / (6 * Real.sqrt (n : ℝ))) * (∫ t in Ioi a, t ^ 2 * Real.exp (-t ^ 2 / 2)) := by
      rw [integral_add h1.integrableOn h2.integrableOn, integral_div, integral_const_mul,
        gaussian_linear_tail_integral]
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left (gaussian_quadratic_tail_integral_le a ha) (by positivity)) _

theorem edgeworth_tail_integral_bound (n : ℕ) (κ a : ℝ) (ha : 0 < a) :
    (∫ t in {t : ℝ | a ≤ |t|}, edgeworthTailIntegrand n κ t) ≤
      2 * (Real.exp (-a ^ 2 / 2) / a ^ 2 +
        (|κ| / (6 * Real.sqrt (n : ℝ))) * ((a + 1 / a) * Real.exp (-a ^ 2 / 2))) := by
  rw [even_function_tail_integral _ (edgeworthTailIntegrand_even n κ) a ha]
  exact mul_le_mul_of_nonneg_left (edgeworth_positive_tail_integral_bound n κ a ha) (by norm_num)

theorem effective_edgeworth_gaussian_tail (n : ℕ) (hn : 2 ≤ n) (κ : ℝ) (hκ : |κ| ≤ 1.84) :
    (∫ t in {t : ℝ | Real.sqrt (n : ℝ) / 2 ≤ |t|}, edgeworthTailIntegrand n κ t) ≤
      5 * Real.exp (-(n : ℝ) / 8) := by
  let s := Real.sqrt (n : ℝ)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hn0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have h := edgeworth_tail_integral_bound n κ (s / 2) (by positivity)
  have hex : -(s / 2) ^ 2 / 2 = -(n : ℝ) / 8 := by nlinarith only [hs2]
  rw [hex] at h
  have he : 2 * (Real.exp (-(n : ℝ) / 8) / (s / 2) ^ 2 +
      (|κ| / (6 * s)) * ((s / 2 + 1 / (s / 2)) * Real.exp (-(n : ℝ) / 8))) =
      (8 / (n : ℝ) + |κ| * (1 / 6 + 2 / (3 * (n : ℝ)))) * Real.exp (-(n : ℝ) / 8) := by
    rw [← hs2]
    field_simp
    <;> ring
  change _ ≤ 2 * (Real.exp (-(n : ℝ) / 8) / (s / 2) ^ 2 +
      (|κ| / (6 * s)) * ((s / 2 + 1 / (s / 2)) * Real.exp (-(n : ℝ) / 8))) at h
  rw [he] at h
  have h8 : 8 / (n : ℝ) ≤ 4 := (div_le_iff₀ hn0).mpr (by linarith)
  have h2 : 2 / (3 * (n : ℝ)) ≤ 1 / 3 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hp : |κ| * (1 / 6 + 2 / (3 * (n : ℝ))) ≤ (1.84 : ℝ) * (1 / 2) := by
    apply mul_le_mul hκ (by linarith) (by positivity) (by norm_num)
  have hc : 8 / (n : ℝ) + |κ| * (1 / 6 + 2 / (3 * (n : ℝ))) ≤ 5 := by linarith
  exact h.trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le)

end BerryEsseen
