import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The manuscript's one-sided loss lemma, including strict threshold events.
The direct fourth-moment argument below avoids clipping and gives C = 11000,
with no smallness restriction on the fourth moment. -/
noncomputable section
open MeasureTheory Set
namespace BerryEsseen

theorem abs_le_thousand_fourth {w : ℝ} (hw : 1 / 10 ≤ |w|) :
    |w| ≤ 1000 * w ^ 4 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 10) hw 3
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg w)
  have he : |w| ^ 4 = w ^ 4 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
  have hm' : |w| / 1000 ≤ |w| ^ 4 := by nlinarith only [hm]
  rw [he] at hm'
  linarith

theorem abs_le_tenth_add_fourth (w : ℝ) :
    |w| ≤ 1 / 10 + 1000 * w ^ 4 := by
  by_cases hw : 1 / 10 ≤ |w|
  · linarith [abs_le_thousand_fourth hw]
  · have h := pow_nonneg (sq_nonneg w) 2
    nlinarith

theorem positive_part_threshold_bound (w u : ℝ) (hu : 0 ≤ u) :
    max w 0 ≤ u + (1 / 10 : ℝ) * (if u < w then 1 else 0) + 1000 * w ^ 4 := by
  by_cases hw : u < w
  · simp only [hw, ↓reduceIte, mul_one]
    have hpos : 0 ≤ w := le_trans hu (le_of_lt hw)
    rw [max_eq_left hpos]
    have h := abs_le_tenth_add_fourth w
    rw [abs_of_nonneg hpos] at h
    linarith
  · simp only [hw, ↓reduceIte, mul_zero, add_zero]
    have hmax : max w 0 ≤ u := max_le (le_of_not_gt hw) hu
    nlinarith [sq_nonneg (w ^ 2)]

theorem centered_threshold_bound (w r : ℝ) (_hr : 0 ≤ r) :
    w ≤ (1 / 10 + r) * (if -r < w then 1 else 0) - r + 1000 * w ^ 4 := by
  by_cases hw : -r < w
  · simp only [hw, ↓reduceIte, mul_one]
    have h := abs_le_tenth_add_fourth w
    linarith [le_abs_self w]
  · simp only [hw, ↓reduceIte, mul_zero, zero_sub]
    have hw' : w ≤ -r := le_of_not_gt hw
    nlinarith [sq_nonneg (w ^ 2)]

theorem positive_part_negative_threshold_bound (w r : ℝ) (hr : 0 ≤ r) :
    max w 0 ≤ (1 / 10 : ℝ) * (if -r < w then 1 else 0) + 1000 * w ^ 4 := by
  by_cases hw : -r < w
  · simp only [hw, ↓reduceIte, mul_one]
    by_cases hp : 0 ≤ w
    · rw [max_eq_left hp]
      simpa [abs_of_nonneg hp] using abs_le_tenth_add_fourth w
    · rw [max_eq_right (le_of_not_ge hp)]
      nlinarith [sq_nonneg (w ^ 2)]
  · simp only [hw, ↓reduceIte, mul_zero, zero_add]
    have hp : w ≤ 0 := le_trans (le_of_not_gt hw) (neg_nonpos.mpr hr)
    rw [max_eq_right hp]
    positivity

theorem negative_threshold_probability_bound (w r : ℝ) (hr : 1 / 10 ≤ r) :
    (1 : ℝ) - 10000 * w ^ 4 ≤ if -r < w then 1 else 0 := by
  by_cases hw : -r < w
  · simp only [hw, ↓reduceIte]
    nlinarith [sq_nonneg (w ^ 2)]
  · simp only [hw, ↓reduceIte]
    have ha : 1 / 10 ≤ |w| := by linarith [le_abs_self (-w), abs_neg w]
    have h := abs_le_thousand_fourth ha
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_positive_part_of_centered {W : Ω → ℝ} (hW : Integrable W μ)
    (hmean : (∫ x, W x ∂μ) = 0) :
    (∫ x, max (W x) 0 ∂μ) = (∫ x, |W x| ∂μ) / 2 := by
  have he : (fun x => max (W x) 0) = (fun x => (|W x| + W x) / 2) := by
    funext x
    by_cases h : 0 ≤ W x
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right (le_of_not_ge h), abs_of_nonpos (le_of_not_ge h)]; ring
  rw [he, integral_div, integral_add hW.abs hW, hmean, add_zero]

theorem one_sided_loss_upper_of_value [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (hW : Integrable W μ)
    (h4 : Integrable (fun x => W x ^ 4) μ)
    (hmean : (∫ x, W x ∂μ) = 0)
    {u F : ℝ} (hu : |u| ≤ 1 / 2)
    (hFpos : 0 ≤ u → 3 / 4 * u ≤ F)
    (hFneg : u ≤ 0 → 5 / 4 * u ≤ F) :
    3 / 8 * (∫ x, |W x| ∂μ) - 11000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | u < W x} + F := by
  let A := {x | u < W x}
  let b : Ω → ℝ := A.indicator (fun _ => 1)
  have hA : MeasurableSet A := measurableSet_lt measurable_const hWm
  have hb : Integrable b μ := (integrable_const 1).indicator hA
  have hbeq : (∫ x, b x ∂μ) = μ.real A := integral_indicator_one hA
  have hbnonneg : 0 ≤ μ.real A := ENNReal.toReal_nonneg
  have hM : 0 ≤ ∫ x, W x ^ 4 ∂μ := integral_nonneg (fun _ => by positivity)
  have hp : Integrable (fun x => max (W x) 0) μ := by
    apply hW.abs.mono' (hWm.max measurable_const).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hhalf := integral_positive_part_of_centered hW hmean
  by_cases hupos : 0 ≤ u
  · have hi := integral_mono hp (((integrable_const u).add (hb.const_mul (1 / 10))).add
        (h4.const_mul 1000)) (fun x => positive_part_threshold_bound (W x) u hupos)
    simp only [Pi.add_apply] at hi
    have hsum : Integrable (fun x => u + 1 / 10 * b x) μ :=
      (integrable_const u).add (hb.const_mul (1 / 10))
    rw [integral_add hsum
      (h4.const_mul 1000), integral_add (integrable_const u) (hb.const_mul (1 / 10)),
      integral_const, integral_const_mul, integral_const_mul, hbeq, hhalf] at hi
    simp only [probReal_univ, smul_eq_mul, one_mul] at hi
    have hf := hFpos hupos
    change _ ≤ μ.real A + F
    linarith
  · have huneg : u ≤ 0 := le_of_not_ge hupos
    have hf := hFneg huneg
    by_cases hur : -u ≤ 1 / 10
    · have hi := integral_mono hW (((hb.const_mul (1 / 10 - u)).sub
          (integrable_const (-u))).add (h4.const_mul 1000))
          (fun x => by simpa [b, A, indicator_apply, sub_eq_add_neg] using
            centered_threshold_bound (W x) (-u) (neg_nonneg.mpr huneg))
      have hj := integral_mono hp ((hb.const_mul (1 / 10)).add (h4.const_mul 1000))
          (fun x => by simpa [b, A, indicator_apply] using
            positive_part_negative_threshold_bound (W x) (-u) (neg_nonneg.mpr huneg))
      simp only [Pi.add_apply, Pi.sub_apply] at hi hj
      have hsub : Integrable (fun x => (1 / 10 - u) * b x - -u) μ :=
        (hb.const_mul (1 / 10 - u)).sub (integrable_const (-u))
      rw [integral_add hsub
        (h4.const_mul 1000), integral_sub (hb.const_mul (1 / 10 - u)) (integrable_const (-u))] at hi
      rw [integral_add (hb.const_mul (1 / 10)) (h4.const_mul 1000)] at hj
      simp only [integral_const_mul, integral_const,
        hbeq, hmean, hhalf, probReal_univ, smul_eq_mul, one_mul] at hi hj
      have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 10 + u) hbnonneg
      change _ ≤ μ.real A + F
      nlinarith
    · have hi := integral_mono ((integrable_const 1).sub (h4.const_mul 10000)) hb
          (fun x => by simpa [b, A, indicator_apply] using
            negative_threshold_probability_bound (W x) (-u) (le_of_not_ge hur))
      have hj := integral_mono hW.abs ((integrable_const (1 / 10)).add (h4.const_mul 1000))
          (fun x => abs_le_tenth_add_fourth (W x))
      simp only [Pi.add_apply, Pi.sub_apply] at hi hj
      rw [integral_sub (integrable_const 1) (h4.const_mul 10000)] at hi
      rw [integral_add (integrable_const (1 / 10)) (h4.const_mul 1000)] at hj
      simp only [integral_const_mul, integral_const,
        hbeq, probReal_univ, smul_eq_mul, one_mul] at hi hj
      have hulower := (abs_le.mp hu).1
      change _ ≤ μ.real A + F
      linarith

theorem loss_function_value_bounds {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-(3 / 5)) (3 / 5)))
    (hfd : DifferentiableOn ℝ f (Ioo (-(3 / 5)) (3 / 5)))
    (hf0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo (-(3 / 5)) (3 / 5), 3 / 4 ≤ deriv f x ∧ deriv f x ≤ 5 / 4)
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (0 ≤ u → 3 / 4 * u ≤ f u ∧ f u ≤ 5 / 4 * u) ∧
      (u ≤ 0 → 5 / 4 * u ≤ f u ∧ f u ≤ 3 / 4 * u) := by
  have hz : (0 : ℝ) ∈ Icc (-(3 / 5)) (3 / 5) := by constructor <;> norm_num
  have hu' : u ∈ Icc (-(3 / 5)) (3 / 5) := by
    rcases abs_le.mp hu with ⟨ha, hb⟩
    constructor <;> linarith
  have hfd' : DifferentiableOn ℝ f (interior (Icc (-(3 / 5)) (3 / 5))) := by
    simpa only [interior_Icc] using hfd
  have hlo : ∀ x ∈ interior (Icc (-(3 / 5 : ℝ)) (3 / 5)), 3 / 4 ≤ deriv f x := by
    simpa only [interior_Icc] using fun x hx => (hd x hx).1
  have hhi : ∀ x ∈ interior (Icc (-(3 / 5 : ℝ)) (3 / 5)), deriv f x ≤ 5 / 4 := by
    simpa only [interior_Icc] using fun x hx => (hd x hx).2
  constructor
  · intro h
    have h1 := (convex_Icc (-(3 / 5 : ℝ)) (3 / 5)).mul_sub_le_image_sub_of_le_deriv
      hf hfd' hlo 0 hz u hu' h
    have h2 := (convex_Icc (-(3 / 5 : ℝ)) (3 / 5)).image_sub_le_mul_sub_of_deriv_le
      hf hfd' hhi 0 hz u hu' h
    rw [hf0] at h1 h2
    constructor <;> linarith
  · intro h
    have h1 := (convex_Icc (-(3 / 5 : ℝ)) (3 / 5)).mul_sub_le_image_sub_of_le_deriv
      hf hfd' hlo u hu' 0 hz h
    have h2 := (convex_Icc (-(3 / 5 : ℝ)) (3 / 5)).image_sub_le_mul_sub_of_deriv_le
      hf hfd' hhi u hu' 0 hz h
    rw [hf0] at h1 h2
    constructor <;> linarith

/-- Both inequalities of the original lemma, with an improved explicit error
constant and without the unnecessary small-fourth-moment assumption. -/
theorem one_sided_loss [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (h4 : Integrable (fun x => W x ^ 4) μ)
    (hmean : (∫ x, W x ∂μ) = 0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-(3 / 5)) (3 / 5)))
    (hfd : DifferentiableOn ℝ f (Ioo (-(3 / 5)) (3 / 5)))
    (hf0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo (-(3 / 5)) (3 / 5), 3 / 4 ≤ deriv f x ∧ deriv f x ≤ 5 / 4)
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (3 / 8 * (∫ x, |W x| ∂μ) - 11000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | u < W x} + f u) ∧
    (3 / 8 * (∫ x, |W x| ∂μ) - 11000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | W x < u} - f u) := by
  have hW : Integrable W μ := by
    refine ((integrable_const (1 / 10 : ℝ)).add (h4.const_mul 1000)).mono'
      hWm.aestronglyMeasurable ?_
    filter_upwards [] with x
    exact abs_le_tenth_add_fourth (W x)
  have hv := loss_function_value_bounds hf hfd hf0 hd hu
  constructor
  · exact one_sided_loss_upper_of_value hWm hW h4 hmean hu
      (fun h => (hv.1 h).1) (fun h => (hv.2 h).1)
  · have he : (fun x => (-W x) ^ 4) = (fun x => W x ^ 4) := by funext x; ring
    have h4neg : Integrable (fun x => (-W x) ^ 4) μ := by rw [he]; exact h4
    have hmeanneg : (∫ x, -W x ∂μ) = 0 := by rw [integral_neg, hmean, neg_zero]
    have hu' : |-u| ≤ 1 / 2 := by simpa only [abs_neg] using hu
    have hp := one_sided_loss_upper_of_value hWm.neg hW.neg h4neg hmeanneg
      (F := -f u) hu' (fun h => by have hv' := (hv.2 (by linarith)).2; linarith)
      (fun h => by have hv' := (hv.1 (by linarith)).2; linarith)
    simpa only [he, abs_neg, neg_lt_neg_iff, sub_eq_add_neg] using hp

/-- The exact numerical constant used in the manuscript's appendix follows. -/
theorem effective_one_sided_loss [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (h4 : Integrable (fun x => W x ^ 4) μ)
    (hmean : (∫ x, W x ∂μ) = 0) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-(3 / 5)) (3 / 5)))
    (hfd : DifferentiableOn ℝ f (Ioo (-(3 / 5)) (3 / 5)))
    (hf0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo (-(3 / 5)) (3 / 5), 3 / 4 ≤ deriv f x ∧ deriv f x ≤ 5 / 4)
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (3 / 8 * (∫ x, |W x| ∂μ) - 176000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | u < W x} + f u) ∧
    (3 / 8 * (∫ x, |W x| ∂μ) - 176000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | W x < u} - f u) := by
  rcases one_sided_loss hWm h4 hmean hf hfd hf0 hd hu with ⟨h1, h2⟩
  have hM : 0 ≤ ∫ x, W x ^ 4 ∂μ := integral_nonneg (fun _ => by positivity)
  constructor <;> linarith

end BerryEsseen
