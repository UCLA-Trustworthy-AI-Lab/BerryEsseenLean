import BerryEsseen.OneSidedLoss

/-! Lemma 3.2 following the manuscript's bounded-variable, clipping,
recentering and reflection proof, with the appendix's exact constants.
The direct fourth-moment one-sided-loss theorem is not used. -/
noncomputable section
open MeasureTheory Set
namespace BerryEsseen

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem manuscript_bounded_one_sided_loss [IsProbabilityMeasure μ] {V : Ω → ℝ}
    (hVm : Measurable V) (hbnd : ∀ᵐ x ∂μ, |V x| ≤ 1 / 10)
    (hmean : (∫ x, V x ∂μ) = 0) {u F : ℝ} (hu : |u| ≤ 11 / 20)
    (hFpos : 0 ≤ u → 3 / 4 * u ≤ F)
    (hFneg : u ≤ 0 → 5 / 4 * u ≤ F) :
    3 / 8 * (∫ x, |V x| ∂μ) ≤ μ.real {x | u < V x} + F := by
  have hV : Integrable V μ := (integrable_const (1 / 10 : ℝ)).mono'
    hVm.aestronglyMeasurable hbnd
  let A := {x | u < V x}
  let b : Ω → ℝ := A.indicator (fun _ => 1)
  have hA : MeasurableSet A := measurableSet_lt measurable_const hVm
  have hb : Integrable b μ := (integrable_const 1).indicator hA
  have hbeq : (∫ x, b x ∂μ) = μ.real A := integral_indicator_one hA
  have ht : 0 ≤ μ.real A := ENNReal.toReal_nonneg
  have hp : Integrable (fun x => max (V x) 0) μ := by
    apply hV.abs.mono' (hVm.max measurable_const).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hhalf := integral_positive_part_of_centered hV hmean
  by_cases hupos : 0 ≤ u
  · have hi := integral_mono_ae hp ((integrable_const u).add (hb.const_mul (1 / 10)))
      (by
        filter_upwards [hbnd] with x hx
        dsimp [b, A]
        rw [indicator_apply]
        by_cases h : u < V x
        · simp only [Set.mem_setOf_eq, h, ↓reduceIte, mul_one]
          exact (max_le (le_trans (le_abs_self _) hx) (by norm_num)).trans (by linarith)
        · simp only [Set.mem_setOf_eq, h, ↓reduceIte, mul_zero, add_zero]
          exact max_le (le_of_not_gt h) hupos)
    simp only [Pi.add_apply] at hi
    rw [integral_add (integrable_const u) (hb.const_mul (1 / 10)),
      integral_const, integral_const_mul, hbeq, hhalf] at hi
    simp only [probReal_univ, smul_eq_mul, one_mul] at hi
    have hf := hFpos hupos
    change _ ≤ μ.real A + F
    linarith
  · have huneg : u ≤ 0 := le_of_not_ge hupos
    have hf := hFneg huneg
    by_cases hur : -u ≤ 1 / 10
    · have hi := integral_mono_ae hV ((hb.const_mul (1 / 10 - u)).add (integrable_const u))
        (by
          filter_upwards [hbnd] with x hx
          dsimp [b, A]
          rw [indicator_apply]
          by_cases h : u < V x
          · simp only [Set.mem_setOf_eq, h, ↓reduceIte, mul_one]
            linarith [le_abs_self (V x)]
          · simp only [Set.mem_setOf_eq, h, ↓reduceIte, mul_zero, zero_add]
            exact le_of_not_gt h)
      have hj := integral_mono_ae hp (hb.const_mul (1 / 10))
        (by
          filter_upwards [hbnd] with x hx
          dsimp [b, A]
          rw [indicator_apply]
          by_cases h : u < V x
          · simp only [Set.mem_setOf_eq, h, ↓reduceIte, mul_one]
            exact max_le (le_trans (le_abs_self _) hx) (by norm_num)
          · simp only [Set.mem_setOf_eq, h, ↓reduceIte, mul_zero]
            exact max_le (le_trans (le_of_not_gt h) huneg) le_rfl)
      simp only [Pi.add_apply] at hi
      rw [integral_add (hb.const_mul (1 / 10 - u)) (integrable_const u)] at hi
      simp only [integral_const_mul, integral_const, hbeq, hmean, hhalf,
        probReal_univ, smul_eq_mul, one_mul] at hi hj
      have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 10 + u) ht
      change _ ≤ μ.real A + F
      nlinarith
    · have hall : b =ᵐ[μ] fun _ => 1 := by
        filter_upwards [hbnd] with x hx
        have h : u < V x := by linarith [(abs_le.mp hx).1]
        simp [b, A, h]
      have htone : μ.real A = 1 := by
        rw [← hbeq, integral_congr_ae hall]
        simp
      have hsmall := integral_mono_ae hV.abs (integrable_const (1 / 10 : ℝ)) hbnd
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsmall
      change _ ≤ μ.real A + F
      rw [htone]
      linarith [(abs_le.mp hu).1]

def manuscriptClip (w : ℝ) : ℝ := max (-(1 / 20)) (min w (1 / 20))

theorem manuscriptClip_abs (w : ℝ) : |manuscriptClip w| ≤ 1 / 20 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem manuscriptClip_eq_self {w : ℝ} (hw : |w| ≤ 1 / 20) : manuscriptClip w = w := by
  rcases abs_le.mp hw with ⟨hlo, hhi⟩
  rw [manuscriptClip, min_eq_left hhi, max_eq_right hlo]

theorem manuscriptClip_abs_sub_le (w : ℝ) : |w - manuscriptClip w| ≤ |w| := by
  by_cases hlo : w ≤ -(1 / 20)
  · rw [manuscriptClip, min_eq_left (by linarith : w ≤ 1 / 20), max_eq_left hlo,
      abs_of_nonpos (by linarith : w - -(1 / 20) ≤ 0), abs_of_nonpos (by linarith : w ≤ 0)]
    linarith
  · by_cases hhi : 1 / 20 ≤ w
    · rw [manuscriptClip, min_eq_right hhi, max_eq_right (by norm_num : -(1 / 20 : ℝ) ≤ 1 / 20),
        abs_of_nonneg (by linarith : 0 ≤ w - 1 / 20), abs_of_nonneg (by linarith : 0 ≤ w)]
      linarith
    · rw [manuscriptClip_eq_self (by rw [abs_le]; constructor <;> linarith), sub_self, abs_zero]
      exact abs_nonneg _

theorem manuscript_tail_abs_fourth {w : ℝ} (hw : 1 / 20 ≤ |w|) :
    |w| ≤ 8000 * w ^ 4 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 20) hw 3
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg w)
  have he : |w| ^ 4 = w ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hm' : |w| / 8000 ≤ |w| ^ 4 := by nlinarith only [hm]
  rw [he] at hm'
  linarith

theorem manuscriptClip_error_fourth (w : ℝ) : |w - manuscriptClip w| ≤ 8000 * w ^ 4 := by
  by_cases hw : |w| ≤ 1 / 20
  · rw [manuscriptClip_eq_self hw, sub_self, abs_zero]
    positivity
  · exact (manuscriptClip_abs_sub_le w).trans (manuscript_tail_abs_fourth (le_of_not_ge hw))

theorem manuscriptClip_changed_fourth (w : ℝ) :
    (if manuscriptClip w ≠ w then (1 : ℝ) else 0) ≤ 160000 * w ^ 4 := by
  by_cases hw : manuscriptClip w = w
  · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte]
    positivity
  · simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte]
    have hab : 1 / 20 ≤ |w| := by
      by_contra h
      exact hw (manuscriptClip_eq_self (le_of_lt (lt_of_not_ge h)))
    have h := manuscript_tail_abs_fourth hab
    linarith


theorem manuscript_integrable_of_fourth [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (h4 : Integrable (fun x => W x ^ 4) μ) : Integrable W μ := by
  apply ((integrable_const (1 / 20 : ℝ)).add (h4.const_mul 8000)).mono'
    hWm.aestronglyMeasurable
  filter_upwards [] with x
  have h := abs_add_le (W x - manuscriptClip (W x)) (manuscriptClip (W x))
  rw [sub_add_cancel] at h
  exact h.trans (by
    change _ ≤ 1 / 20 + 8000 * W x ^ 4
    linarith [manuscriptClip_abs (W x), manuscriptClip_error_fourth (W x)])

theorem manuscriptClip_measurable {W : Ω → ℝ} (hWm : Measurable W) :
    Measurable (fun x => manuscriptClip (W x)) :=
  measurable_const.max (hWm.min measurable_const)

theorem manuscriptClip_integrable [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) : Integrable (fun x => manuscriptClip (W x)) μ := by
  apply (integrable_const (1 / 20 : ℝ)).mono' (manuscriptClip_measurable hWm).aestronglyMeasurable
  filter_upwards [] with x
  exact manuscriptClip_abs (W x)

theorem manuscriptClip_budgets [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (h4 : Integrable (fun x => W x ^ 4) μ)
    (hmean : (∫ x, W x ∂μ) = 0) :
    |∫ x, manuscriptClip (W x) ∂μ| ≤ 8000 * (∫ x, W x ^ 4 ∂μ) ∧
    μ.real {x | manuscriptClip (W x) ≠ W x} ≤ 160000 * (∫ x, W x ^ 4 ∂μ) ∧
    (∫ x, |W x| ∂μ) - 16000 * (∫ x, W x ^ 4 ∂μ) ≤
      ∫ x, |manuscriptClip (W x) - (∫ y, manuscriptClip (W y) ∂μ)| ∂μ := by
  let T : Ω → ℝ := fun x => manuscriptClip (W x)
  let m : ℝ := ∫ x, T x ∂μ
  have hW := manuscript_integrable_of_fourth hWm h4
  have hT : Integrable T μ := manuscriptClip_integrable hWm
  have hTm : Measurable T := manuscriptClip_measurable hWm
  have herr := integral_mono (hW.sub hT).abs (h4.const_mul 8000)
    (fun x => manuscriptClip_error_fourth (W x))
  rw [integral_const_mul] at herr
  change (∫ x, |W x - T x| ∂μ) ≤ 8000 * (∫ x, W x ^ 4 ∂μ) at herr
  have hm : |m| ≤ 8000 * (∫ x, W x ^ 4 ∂μ) := by
    have hi := abs_integral_le_integral_abs (f := fun x => W x - T x) (μ := μ)
    rw [integral_sub hW hT, hmean, zero_sub, abs_neg] at hi
    exact hi.trans herr
  refine ⟨hm, ?_, ?_⟩
  · let A := {x | T x ≠ W x}
    have hA : MeasurableSet A := (measurableSet_eq_fun hTm hWm).compl
    have hi := integral_mono ((integrable_const (1 : ℝ)).indicator hA) (h4.const_mul 160000)
      (fun x => by simpa only [A, T, indicator_apply, Set.mem_setOf_eq] using manuscriptClip_changed_fourth (W x))
    have hbi : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real A := integral_indicator_one hA
    rw [hbi, integral_const_mul] at hi
    exact hi
  · have hV : Integrable (fun x => T x - m) μ := hT.sub (integrable_const m)
    have hi := integral_mono hW.abs (((hW.sub hT).abs.add hV.abs).add (integrable_const |m|))
      (fun x => by
        have ha := abs_add_le (W x - T x) (T x - m)
        have hb := abs_add_le ((W x - T x) + (T x - m)) m
        have he : (W x - T x) + (T x - m) + m = W x := by ring
        rw [he] at hb
        change |W x| ≤ |W x - T x| + |T x - m| + |m|
        linarith)
    change (∫ x, |W x| ∂μ) ≤ ∫ x, |W x - T x| + |T x - m| + |m| ∂μ at hi
    have herror : Integrable (fun x => |W x - T x|) μ := (hW.sub hT).abs
    have hsum : Integrable (fun x => |W x - T x| + |T x - m|) μ := herror.add hV.abs
    rw [integral_add hsum (integrable_const |m|),
      integral_add herror hV.abs, integral_const] at hi
    simp only [probReal_univ, smul_eq_mul, one_mul] at hi
    change _ ≤ ∫ x, |T x - m| ∂μ
    linarith

theorem manuscript_strict_event_transfer [IsProbabilityMeasure μ] {W T : Ω → ℝ}
    (hWm : Measurable W) (hTm : Measurable T) (u m : ℝ) :
    μ.real {x | u - m < T x - m} ≤
      μ.real {x | u < W x} + μ.real {x | T x ≠ W x} := by
  have hA : MeasurableSet {x | u < T x} := measurableSet_lt measurable_const hTm
  have hB : MeasurableSet {x | u < W x} := measurableSet_lt measurable_const hWm
  have hC : MeasurableSet {x | T x ≠ W x} := (measurableSet_eq_fun hTm hWm).compl
  have hi := integral_mono (μ := μ) ((integrable_const (1 : ℝ)).indicator hA)
    (((integrable_const (1 : ℝ)).indicator hB).add ((integrable_const (1 : ℝ)).indicator hC))
    (fun x => by
      simp only [Pi.add_apply, indicator_apply, Set.mem_setOf_eq]
      by_cases he : T x = W x
      · simp [he]
      · simp only [he, ne_eq, not_false_eq_true, ↓reduceIte]
        split_ifs <;> norm_num)
  simp only [Pi.add_apply] at hi
  have heA : (∫ x, {x | u < T x}.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real {x | u < T x} := integral_indicator_one hA
  have heB : (∫ x, {x | u < W x}.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real {x | u < W x} := integral_indicator_one hB
  have heC : (∫ x, {x | T x ≠ W x}.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real {x | T x ≠ W x} := integral_indicator_one hC
  rw [integral_add ((integrable_const (1 : ℝ)).indicator hB) ((integrable_const (1 : ℝ)).indicator hC),
    heA, heB, heC] at hi
  simpa only [sub_lt_sub_iff_right] using hi


theorem manuscript_loss_function_controls {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-(3 / 5)) (3 / 5)))
    (hfd : DifferentiableOn ℝ f (Ioo (-(3 / 5)) (3 / 5)))
    (hf0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo (-(3 / 5)) (3 / 5), 3 / 4 ≤ deriv f x ∧ deriv f x ≤ 5 / 4) :
    (∀ u : ℝ, |u| ≤ 11 / 20 →
      (0 ≤ u → 3 / 4 * u ≤ f u ∧ f u ≤ 5 / 4 * u) ∧
      (u ≤ 0 → 5 / 4 * u ≤ f u ∧ f u ≤ 3 / 4 * u)) ∧
    (∀ u v : ℝ, |u| ≤ 11 / 20 → |v| ≤ 11 / 20 →
      |f u - f v| ≤ 5 / 4 * |u - v|) := by
  have hin (u : ℝ) (hu : |u| ≤ 11 / 20) : u ∈ Icc (-(3 / 5)) (3 / 5) := by
    rcases abs_le.mp hu with ⟨ha, hb⟩
    constructor <;> linarith
  have hfd' : DifferentiableOn ℝ f (interior (Icc (-(3 / 5)) (3 / 5))) := by
    simpa only [interior_Icc] using hfd
  have hlo : ∀ x ∈ interior (Icc (-(3 / 5 : ℝ)) (3 / 5)), 3 / 4 ≤ deriv f x := by
    simpa only [interior_Icc] using fun x hx => (hd x hx).1
  have hhi : ∀ x ∈ interior (Icc (-(3 / 5 : ℝ)) (3 / 5)), deriv f x ≤ 5 / 4 := by
    simpa only [interior_Icc] using fun x hx => (hd x hx).2
  have hdiff (u v : ℝ) (hu : |u| ≤ 11 / 20) (hv : |v| ≤ 11 / 20) (huv : u ≤ v) :
      3 / 4 * (v - u) ≤ f v - f u ∧ f v - f u ≤ 5 / 4 * (v - u) := by
    exact ⟨(convex_Icc (-(3 / 5 : ℝ)) (3 / 5)).mul_sub_le_image_sub_of_le_deriv
        hf hfd' hlo u (hin u hu) v (hin v hv) huv,
      (convex_Icc (-(3 / 5 : ℝ)) (3 / 5)).image_sub_le_mul_sub_of_deriv_le
        hf hfd' hhi u (hin u hu) v (hin v hv) huv⟩
  constructor
  · intro u hu
    constructor
    · intro hup
      have hh := hdiff 0 u (by norm_num) hu hup
      rw [hf0] at hh
      constructor <;> linarith [hh.1, hh.2]
    · intro hun
      have hh := hdiff u 0 hu (by norm_num) hun
      rw [hf0] at hh
      constructor <;> linarith [hh.1, hh.2]
  · intro u v hu hv
    rcases le_total u v with huv | hvu
    · have hh := hdiff u v hu hv huv
      rw [abs_of_nonpos (by linarith [hh.1] : f u - f v ≤ 0),
        abs_of_nonpos (by linarith : u - v ≤ 0)]
      linarith [hh.2]
    · have hh := hdiff v u hv hu hvu
      rw [abs_of_nonneg (by linarith [hh.1] : 0 ≤ f u - f v),
        abs_of_nonneg (by linarith : 0 ≤ u - v)]
      exact hh.2

theorem manuscript_one_sided_loss_upper_of_controls [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (h4 : Integrable (fun x => W x ^ 4) μ)
    (hmean : (∫ x, W x ∂μ) = 0)
    (hsmall : (∫ x, W x ^ 4 ∂μ) ≤ 1 / 160000) {f : ℝ → ℝ}
    (hvalue : ∀ u : ℝ, |u| ≤ 11 / 20 →
      (0 ≤ u → 3 / 4 * u ≤ f u ∧ f u ≤ 5 / 4 * u) ∧
      (u ≤ 0 → 5 / 4 * u ≤ f u ∧ f u ≤ 3 / 4 * u))
    (hlip : ∀ u v : ℝ, |u| ≤ 11 / 20 → |v| ≤ 11 / 20 →
      |f u - f v| ≤ 5 / 4 * |u - v|)
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    3 / 8 * (∫ x, |W x| ∂μ) - 176000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | u < W x} + f u := by
  let T : Ω → ℝ := fun x => manuscriptClip (W x)
  let m : ℝ := ∫ x, T x ∂μ
  let V : Ω → ℝ := fun x => T x - m
  have hTm : Measurable T := manuscriptClip_measurable hWm
  have hT : Integrable T μ := manuscriptClip_integrable hWm
  obtain ⟨hme, htail, hmoment⟩ := manuscriptClip_budgets hWm h4 hmean
  change |m| ≤ _ at hme
  have hm : |m| ≤ 1 / 20 := by linarith
  have hVm : Measurable V := hTm.sub measurable_const
  have hVmean : (∫ x, V x ∂μ) = 0 := by
    change (∫ x, T x - m ∂μ) = 0
    rw [integral_sub hT (integrable_const m), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    exact sub_self m
  have hVbound : ∀ᵐ x ∂μ, |V x| ≤ 1 / 10 := by
    filter_upwards [] with x
    have hh : |T x - m| ≤ |T x| + |m| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (T x) (-m)
    have ht : |T x| ≤ 1 / 20 := manuscriptClip_abs (W x)
    change |T x - m| ≤ 1 / 10
    linarith
  have hum : |u - m| ≤ 11 / 20 := by
    have hh : |u - m| ≤ |u| + |m| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u (-m)
    linarith
  have hv := hvalue (u - m) hum
  have hbounded := manuscript_bounded_one_sided_loss hVm hVbound hVmean hum
    (fun h => (hv.1 h).1) (fun h => (hv.2 h).1)
  have hprob := manuscript_strict_event_transfer (μ := μ) hWm hTm u m
  have hfu := hlip u (u - m) (by linarith) hum
  rw [show u - (u - m) = m by ring] at hfu
  change _ ≤ ∫ x, |V x| ∂μ at hmoment
  change _ ≤ μ.real {x | u - m < T x - m} + f (u - m) at hbounded
  have hflo := (abs_le.mp hfu).1
  change μ.real {x | T x ≠ W x} ≤ _ at htail
  linarith

/-- The manuscript's clipping-and-recentering proof of both strict-event
inequalities, with precisely c₀=3/8, C=176000, κ=1/160000. -/
theorem manuscript_one_sided_loss [IsProbabilityMeasure μ] {W : Ω → ℝ}
    (hWm : Measurable W) (h4 : Integrable (fun x => W x ^ 4) μ)
    (hmean : (∫ x, W x ∂μ) = 0)
    (hsmall : (∫ x, W x ^ 4 ∂μ) ≤ 1 / 160000) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-(3 / 5)) (3 / 5)))
    (hfd : DifferentiableOn ℝ f (Ioo (-(3 / 5)) (3 / 5)))
    (hf0 : f 0 = 0)
    (hd : ∀ x ∈ Ioo (-(3 / 5)) (3 / 5), 3 / 4 ≤ deriv f x ∧ deriv f x ≤ 5 / 4)
    {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (3 / 8 * (∫ x, |W x| ∂μ) - 176000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | u < W x} + f u) ∧
    (3 / 8 * (∫ x, |W x| ∂μ) - 176000 * (∫ x, W x ^ 4 ∂μ) ≤
      μ.real {x | W x < u} - f u) := by
  obtain ⟨hvalue, hlip⟩ := manuscript_loss_function_controls hf hfd hf0 hd
  constructor
  · exact manuscript_one_sided_loss_upper_of_controls hWm h4 hmean hsmall hvalue hlip hu
  · let g : ℝ → ℝ := fun x => -f (-x)
    have hgvalue : ∀ x : ℝ, |x| ≤ 11 / 20 →
      (0 ≤ x → 3 / 4 * x ≤ g x ∧ g x ≤ 5 / 4 * x) ∧
      (x ≤ 0 → 5 / 4 * x ≤ g x ∧ g x ≤ 3 / 4 * x) := by
      intro x hx
      have hv := hvalue (-x) (by simpa only [abs_neg] using hx)
      constructor
      · intro hp
        obtain ⟨ha, hb⟩ := hv.2 (by linarith)
        dsimp [g]
        constructor <;> linarith
      · intro hn
        obtain ⟨ha, hb⟩ := hv.1 (by linarith)
        dsimp [g]
        constructor <;> linarith
    have hglip : ∀ x y : ℝ, |x| ≤ 11 / 20 → |y| ≤ 11 / 20 →
        |g x - g y| ≤ 5 / 4 * |x - y| := by
      intro x y hx hy
      have hh := hlip (-x) (-y) (by simpa only [abs_neg] using hx) (by simpa only [abs_neg] using hy)
      simpa only [g, neg_sub_neg, abs_sub_comm] using hh
    have he : (fun x => (-W x) ^ 4) = (fun x => W x ^ 4) := by funext x; ring
    have h4neg : Integrable (fun x => (-W x) ^ 4) μ := by rw [he]; exact h4
    have hmneg : (∫ x, -W x ∂μ) = 0 := by rw [integral_neg, hmean, neg_zero]
    have hsneg : (∫ x, (-W x) ^ 4 ∂μ) ≤ 1 / 160000 := by rw [he]; exact hsmall
    have hh := manuscript_one_sided_loss_upper_of_controls hWm.neg h4neg hmneg hsneg
      hgvalue hglip (u := -u) (by simpa only [abs_neg] using hu)
    simpa only [he, abs_neg, neg_lt_neg_iff, g, neg_neg, sub_eq_add_neg] using hh

end BerryEsseen
