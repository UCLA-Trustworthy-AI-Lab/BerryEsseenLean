import BerryEsseen.ManuscriptSmoothingKernel

/-! The manuscript's numerical tail and first-moment estimates for sinc⁴. -/
noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem manuscript_integral_even (f : ℝ → ℝ) (he : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have hh : (fun x => f |x|) = f := by
    funext x
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx, he]
  rw [← integral_comp_abs, hh]

theorem manuscript_inverse_cube_integral :
    (∫ x : ℝ in Ioi 4, (x ^ 3)⁻¹) = 1 / 32 := by
  calc
    _ = ∫ x : ℝ in Ioi 4, x ^ (-3 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      norm_num [Real.rpow_neg (by linarith [mem_Ioi.mp hx] : (0 : ℝ) ≤ x)]
    _ = 1 / 32 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num)]
      norm_num [Real.rpow_neg (show (0 : ℝ) ≤ 4 by norm_num), Real.rpow_natCast]

theorem manuscript_inverse_fourth_tail_integral :
    (∫ x : ℝ in Ioi 16, (x ^ 4)⁻¹) = 1 / 12288 := by
  calc
    _ = ∫ x : ℝ in Ioi 16, x ^ (-4 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      norm_num [Real.rpow_neg (by linarith [mem_Ioi.mp hx] : (0 : ℝ) ≤ x)]
    _ = 1 / 12288 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) (by norm_num)]
      norm_num [Real.rpow_neg (show (0 : ℝ) ≤ 16 by norm_num), Real.rpow_natCast]

theorem manuscriptSmoothingKernel_tail_sixteen :
    (∫ x in Ioi (16 : ℝ), manuscriptSmoothingKernel x) ≤ 1 / (128 * Real.pi) := by
  calc
    _ ≤ ∫ x : ℝ in Ioi 16, (3 / (8 * Real.pi) * 256) * (x ^ 4)⁻¹ := by
      apply integral_mono_ae (manuscriptSmoothingKernel_integrable.integrableOn)
        ((manuscript_inverse_power_integrable 4 (by norm_num) 16 (by norm_num)).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa [div_eq_mul_inv, mul_assoc] using
        manuscriptSmoothingKernel_le_inverse_fourth x (by linarith [mem_Ioi.mp hx])
    _ = 1 / (128 * Real.pi) := by
      rw [integral_const_mul, manuscript_inverse_fourth_tail_integral]
      ring

theorem manuscriptSmoothingKernel_tail_sixteen_lt :
    (∫ x in Ioi (16 : ℝ), manuscriptSmoothingKernel x) < 1 / 8 := by
  refine (manuscriptSmoothingKernel_tail_sixteen).trans_lt ?_
  rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
  nlinarith [Real.pi_gt_three]

theorem manuscriptSmoothingKernel_first_moment_bound :
    (∫ x : ℝ, |x| * manuscriptSmoothingKernel x) ≤ 12 / Real.pi := by
  let f : ℝ → ℝ := fun x => |x| * manuscriptSmoothingKernel x
  have hf := manuscriptSmoothingKernel_first_moment_integrable
  have hc : (∫ x in Ioc (0 : ℝ) 4, f x) ≤ 8 * (3 / (8 * Real.pi)) := by
    calc
      _ ≤ ∫ x : ℝ in Ioc 0 4, (3 / (8 * Real.pi)) * x := by
        apply integral_mono_ae hf.integrableOn
          ((continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        dsimp [f]
        rw [abs_of_pos hx.1]
        nlinarith [mul_le_mul_of_nonneg_left (manuscriptSmoothingKernel_le_constant x) hx.1.le]
      _ = 8 * (3 / (8 * Real.pi)) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num [integral_id]
        ring
  have ht : (∫ x in Ioi (4 : ℝ), f x) ≤ 8 * (3 / (8 * Real.pi)) := by
    calc
      _ ≤ ∫ x : ℝ in Ioi 4, (3 / (8 * Real.pi) * 256) * (x ^ 3)⁻¹ := by
        apply integral_mono_ae hf.integrableOn
          ((manuscript_inverse_power_integrable 3 (by norm_num) 4 (by norm_num)).const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := by linarith [mem_Ioi.mp hx]
        change |x| * manuscriptSmoothingKernel x ≤
          (3 / (8 * Real.pi) * 256) * (x ^ 3)⁻¹
        rw [abs_of_pos hx0]
        calc
          _ ≤ x * ((3 / (8 * Real.pi)) * (256 / x ^ 4)) :=
            mul_le_mul_of_nonneg_left
              (manuscriptSmoothingKernel_le_inverse_fourth x hx0.ne') hx0.le
          _ = _ := by field_simp
      _ = 8 * (3 / (8 * Real.pi)) := by
        rw [integral_const_mul, manuscript_inverse_cube_integral]
        ring
  have hsplit : (∫ x in Ioi (0 : ℝ), f x) =
      (∫ x in Ioc (0 : ℝ) 4, f x) + ∫ x in Ioi (4 : ℝ), f x := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hf.integrableOn hf.integrableOn,
      Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 4)]
  rw [manuscript_integral_even _ (by intro x; simp [manuscriptSmoothingKernel_even])]
  change 2 * (∫ x in Ioi (0 : ℝ), f x) ≤ 12 / Real.pi
  rw [hsplit]
  calc
    _ ≤ 2 * (8 * (3 / (8 * Real.pi)) + 8 * (3 / (8 * Real.pi))) := by linarith
    _ = 12 / Real.pi := by ring

theorem manuscriptSmoothingKernel_first_moment_lt_four :
    (∫ x : ℝ, |x| * manuscriptSmoothingKernel x) < 4 := by
  refine manuscriptSmoothingKernel_first_moment_bound.trans_lt ?_
  rw [div_lt_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

theorem manuscriptSmoothingKernel_signed_moment_integrable :
    Integrable (fun x : ℝ => x * manuscriptSmoothingKernel x) := by
  apply manuscriptSmoothingKernel_first_moment_integrable.mono'
    (continuous_id.mul manuscriptSmoothingKernel_continuous).measurable.aestronglyMeasurable
  filter_upwards [] with x
  change ‖x * manuscriptSmoothingKernel x‖ ≤ |x| * manuscriptSmoothingKernel x
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (manuscriptSmoothingKernel_nonneg x)]
  exact le_rfl

theorem manuscriptSmoothingKernel_signed_moment_zero :
    (∫ x : ℝ, x * manuscriptSmoothingKernel x) = 0 := by
  have hh := integral_neg_eq_self (fun x : ℝ => x * manuscriptSmoothingKernel x) volume
  simp only [manuscriptSmoothingKernel_even, neg_mul, integral_neg] at hh
  linarith

theorem manuscriptSmoothingKernel_loss_integrable :
    Integrable (fun x : ℝ => max (16 - x) 0 * manuscriptSmoothingKernel x) := by
  apply ((manuscriptSmoothingKernel_integrable.const_mul 16).add
    manuscriptSmoothingKernel_first_moment_integrable).mono'
    ((((continuous_const.sub continuous_id).max continuous_const).mul
      manuscriptSmoothingKernel_continuous).measurable.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖max (16 - x) 0 * manuscriptSmoothingKernel x‖ ≤
    16 * manuscriptSmoothingKernel x + |x| * manuscriptSmoothingKernel x
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (le_max_right _ _) (manuscriptSmoothingKernel_nonneg x))]
  have hb : max (16 - x) 0 ≤ 16 + |x| := by
    exact max_le (by linarith [neg_abs_le x]) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hb (manuscriptSmoothingKernel_nonneg x)]

theorem manuscriptSmoothingKernel_loss_bound :
    (∫ x : ℝ, max (16 - x) 0 * manuscriptSmoothingKernel x) ≤
      16 * (∫ x, manuscriptSmoothingKernel x) + 6 / Real.pi := by
  have habs := manuscriptSmoothingKernel_first_moment_integrable
  have hsgn := manuscriptSmoothingKernel_signed_moment_integrable
  have hdiv : Integrable (fun x : ℝ =>
      (|x| * manuscriptSmoothingKernel x - x * manuscriptSmoothingKernel x) / 2) :=
    (habs.sub hsgn).div_const 2
  have hbase : Integrable (fun x => 16 * manuscriptSmoothingKernel x) :=
    manuscriptSmoothingKernel_integrable.const_mul 16
  have hint : (∫ x : ℝ, max (16 - x) 0 * manuscriptSmoothingKernel x) ≤
      ∫ x : ℝ, 16 * manuscriptSmoothingKernel x +
        (|x| * manuscriptSmoothingKernel x - x * manuscriptSmoothingKernel x) / 2 := by
    apply integral_mono_ae manuscriptSmoothingKernel_loss_integrable (hbase.add hdiv)
    filter_upwards [] with x
    change max (16 - x) 0 * manuscriptSmoothingKernel x ≤
      16 * manuscriptSmoothingKernel x +
        (|x| * manuscriptSmoothingKernel x - x * manuscriptSmoothingKernel x) / 2
    have hb : max (16 - x) 0 ≤ 16 + (|x| - x) / 2 := by
      apply max_le
      · linarith [neg_abs_le x]
      · linarith [le_abs_self x]
    nlinarith [mul_le_mul_of_nonneg_right hb (manuscriptSmoothingKernel_nonneg x)]
  rw [integral_add hbase hdiv, integral_const_mul, integral_div,
    integral_sub habs hsgn, manuscriptSmoothingKernel_signed_moment_zero, sub_zero] at hint
  have hhalf : (∫ x : ℝ, |x| * manuscriptSmoothingKernel x) / 2 ≤ 6 / Real.pi := by
    calc
      _ ≤ (12 / Real.pi) / 2 := div_le_div_of_nonneg_right
        manuscriptSmoothingKernel_first_moment_bound (by norm_num)
      _ = _ := by ring
  linarith [hhalf]

theorem manuscriptSmoothingKernel_loss_symmetry :
    (∫ x : ℝ, max (16 + x) 0 * manuscriptSmoothingKernel x) =
      ∫ x : ℝ, max (16 - x) 0 * manuscriptSmoothingKernel x := by
  have hh := integral_neg_eq_self
    (fun x : ℝ => max (16 - x) 0 * manuscriptSmoothingKernel x) volume
  simpa only [manuscriptSmoothingKernel_even, sub_neg_eq_add] using hh

end BerryEsseen
