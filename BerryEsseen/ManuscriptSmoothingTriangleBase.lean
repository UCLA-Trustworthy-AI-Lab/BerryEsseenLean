import BerryEsseen.ManuscriptSmoothingKernel
import BerryEsseen.PublishedSmoothing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory Set
namespace BerryEsseen

/-- Density of the sum of two uniforms on [-1/4,1/4]. -/
def manuscriptTriangle (x : ℝ) : ℝ := max (2 - 4 * |x|) 0

theorem manuscriptTriangle_nonneg (x : ℝ) : 0 ≤ manuscriptTriangle x := le_max_right _ _

theorem manuscriptTriangle_continuous : Continuous manuscriptTriangle := by
  unfold manuscriptTriangle
  fun_prop

theorem manuscriptTriangle_even (x : ℝ) : manuscriptTriangle (-x) = manuscriptTriangle x := by
  simp [manuscriptTriangle]

theorem manuscriptTriangle_zero (x : ℝ) (hx : 1 / 2 ≤ |x|) : manuscriptTriangle x = 0 := by
  unfold manuscriptTriangle
  exact max_eq_right (by linarith)

theorem manuscriptTriangle_support : Function.support manuscriptTriangle ⊆ Icc (-(1/2:ℝ)) (1/2) := by
  intro x hx
  by_contra h
  have ha : 1 / 2 ≤ |x| := by
    simp only [mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  exact hx (manuscriptTriangle_zero x ha)

theorem manuscriptTriangle_compact : HasCompactSupport manuscriptTriangle :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc manuscriptTriangle_support

theorem manuscriptTriangle_integrable : Integrable manuscriptTriangle :=
  manuscriptTriangle_continuous.integrable_of_hasCompactSupport manuscriptTriangle_compact

theorem manuscriptTriangle_right (x : ℝ) (hx : x ∈ Icc (0:ℝ) (1/2)) :
    manuscriptTriangle x = 2 - 4*x := by
  rw [manuscriptTriangle, abs_of_nonneg hx.1, max_eq_left (by linarith [hx.2])]

theorem manuscriptTriangle_left (x : ℝ) (hx : x ∈ Icc (-(1/2:ℝ)) 0) :
    manuscriptTriangle x = 2 + 4*x := by
  rw [manuscriptTriangle, abs_of_nonpos hx.2, max_eq_left (by linarith [hx.1])]
  ring

theorem manuscriptTriangle_sq_integral : (∫ x : ℝ, manuscriptTriangle x ^ 2) = 4/3 := by
  have hc : Continuous (fun x : ℝ => manuscriptTriangle x ^ 2) := manuscriptTriangle_continuous.pow 2
  have hs : Function.support (fun x : ℝ => manuscriptTriangle x ^ 2) ⊆
      Icc (-(1/2:ℝ)) (1/2) := by
    intro x hx
    apply manuscriptTriangle_support
    intro hz
    exact hx (by simp [hz])
  have he : (Icc (-(1/2:ℝ)) (1/2)).indicator (fun x : ℝ => manuscriptTriangle x ^ 2) =
      fun x : ℝ => manuscriptTriangle x ^ 2 := by
    exact indicator_eq_self.mpr hs
  have hi : (∫ x in Icc (-(1/2:ℝ)) (1/2), manuscriptTriangle x ^ 2) =
      (∫ x : ℝ, manuscriptTriangle x ^ 2) := by
    rw [← integral_indicator measurableSet_Icc, he]
  rw [← hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have hl : (∫ x : ℝ in -(1/2)..0, manuscriptTriangle x ^ 2) =
      ∫ x : ℝ in -(1/2)..0, (2+4*x)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simpa only using congrArg (fun y : ℝ => y^2) (manuscriptTriangle_left x hx)
  have hr : (∫ x : ℝ in 0..(1/2), manuscriptTriangle x ^ 2) =
      ∫ x : ℝ in 0..(1/2), (2-4*x)^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    simpa only using congrArg (fun y : ℝ => y^2) (manuscriptTriangle_right x hx)
  rw [hl, hr]
  have hp (a b : ℝ) : (∫ x in a..b, (2+4*x)^2) =
      (4*b+8*b^2+(16/3)*b^3) - (4*a+8*a^2+(16/3)*a^3) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      convert (((hasDerivAt_id x).const_mul 4).add
        (((hasDerivAt_id x).pow 2).const_mul 8)).add
        (((hasDerivAt_id x).pow 3).const_mul (16/3)) using 1 <;> simp only [id_eq] <;> ring
    · exact (by fun_prop : Continuous (fun x : ℝ => (2+4*x)^2)).intervalIntegrable _ _
  have hm (a b : ℝ) : (∫ x in a..b, (2-4*x)^2) =
      (4*b-8*b^2+(16/3)*b^3) - (4*a-8*a^2+(16/3)*a^3) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      convert (((hasDerivAt_id x).const_mul 4).sub
        (((hasDerivAt_id x).pow 2).const_mul 8)).add
        (((hasDerivAt_id x).pow 3).const_mul (16/3)) using 1 <;> simp only [id_eq] <;> ring
    · exact (by fun_prop : Continuous (fun x : ℝ => (2-4*x)^2)).intervalIntegrable _ _
  rw [hp, hm]
  norm_num

theorem manuscriptTriangle_integral : (∫ x : ℝ, manuscriptTriangle x) = 1 := by
  have hi : (∫ x in Icc (-(1/2:ℝ)) (1/2), manuscriptTriangle x) =
      ∫ x : ℝ, manuscriptTriangle x := by
    rw [← integral_indicator measurableSet_Icc, indicator_eq_self.mpr manuscriptTriangle_support]
  rw [← hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (manuscriptTriangle_continuous.intervalIntegrable (-(1/2)) 0)
    (manuscriptTriangle_continuous.intervalIntegrable 0 (1/2))]
  have hl : (∫ x : ℝ in -(1/2)..0, manuscriptTriangle x) = ∫ x : ℝ in -(1/2)..0, 2+4*x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact manuscriptTriangle_left x (by simpa [uIcc_of_le (show (-(1/2):ℝ) ≤ 0 by norm_num)] using hx)
  have hr : (∫ x : ℝ in 0..(1/2), manuscriptTriangle x) = ∫ x : ℝ in 0..(1/2), 2-4*x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact manuscriptTriangle_right x (by simpa [uIcc_of_le (show (0:ℝ) ≤ 1/2 by norm_num)] using hx)
  rw [hl, hr, intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous (fun x : ℝ => 4*x)).intervalIntegrable _ _),
    intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous (fun x : ℝ => 4*x)).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul (4:ℝ), intervalIntegral.integral_const_mul (4:ℝ), integral_id, integral_id]
  norm_num

end BerryEsseen
