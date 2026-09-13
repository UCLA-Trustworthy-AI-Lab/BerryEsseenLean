import BerryEsseen.ClusterMoments
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! The manuscript's displayed moment-interpolation chain.  Hölder is applied
with exponents 3/2 and 3 to |x|^(2/3) and |x|^(4/3), before the fourth-moment
budget is substituted.  Both the qualitative and effective cluster consumers
use `absoluteMoment_lower_exact` below, hence pass through the first displayed
lower bound as well as the second. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The actual Hölder interpolation, before any fourth-moment budget is used. -/
theorem CenteredFourthLaw.holder_moment_interpolation (P : CenteredFourthLaw) :
    P.secondMoment ≤ P.absoluteMoment ^ (2 / 3 : ℝ) * P.fourthMoment ^ (1 / 3 : ℝ) := by
  let f : ℝ → ℝ := fun x => |x| ^ (2 / 3 : ℝ)
  let g : ℝ → ℝ := fun x => |x| ^ (4 / 3 : ℝ)
  have hf0 : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg (abs_nonneg x) _
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (abs_nonneg x) _
  have hfp : (fun x => f x ^ (3 / 2 : ℝ)) = (fun x : ℝ => |x|) := by
    funext x
    dsimp only [f]
    rw [← Real.rpow_mul (abs_nonneg x)]
    norm_num
  have hgp : (fun x => g x ^ (3 : ℝ)) = (fun x : ℝ => x ^ 4) := by
    funext x
    dsimp only [g]
    rw [← Real.rpow_mul (abs_nonneg x)]
    norm_num [← abs_pow, abs_of_nonneg (show 0 ≤ x ^ 4 by positivity)]
  have hfg : (fun x => f x * g x) = (fun x : ℝ => x ^ 2) := by
    funext x
    dsimp only [f, g]
    rw [← Real.rpow_add_of_nonneg (abs_nonneg x) (by norm_num) (by norm_num)]
    norm_num [sq_abs]
  have hfLp : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) P.measure := by
    apply (integrable_norm_rpow_iff (show AEStronglyMeasurable f P.measure by dsimp [f]; fun_prop (disch := norm_num))
      (by norm_num) (by finiteness)).mp
    have he : (fun x => ‖f x‖ ^ (ENNReal.ofReal (3 / 2 : ℝ)).toReal) =
        (fun x => f x ^ (3 / 2 : ℝ)) := by
      funext x
      rw [ENNReal.toReal_ofReal (by norm_num), Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    rw [he, hfp]
    exact P.first_integrable.abs
  have hgLp : MemLp g (ENNReal.ofReal (3 : ℝ)) P.measure := by
    apply (integrable_norm_rpow_iff (show AEStronglyMeasurable g P.measure by dsimp [g]; fun_prop (disch := norm_num))
      (by norm_num) (by finiteness)).mp
    have he : (fun x => ‖g x‖ ^ (ENNReal.ofReal (3 : ℝ)).toReal) =
        (fun x => g x ^ (3 : ℝ)) := by
      funext x
      rw [ENNReal.toReal_ofReal (by norm_num), Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    rw [he, hgp]
    exact P.fourth_integrable
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    apply Real.holderConjugate_iff.mpr
    norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hfLp hgLp
  rw [hfg, hfp, hgp] at h
  norm_num only [one_div_div] at h
  exact h

/-- Positive second moment forces a positive fourth moment in the same Hölder
estimate, so the first displayed denominator is genuinely nonzero. -/
theorem CenteredFourthLaw.fourthMoment_pos_of_secondMoment_pos (P : CenteredFourthLaw)
    (ht : 0 < P.secondMoment) : 0 < P.fourthMoment := by
  have hnonneg : 0 ≤ P.fourthMoment := integral_nonneg (fun x => by positivity)
  by_contra hnot
  have hz : P.fourthMoment = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have h := P.holder_moment_interpolation
  rw [hz, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0), mul_zero] at h
  exact (not_le_of_gt ht) h

/-- The manuscript's first displayed bound E|W| ≥ t^(3/2)/sqrt(E W^4),
obtained by raising the actual Hölder inequality to the power 3/2. -/
theorem CenteredFourthLaw.absoluteMoment_lower_holder (P : CenteredFourthLaw)
    (ht : 0 < P.secondMoment) :
    P.secondMoment ^ (3 / 2 : ℝ) / Real.sqrt P.fourthMoment ≤ P.absoluteMoment := by
  have hA : 0 ≤ P.absoluteMoment := integral_nonneg (fun x => abs_nonneg x)
  have hM : 0 < P.fourthMoment := P.fourthMoment_pos_of_secondMoment_pos ht
  have h := Real.rpow_le_rpow ht.le P.holder_moment_interpolation (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hM.le _),
    ← Real.rpow_mul hA, ← Real.rpow_mul hM.le] at h
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num,
    show (1 / 3 : ℝ) * (3 / 2) = 1 / 2 by norm_num, Real.rpow_one] at h
  rw [← Real.sqrt_eq_rpow] at h
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hM)).mpr h

/-- Both inequalities in the displayed interpolation chain, in their original
order of derivation: Hölder first, then the fourth-moment bound. -/
theorem CenteredFourthLaw.absoluteMoment_interpolation_chain (P : CenteredFourthLaw) (ε : ℝ)
    (ht : 0 < P.secondMoment)
    (hfour : P.fourthMoment ≤ 3 * P.secondMoment ^ 2 + ε ^ 2 * P.secondMoment) :
    P.secondMoment ^ (3 / 2 : ℝ) / Real.sqrt P.fourthMoment ≤ P.absoluteMoment ∧
      P.secondMoment / Real.sqrt (3 * P.secondMoment + ε ^ 2) ≤
        P.secondMoment ^ (3 / 2 : ℝ) / Real.sqrt P.fourthMoment := by
  have hfirst := P.absoluteMoment_lower_holder ht
  have hM : 0 < P.fourthMoment := P.fourthMoment_pos_of_secondMoment_pos ht
  have hC : 0 < 3 * P.secondMoment + ε ^ 2 := by positivity
  have hroot : Real.sqrt P.fourthMoment ≤
      Real.sqrt P.secondMoment * Real.sqrt (3 * P.secondMoment + ε ^ 2) := by
    rw [← Real.sqrt_mul ht.le]
    apply Real.sqrt_le_sqrt
    nlinarith only [hfour]
  have hpower : P.secondMoment ^ (3 / 2 : ℝ) =
      P.secondMoment * Real.sqrt P.secondMoment := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  refine ⟨hfirst, ?_⟩
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hC) (Real.sqrt_pos.mpr hM)).mpr
  rw [hpower]
  have hscaled := mul_le_mul_of_nonneg_left hroot ht.le
  simpa only [mul_assoc] using hscaled

/-- The existing consumer now passes through both manuscript display steps. -/
theorem CenteredFourthLaw.absoluteMoment_lower_exact (P : CenteredFourthLaw) (ε : ℝ)
    (ht : 0 < P.secondMoment)
    (hfour : P.fourthMoment ≤ 3 * P.secondMoment ^ 2 + ε ^ 2 * P.secondMoment) :
    P.secondMoment / Real.sqrt (3 * P.secondMoment + ε ^ 2) ≤ P.absoluteMoment := by
  obtain ⟨hfirst, hsecond⟩ := P.absoluteMoment_interpolation_chain ε ht hfour
  exact hsecond.trans hfirst

theorem CenteredFourthLaw.measure_eq_dirac_of_second_zero (P : CenteredFourthLaw)
    (h : P.secondMoment = 0) : P.measure = Measure.dirac 0 := by
  have hz : (fun x : ℝ => x ^ 2) =ᵐ[P.measure] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun x : ℝ => sq_nonneg x))
      (P.integrable_pow 2 (by omega))).1 h
  have hx : (fun x : ℝ => x) =ᵐ[P.measure] (fun _ => 0) := by
    filter_upwards [hz] with x hx
    change x ^ 2 = 0 at hx
    exact eq_zero_of_pow_eq_zero hx
  calc
    P.measure = P.measure.map (fun x : ℝ => x) := Measure.map_id.symm
    _ = P.measure.map (fun _ : ℝ => (0 : ℝ)) := Measure.map_congr hx
    _ = Measure.dirac 0 := by simp

end BerryEsseen
