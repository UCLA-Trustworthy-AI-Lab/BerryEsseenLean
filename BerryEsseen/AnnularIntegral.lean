import BerryEsseen.EffectiveGaussianTail
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem integrable_comp_abs_of_integrable (f : ℝ → ℝ) (hf : Integrable f) :
    Integrable (fun t => f |t|) := by
  have hr : IntegrableOn (fun t => f |t|) (Ioi 0) := by
    apply hf.integrableOn.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hl : IntegrableOn (fun t => f |t|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hr
  have h := integrableOn_union.mpr ⟨hl, hr⟩
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

def annularInverse (a L t : ℝ) : ℝ := (Icc a L).indicator (fun x : ℝ => x⁻¹) |t|

theorem annularInverse_nonneg (a L t : ℝ) : 0 ≤ annularInverse a L t := by
  unfold annularInverse
  by_cases ht : |t| ∈ Icc a L
  · rw [indicator_of_mem ht]
    positivity
  · rw [indicator_of_notMem ht]

theorem inverse_interval_integrable (a L : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x⁻¹) (Icc a L) := by
  have hc : IntegrableOn (fun _ : ℝ => a⁻¹) (Icc a L) := integrableOn_const isCompact_Icc.measure_lt_top.ne
  apply hc.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos (ha.trans_le hx.1)]
  simpa only [one_div] using one_div_le_one_div_of_le ha hx.1

theorem annularInverse_integrable (a L : ℝ) (ha : 0 < a) : Integrable (annularInverse a L) :=
  integrable_comp_abs_of_integrable _ ((inverse_interval_integrable a L ha).integrable_indicator measurableSet_Icc)

theorem annularInverse_integral (a L : ℝ) (ha : 0 < a) (haL : a ≤ L) :
    (∫ t, annularInverse a L t) = 2 * Real.log (L / a) := by
  unfold annularInverse
  rw [integral_comp_abs, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  rw [show Icc a L ∩ Ioi 0 = Icc a L from inter_eq_left.mpr (fun t ht => ha.trans_le ht.1)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haL,
    integral_inv (by rw [uIcc_of_le haL]; simp only [mem_Icc, not_and]; intro h; linarith)]

theorem charFun_power_bound_of_log_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hgap : ‖charFun μ u‖ ≤ 1 - Real.log (n : ℝ) / (n : ℝ)) :
    ‖charFun μ u ^ n‖ ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : ‖charFun μ u‖ ≤ Real.exp (-Real.log (n : ℝ) / (n : ℝ)) := by
    apply hgap.trans
    convert Real.add_one_le_exp (-Real.log (n : ℝ) / (n : ℝ)) using 1 <;> ring
  have hp := pow_le_pow_left₀ (norm_nonneg (charFun μ u)) he n
  rw [← Real.exp_nat_mul] at hp
  have hex : (n : ℝ) * (-Real.log (n : ℝ) / (n : ℝ)) = -Real.log (n : ℝ) := by field_simp
  rw [hex, Real.exp_neg, Real.exp_log hn0] at hp
  simpa only [norm_pow, one_div] using hp

end BerryEsseen
