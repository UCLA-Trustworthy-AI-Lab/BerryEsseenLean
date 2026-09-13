import BerryEsseen.SmallVarianceSequence
import Mathlib.Probability.ConditionalProbability

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem integrable_id_of_interval (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc a b) : Integrable (fun x : ℝ => x) μ := by
  apply (integrable_const (|a| + |b|)).mono' (by fun_prop)
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b, hx.1, hx.2]

theorem integral_id_mem_interval (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc a b) : (∫ x, x ∂μ) ∈ Icc a b := by
  have hi := integrable_id_of_interval μ a b hb
  have hlo := integral_mono_ae (integrable_const a) hi (hb.mono (fun x hx => hx.1))
  have hhi := integral_mono_ae hi (integrable_const b) (hb.mono (fun x hx => hx.2))
  simpa only [integral_const, probReal_univ, one_smul] using And.intro hlo hhi

theorem centered_interval_noise_exists (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b d : ℝ)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc a b) (hd : 0 < d) :
    ∃ P : CenteredFourthLaw, P.measure = standardizedMeasure μ (∫ x, x ∂μ) d ∧
      ∀ᵐ x ∂P.measure, |x| ≤ (b - a) / d := by
  let m := ∫ x, x ∂μ
  have hm := integral_id_mem_interval μ a b hb
  have hbound : ∀ᵐ y ∂standardizedMeasure μ m d, |y| ≤ (b - a) / d := by
    unfold standardizedMeasure
    apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).2
    filter_upwards [hb] with x hx
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    rw [abs_le]
    constructor <;> dsimp only [m] <;> linarith [hx.1, hx.2, hm.1, hm.2]
  have hmean : (∫ x, x ∂standardizedMeasure μ m d) = 0 :=
    standardizedMeasure_mean μ m d (integrable_id_of_interval μ a b hb) rfl
  exact ⟨CenteredFourthLaw.ofBounded _ ((b - a) / d) hbound hmean, rfl, hbound⟩

theorem conditioned_mixture_identity (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ)
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) (hcomp : μ sᶜ ≠ 0) :
    mixtureMeasure (ProbabilityTheory.cond μ sᶜ) (ProbabilityTheory.cond μ s) (μ.real s) = μ := by
  have hright : ENNReal.ofReal (μ.real s) = μ s := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hleft : ENNReal.ofReal (1 - μ.real s) = μ sᶜ := by
    rw [← probReal_compl_eq_one_sub hs]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  unfold mixtureMeasure
  rw [hleft, hright]
  simp only [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hcomp (measure_ne_top _ _),
    ENNReal.mul_inv_cancel hpos (measure_ne_top _ _), one_smul]
  exact Measure.restrict_compl_add_restrict hs

theorem cond_two_intervals_lower (μ : Measure ℝ) (a b η : ℝ) (hgap : 2 * η < b - a)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (a - η) (a + η) ∪ Icc (b - η) (b + η)) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ (Ioi ((a + b) / 2))ᶜ, x ∈ Icc (a - η) (a + η) := by
  unfold ProbabilityTheory.cond
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioi.compl] with x hx hs
  rcases hx with hx | hx
  · exact hx
  · have hxs : x ≤ (a + b) / 2 := by simpa only [mem_compl_iff, mem_Ioi, not_lt] using hs
    exfalso
    linarith [hx.1]

theorem cond_two_intervals_upper (μ : Measure ℝ) (a b η : ℝ) (hgap : 2 * η < b - a)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (a - η) (a + η) ∪ Icc (b - η) (b + η)) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ (Ioi ((a + b) / 2)), x ∈ Icc (b - η) (b + η) := by
  unfold ProbabilityTheory.cond
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioi] with x hx hs
  rcases hx with hx | hx
  · exfalso
    have hxs : (a + b) / 2 < x := hs
    linarith [hx.2]
  · exact hx

end BerryEsseen
