import BerryEsseen.ManuscriptGeneralDifferenceCoupling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_abs_le_scaled_square (x r : ℝ) (hr : 0 < r) :
    |x| ≤ r + x ^ 2 / r := by
  rw [show r + x ^ 2 / r = (r ^ 2 + x ^ 2) / r by field_simp <;> ring]
  apply (le_div_iff₀ hr).2
  nlinarith [sq_nonneg (|x| - r), sq_abs x]

theorem manuscript_double_coupling_abs_error_integrable (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π) :
    Integrable (fun z => |manuscriptCoupledD z - manuscriptCoupledLimitD z|) (π.prod π) := by
  have hi2 := manuscript_double_coupling_error_integrable π hi
  apply ((integrable_const (1 : ℝ)).add hi2).mono'
    (by unfold manuscriptCoupledD manuscriptCoupledLimitD; fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_abs]
  simpa using manuscript_abs_le_scaled_square (manuscriptCoupledD z - manuscriptCoupledLimitD z) 1 (by norm_num)

theorem manuscript_double_coupling_abs_error_bound (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π) (r : ℝ) (hr : 0 < r) :
    (∫ z, |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂π.prod π) ≤
      r + (∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂π.prod π) / r := by
  have hi2 := manuscript_double_coupling_error_integrable π hi
  have hb := integral_mono (manuscript_double_coupling_abs_error_integrable π hi)
    ((integrable_const r).add (hi2.div_const r))
    (fun z => manuscript_abs_le_scaled_square _ r hr)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const r) (hi2.div_const r), integral_const, integral_div] at hb
  simpa only [probReal_univ, one_smul] using hb

theorem manuscript_double_coupling_limits
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw) (π : ℕ → Measure (ℝ × ℝ))
    (hπ : ∀ j, IsProbabilityMeasure (π j))
    (hf : ∀ j, (π j).map Prod.fst = (P j).measure)
    (hs : ∀ j, (π j).map Prod.snd = Q.measure)
    (hi : ∀ j, Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (π j))
    (hcost : Tendsto (fun j => ∫ z, (z.1 - z.2) ^ 2 ∂π j) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂(π j).prod (π j)) atTop (𝓝 0) ∧
    Tendsto (fun j => ∫ z, |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂(π j).prod (π j)) atTop (𝓝 0) ∧
    Tendsto (fun j => ∫ z, |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2| ∂(π j).prod (π j)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun j => ∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂(π j).prod (π j)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
      (fun j => ?_) (by simpa using hcost.const_mul 4)
    letI := hπ j
    exact manuscript_double_coupling_error_bound (π j) (hi j)
  refine ⟨hsq, ?_, ?_⟩
  · apply Metric.tendsto_nhds.2
    intro ε hε
    let r := ε / 4
    have hr : 0 < r := by dsimp [r]; positivity
    have hh : Tendsto (fun j => (∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂(π j).prod (π j)) / r)
        atTop (𝓝 0) := by simpa only [zero_div] using hsq.div_const r
    filter_upwards [hh.eventually (gt_mem_nhds (by positivity : 0 < ε / 2))] with j hj
    letI := hπ j
    have hb := manuscript_double_coupling_abs_error_bound (π j) (hi j) r hr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
    dsimp [r] at hb hj
    linarith
  · apply Metric.tendsto_nhds.2
    intro ε hε
    let r := ε / 16
    have hr : 0 < r := by dsimp [r]; positivity
    have hh : Tendsto (fun j => (∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂(π j).prod (π j)) / (2 * r))
        atTop (𝓝 0) := by simpa only [zero_div] using hsq.div_const (2 * r)
    filter_upwards [hh.eventually (gt_mem_nhds (by positivity : 0 < ε / 2))] with j hj
    letI := hπ j
    have hb := manuscript_double_coupling_square_difference_bound (P j) Q (π j) (hf j) (hs j) (hi j) r hr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
    dsimp [r] at hb hj
    linarith

/-- Truncation of the fixed integrable factor D² used in the manuscript. -/
def manuscriptSquareTail (μ : Measure ℝ) (A : ℝ) : ℝ :=
  ∫ x, x ^ 2 - min (x ^ 2) A ∂μ

theorem manuscript_square_tail_integrable (μ : Measure ℝ)
    (hi : Integrable (fun x : ℝ => x ^ 2) μ) (A : ℝ) (hA : 0 ≤ A) :
    Integrable (fun x : ℝ => x ^ 2 - min (x ^ 2) A) μ := by
  apply hi.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
  exact sub_le_self _ (le_min (sq_nonneg x) hA)

theorem manuscript_square_tail_tendsto (μ : Measure ℝ)
    (hi : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun N : ℕ => manuscriptSquareTail μ N) atTop (𝓝 0) := by
  have he : Tendsto (fun N : ℕ => ∫ x, x ^ 2 - min (x ^ 2) (N : ℝ) ∂μ)
      atTop (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x : ℝ => x ^ 2)
    · intro N
      exact (show Continuous (fun x : ℝ => x ^ 2 - min (x ^ 2) (N : ℝ)) by fun_prop).measurable.aestronglyMeasurable
    · exact hi
    · intro N
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
      exact sub_le_self _ (le_min (sq_nonneg x) (Nat.cast_nonneg N))
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (x ^ 2))] with N hN
      simp only [min_eq_left hN, sub_self]
  simpa only [integral_zero] using he

end BerryEsseen
