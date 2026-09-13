import BerryEsseen.ManuscriptGeneralCurvatureCoupling
import Mathlib.Topology.MetricSpace.UniformConvergence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_square_coupled_fst (P : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (hf : π.map Prod.fst = P.measure) (u : ℝ) :
    characteristicSquare P u = ∫ z, Real.cos (u * manuscriptCoupledD z) ∂π.prod π := by
  change ‖charFun P.measure u‖ ^ 2 = _
  rw [← manuscriptDifferenceLaw_cos, ← manuscript_double_coupling_fst π P.measure hf,
    integral_map (by unfold manuscriptCoupledD; fun_prop) (by fun_prop)]

theorem manuscript_square_coupled_snd (P : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (hs : π.map Prod.snd = P.measure) (u : ℝ) :
    characteristicSquare P u = ∫ z, Real.cos (u * manuscriptCoupledLimitD z) ∂π.prod π := by
  change ‖charFun P.measure u‖ ^ 2 = _
  rw [← manuscriptDifferenceLaw_cos, ← manuscript_double_coupling_snd π P.measure hs,
    integral_map (by unfold manuscriptCoupledLimitD; fun_prop) (by fun_prop)]

theorem manuscript_square_coupling_bound (P Q : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hf : π.map Prod.fst = P.measure) (hs : π.map Prod.snd = Q.measure)
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π)
    (T u : ℝ) (hu : |u| ≤ T) :
    |characteristicSquare P u - characteristicSquare Q u| ≤
      T * (∫ z, |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂π.prod π) := by
  have hfi : Integrable (fun z => Real.cos (u * manuscriptCoupledD z)) (π.prod π) := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold manuscriptCoupledD; fun_prop)
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u * manuscriptCoupledD z)
  have hsi : Integrable (fun z => Real.cos (u * manuscriptCoupledLimitD z)) (π.prod π) := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold manuscriptCoupledLimitD; fun_prop)
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u * manuscriptCoupledLimitD z)
  have hab := manuscript_double_coupling_abs_error_integrable π hi
  rw [manuscript_square_coupled_fst P π hf, manuscript_square_coupled_snd Q π hs,
    ← integral_sub hfi hsi]
  calc
    _ ≤ ∫ z, |Real.cos (u * manuscriptCoupledD z) - Real.cos (u * manuscriptCoupledLimitD z)| ∂π.prod π := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => Real.cos (u * manuscriptCoupledD z) - Real.cos (u * manuscriptCoupledLimitD z)) (μ := π.prod π)
    _ ≤ ∫ z, T * |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂π.prod π := by
      apply integral_mono (hfi.sub hsi).abs (hab.const_mul T)
      intro z
      exact (manuscript_cos_difference_bound u (manuscriptCoupledD z) (manuscriptCoupledLimitD z) T hu).trans (min_le_right _ _)
    _ = _ := integral_const_mul _ _

/-- The manuscript's compact q convergence, on the actual independent double coupling. -/
theorem manuscript_compact_square_from_wassersteinThree
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun j => characteristicSquare (P j)) (characteristicSquare Q) atTop K := by
  obtain ⟨π, hπ, hf, hs, hi3, _, hc2⟩ := manuscript_cubic_coupling_costs_tendsto P Q hW
  have hi2 : ∀ j, Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (π j) := by
    intro j
    letI := hπ j
    exact manuscript_coupled_square_integrable (π j) (hi3 j)
  have hlim := (manuscript_double_coupling_limits P Q π hπ hf hs hi2 hc2).2.1
  obtain ⟨T, hT, hTK⟩ := hK.isBounded.exists_pos_norm_le
  have he : Tendsto (fun j => T * (∫ z, |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂(π j).prod (π j))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul T
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  filter_upwards [he.eventually (gt_mem_nhds hε)] with j hj
  intro u hu
  letI := hπ j
  have hb := manuscript_square_coupling_bound (P j) Q (π j) (hf j) (hs j) (hi2 j) T u
    (by simpa only [Real.norm_eq_abs] using hTK u hu)
  rw [Real.dist_eq, abs_sub_comm]
  exact hb.trans_lt hj

/-- The displayed q'' coupled-integral bound followed by truncation of the fixed D². -/
theorem manuscript_compact_curvature_from_wassersteinThree
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun j => characteristicSquareCurvature (P j))
      (characteristicSquareCurvature Q) atTop K := by
  obtain ⟨π, hπ, hf, hs, hi3, _, hc2⟩ := manuscript_cubic_coupling_costs_tendsto P Q hW
  have hi2 : ∀ j, Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (π j) := by
    intro j
    letI := hπ j
    exact manuscript_coupled_square_integrable (π j) (hi3 j)
  have hlim := manuscript_double_coupling_limits P Q π hπ hf hs hi2 hc2
  obtain ⟨T, hT, hTK⟩ := hK.isBounded.exists_pos_norm_le
  have htail := manuscript_square_tail_tendsto (manuscriptDifferenceLaw Q.measure Q.measure)
    (manuscriptDifferenceLaw_second_integrable Q)
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  obtain ⟨A, hA⟩ := (htail.eventually (gt_mem_nhds (by positivity : 0 < ε / 4))).exists
  have he : Tendsto (fun j =>
      (∫ z, |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2| ∂(π j).prod (π j)) +
      ((A : ℝ) * T) * (∫ z, |manuscriptCoupledD z - manuscriptCoupledLimitD z| ∂(π j).prod (π j)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hlim.2.2.add (hlim.2.1.const_mul ((A : ℝ) * T))
  filter_upwards [he.eventually (gt_mem_nhds (by positivity : 0 < ε / 2))] with j hj
  intro u hu
  letI := hπ j
  have hb := manuscript_curvature_coupling_bound (P j) Q (π j) (hf j) (hs j) (hi2 j)
    T A u hT.le (Nat.cast_nonneg A) (by simpa only [Real.norm_eq_abs] using hTK u hu)
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end BerryEsseen
