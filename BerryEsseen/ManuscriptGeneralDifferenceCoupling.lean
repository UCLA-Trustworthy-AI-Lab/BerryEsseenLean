import BerryEsseen.ManuscriptGeneralCoupling
import BerryEsseen.ManuscriptDifferenceDerivativesCore

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

abbrev ManuscriptDoubleCoupling := (ℝ × ℝ) × (ℝ × ℝ)

def manuscriptCoupledD (z : ManuscriptDoubleCoupling) : ℝ := z.1.1 - z.2.1
def manuscriptCoupledLimitD (z : ManuscriptDoubleCoupling) : ℝ := z.1.2 - z.2.2

theorem manuscript_double_coupling_fst (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π] (μ : Measure ℝ) (hf : π.map Prod.fst = μ) :
    (π.prod π).map manuscriptCoupledD = manuscriptDifferenceLaw μ μ := by
  letI : SFinite π := inferInstance
  rw [manuscriptDifferenceLaw, ← hf, Measure.map_prod_map π π measurable_fst measurable_fst,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem manuscript_double_coupling_snd (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π] (μ : Measure ℝ) (hs : π.map Prod.snd = μ) :
    (π.prod π).map manuscriptCoupledLimitD = manuscriptDifferenceLaw μ μ := by
  letI : SFinite π := inferInstance
  rw [manuscriptDifferenceLaw, ← hs, Measure.map_prod_map π π measurable_snd measurable_snd,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem manuscript_double_coupling_second_fst (P : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (hf : π.map Prod.fst = P.measure) :
    Integrable (fun z => manuscriptCoupledD z ^ 2) (π.prod π) ∧
      (∫ z, manuscriptCoupledD z ^ 2 ∂π.prod π) = 2 := by
  have hmap := manuscript_double_coupling_fst π P.measure hf
  constructor
  · have h := manuscriptDifferenceLaw_second_integrable P
    rw [← hmap] at h
    exact (integrable_map_measure (by fun_prop) (by unfold manuscriptCoupledD; fun_prop)).mp h
  · have h := manuscriptDifferenceLaw_second P
    rw [← hmap, integral_map (by unfold manuscriptCoupledD; fun_prop) (by fun_prop)] at h
    exact h

theorem manuscript_double_coupling_second_snd (P : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (hs : π.map Prod.snd = P.measure) :
    Integrable (fun z => manuscriptCoupledLimitD z ^ 2) (π.prod π) ∧
      (∫ z, manuscriptCoupledLimitD z ^ 2 ∂π.prod π) = 2 := by
  have hmap := manuscript_double_coupling_snd π P.measure hs
  constructor
  · have h := manuscriptDifferenceLaw_second_integrable P
    rw [← hmap] at h
    exact (integrable_map_measure (by fun_prop) (by unfold manuscriptCoupledLimitD; fun_prop)).mp h
  · have h := manuscriptDifferenceLaw_second P
    rw [← hmap, integral_map (by unfold manuscriptCoupledLimitD; fun_prop) (by fun_prop)] at h
    exact h

theorem manuscript_double_coupling_error_integrable (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π) :
    Integrable (fun z => (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2) (π.prod π) := by
  letI : SFinite π := inferInstance
  apply (((hi.comp_fst π).add (hi.comp_snd π)).const_mul 2).mono'
    (by unfold manuscriptCoupledD manuscriptCoupledLimitD; fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp [manuscriptCoupledD, manuscriptCoupledLimitD]
  nlinarith [sq_nonneg ((z.1.1 - z.1.2) + (z.2.1 - z.2.2))]

/-- Independent copies preserve L2 convergence of the differences D_j-D. -/
theorem manuscript_double_coupling_error_bound (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π) :
    (∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂π.prod π) ≤
      4 * (∫ z, (z.1 - z.2) ^ 2 ∂π) := by
  letI : SFinite π := inferInstance
  have hb := integral_mono (manuscript_double_coupling_error_integrable π hi)
    (((hi.comp_fst π).add (hi.comp_snd π)).const_mul 2)
    (fun z => by
      dsimp [manuscriptCoupledD, manuscriptCoupledLimitD]
      nlinarith [sq_nonneg ((z.1.1 - z.1.2) + (z.2.1 - z.2.2))])
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (hi.comp_fst π) (hi.comp_snd π),
    integral_fun_fst (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2),
    integral_fun_snd (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)] at hb
  simpa only [probReal_univ, one_smul, mul_add, ← two_mul, ← mul_assoc,
    show (2 : ℝ) * 2 = 4 by norm_num] using hb

theorem manuscript_square_difference_young (a b r : ℝ) (hr : 0 < r) :
    |a ^ 2 - b ^ 2| ≤ (a - b) ^ 2 / (2 * r) + r * (a ^ 2 + b ^ 2) := by
  have he : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [he, abs_mul]
  rw [show (a - b) ^ 2 / (2 * r) + r * (a ^ 2 + b ^ 2) =
      ((a - b) ^ 2 + 2 * r ^ 2 * (a ^ 2 + b ^ 2)) / (2 * r) by
        field_simp [hr.ne'] <;> ring]
  apply (le_div_iff₀ (by positivity : 0 < 2 * r)).2
  have hs := sq_nonneg (|a - b| - r * |a + b|)
  have hsum := mul_nonneg (sq_nonneg r) (sq_nonneg (a - b))
  nlinarith only [hs, hsum, sq_abs (a - b), sq_abs (a + b)]

theorem manuscript_double_coupling_square_difference_integrable (P Q : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hf : π.map Prod.fst = P.measure) (hs : π.map Prod.snd = Q.measure) :
    Integrable (fun z => |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2|) (π.prod π) :=
  ((manuscript_double_coupling_second_fst P π hf).1.sub
    (manuscript_double_coupling_second_snd Q π hs).1).abs

/-- This proves the manuscript's D_j² -> D² in L1, with an explicit Young budget. -/
theorem manuscript_double_coupling_square_difference_bound (P Q : StandardizedLaw)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hf : π.map Prod.fst = P.measure) (hs : π.map Prod.snd = Q.measure)
    (hi : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π)
    (r : ℝ) (hr : 0 < r) :
    (∫ z, |manuscriptCoupledD z ^ 2 - manuscriptCoupledLimitD z ^ 2| ∂π.prod π) ≤
      (∫ z, (manuscriptCoupledD z - manuscriptCoupledLimitD z) ^ 2 ∂π.prod π) / (2 * r) + 4 * r := by
  obtain ⟨hf2, hfint⟩ := manuscript_double_coupling_second_fst P π hf
  obtain ⟨hs2, hsint⟩ := manuscript_double_coupling_second_snd Q π hs
  have hi2 := manuscript_double_coupling_error_integrable π hi
  have hsum : Integrable (fun z => manuscriptCoupledD z ^ 2 + manuscriptCoupledLimitD z ^ 2) (π.prod π) := hf2.add hs2
  have hright : Integrable (fun z => r * (manuscriptCoupledD z ^ 2 + manuscriptCoupledLimitD z ^ 2)) (π.prod π) := hsum.const_mul r
  have hb := integral_mono ((hf2.sub hs2).abs)
    ((hi2.div_const (2 * r)).add hright)
    (fun z => manuscript_square_difference_young _ _ r hr)
  simp only [Pi.add_apply, Pi.sub_apply] at hb
  rw [integral_add (hi2.div_const (2 * r)) hright,
    integral_div, integral_const_mul, integral_add hf2 hs2, hfint, hsint] at hb
  convert hb using 1 <;> ring

end BerryEsseen
