import BerryEsseen.ManuscriptLatticeCouplings

/-! Reflection of an actual transport plan preserves its cost. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_transportCosts_reflection_subset (μ ν : Measure ℝ) :
    transportCosts μ ν ⊆ transportCosts (μ.map (fun x => -x)) (ν.map (fun x => -x)) := by
  rintro r ⟨π, hπ, hfst, hsnd, hi, hr⟩
  letI : IsProbabilityMeasure π := hπ
  let F : ℝ × ℝ → ℝ × ℝ := fun z => (-z.1, -z.2)
  have hF : Measurable F := by fun_prop
  refine ⟨π.map F, Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hF, ← hfst,
      Measure.map_map (by fun_prop) measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hF, ← hsnd,
      Measure.map_map (by fun_prop) measurable_snd]
    rfl
  · apply (integrable_map_measure (by fun_prop) hF.aemeasurable).mpr
    simpa only [F, Function.comp_def, neg_sub_neg, abs_sub_comm] using hi
  · rw [integral_map hF.aemeasurable (by fun_prop)]
    simpa only [F, neg_sub_neg, abs_sub_comm] using hr

theorem manuscript_transportCosts_reflected (μ ν : Measure ℝ) :
    transportCosts (μ.map (fun x => -x)) (ν.map (fun x => -x)) = transportCosts μ ν := by
  apply Set.Subset.antisymm
  · simpa only [reflected_measure_twice] using
      manuscript_transportCosts_reflection_subset (μ.map (fun x => -x)) (ν.map (fun x => -x))
  · exact manuscript_transportCosts_reflection_subset μ ν

theorem manuscript_wasserstein_reflected_actual (μ ν : Measure ℝ) :
    wassersteinOne (μ.map (fun x => -x)) (ν.map (fun x => -x)) = wassersteinOne μ ν := by
  simp only [wassersteinOne, manuscript_transportCosts_reflected]

end BerryEsseen
