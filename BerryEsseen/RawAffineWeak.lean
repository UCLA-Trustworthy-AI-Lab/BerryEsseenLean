import BerryEsseen.AffineLatticeSpan
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem probabilityMeasure_map_affine_eq_prod_dirac (μ : ProbabilityMeasure ℝ) (a b : ℝ) :
    μ.map (show Measurable (fun x : ℝ => a * x + b) by fun_prop).aemeasurable =
      (μ.prod (diracProba (a, b))).map
        (show Measurable (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2) by
          fun_prop).aemeasurable := by
  apply Subtype.ext
  change (μ : Measure ℝ).map (fun x => a * x + b) =
    ((μ : Measure ℝ).prod (Measure.dirac (a, b))).map
      (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2)
  rw [Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem probabilityMeasure_tendsto_map_affine {ι : Type*} {L : Filter ι}
    (μj : ι → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (aj bj : ι → ℝ) (a b : ℝ)
    (hμ : Tendsto μj L (𝓝 μ)) (ha : Tendsto aj L (𝓝 a)) (hb : Tendsto bj L (𝓝 b)) :
    Tendsto (fun j => (μj j).map
      (show Measurable (fun x : ℝ => aj j * x + bj j) by fun_prop).aemeasurable) L
      (𝓝 (μ.map (show Measurable (fun x : ℝ => a * x + b) by fun_prop).aemeasurable)) := by
  have hd : Tendsto (fun j => diracProba (aj j, bj j)) L (𝓝 (diracProba (a, b))) :=
    continuous_diracProba.continuousAt.tendsto.comp (ha.prodMk_nhds hb)
  have hp : Tendsto (fun j => (μj j).prod (diracProba (aj j, bj j))) L
      (𝓝 (μ.prod (diracProba (a, b)))) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hμ.prodMk_nhds hd)
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hp
    (show Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1 * z.1 + z.2.2) by fun_prop)
  simpa only [← probabilityMeasure_map_affine_eq_prod_dirac] using hm

theorem latticeSpan_standardized_iff (μ : Measure ℝ) (m σ h : ℝ) (hσ : 0 < σ) :
    IsLatticeSpan (standardizedMeasure μ m σ) h ↔ IsLatticeSpan μ (σ * h) := by
  constructor
  · intro hh
    have hl := latticeSpan_affine_map (standardizedMeasure μ m σ) σ m h hσ hh
    have hi : (standardizedMeasure μ m σ).map (fun x => σ * x + m) = μ := by
      rw [standardizedMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
      have he : (fun x : ℝ => σ * ((x - m) / σ) + m) = id := by
        funext x
        dsimp
        field_simp
        ring
      change μ.map (fun x : ℝ => σ * ((x - m) / σ) + m) = μ
      rw [he, Measure.map_id]
    rwa [hi] at hl
  · intro hh
    simpa only [mul_div_cancel_left₀ h hσ.ne'] using
      latticeSpan_standardized μ m σ (σ * h) hσ hh

end BerryEsseen
