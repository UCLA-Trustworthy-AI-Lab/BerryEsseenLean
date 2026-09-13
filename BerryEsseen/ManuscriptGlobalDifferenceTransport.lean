import BerryEsseen.ManuscriptGlobalDifferenceDerivatives
import BerryEsseen.PublishedWasserstein

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Two independent copies of an actual coupling, mapped to the pair of
independent differences. -/
def manuscriptDifferenceCoupling (π : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  (π.prod π).map (fun xy : (ℝ × ℝ) × (ℝ × ℝ) =>
    (xy.1.1 - xy.2.1, xy.1.2 - xy.2.2))

instance manuscriptDifferenceCoupling_probability (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π] : IsProbabilityMeasure (manuscriptDifferenceCoupling π) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem manuscript_difference_coupling_marginals (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π] (μ ν : Measure ℝ)
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν) :
    (manuscriptDifferenceCoupling π).map Prod.fst = manuscriptDifferenceLaw μ μ ∧
    (manuscriptDifferenceCoupling π).map Prod.snd = manuscriptDifferenceLaw ν ν := by
  letI : IsFiniteMeasure π := inferInstance
  letI : SigmaFinite π := IsFiniteMeasure.toSigmaFinite π
  letI : SFinite π := inferInstance
  constructor
  · rw [manuscriptDifferenceCoupling, Measure.map_map (by fun_prop) (by fun_prop),
      manuscriptDifferenceLaw, ← hfst, Measure.map_prod_map π π measurable_fst measurable_fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · rw [manuscriptDifferenceCoupling, Measure.map_map (by fun_prop) (by fun_prop),
      manuscriptDifferenceLaw, ← hsnd, Measure.map_prod_map π π measurable_snd measurable_snd,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

theorem manuscript_difference_coupling_cost (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) π) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) (manuscriptDifferenceCoupling π) ∧
      (∫ z, |z.1 - z.2| ∂manuscriptDifferenceCoupling π) ≤ 2 * ∫ z, |z.1 - z.2| ∂π := by
  letI : IsFiniteMeasure π := inferInstance
  letI : SigmaFinite π := IsFiniteMeasure.toSigmaFinite π
  letI : SFinite π := inferInstance
  have hb (x : (ℝ × ℝ) × (ℝ × ℝ)) :
      |(x.1.1 - x.2.1) - (x.1.2 - x.2.2)| ≤ |x.1.1 - x.1.2| + |x.2.1 - x.2.2| := by
    have he : (x.1.1 - x.2.1) - (x.1.2 - x.2.2) =
        (x.1.1 - x.1.2) - (x.2.1 - x.2.2) := by ring
    rw [he]
    exact abs_sub _ _
  have hiB := (hi.comp_fst π).add (hi.comp_snd π)
  have hiD : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) =>
      |(x.1.1 - x.2.1) - (x.1.2 - x.2.2)|) (π.prod π) := by
    apply hiB.mono' (by fun_prop)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_abs] using hb x
  constructor
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hiD
  · rw [manuscriptDifferenceCoupling, integral_map (by fun_prop) (by fun_prop)]
    calc
      _ ≤ ∫ x : (ℝ × ℝ) × (ℝ × ℝ), |x.1.1 - x.1.2| + |x.2.1 - x.2.2| ∂π.prod π :=
        integral_mono_ae hiD hiB (ae_of_all _ hb)
      _ = _ := by
        rw [integral_add (hi.comp_fst π) (hi.comp_snd π), integral_fun_fst (fun z : ℝ × ℝ => |z.1 - z.2|),
          integral_fun_snd (fun z : ℝ × ℝ => |z.1 - z.2|)]
        simp only [probReal_univ, one_smul]
        ring

theorem manuscript_transportCosts_nonempty (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    (transportCosts μ ν).Nonempty := by
  refine ⟨∫ z : ℝ × ℝ, |z.1 - z.2| ∂μ.prod ν, μ.prod ν, inferInstance, ?_, ?_, ?_, rfl⟩
  · simp
  · simp
  · exact ((hμ.comp_fst ν).sub (hν.comp_snd μ)).abs

theorem manuscript_difference_wasserstein_le_two (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    wassersteinOne (manuscriptDifferenceLaw μ μ) (manuscriptDifferenceLaw ν ν) ≤
      2 * wassersteinOne μ ν := by
  have hhalf : wassersteinOne (manuscriptDifferenceLaw μ μ) (manuscriptDifferenceLaw ν ν) / 2 ≤
      wassersteinOne μ ν := by
    apply le_csInf (manuscript_transportCosts_nonempty μ ν hμ hν)
    rintro r ⟨π, hπ, hf, hs, hi, rfl⟩
    letI := hπ
    obtain ⟨hf', hs'⟩ := manuscript_difference_coupling_marginals π μ ν hf hs
    obtain ⟨hi', hb⟩ := manuscript_difference_coupling_cost π hi
    have hl := wassersteinOne_le_coupling_cost _ _ (manuscriptDifferenceCoupling π)
      inferInstance hf' hs' hi'
    linarith
  linarith

end BerryEsseen
