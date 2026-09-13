import BerryEsseen.WassersteinMoments

/-! Center the second coordinate of an actual coupling. The cost grows by
at most the magnitude of the centering constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def manuscriptCenteredMeasure (ν : Measure ℝ) (m : ℝ) : Measure ℝ :=
  ν.map (fun x => x - m)

def manuscriptCenteredCoupling (π : Measure (ℝ × ℝ)) (m : ℝ) : Measure (ℝ × ℝ) :=
  π.map (fun z => (z.1, z.2 - m))

theorem manuscript_centered_coupling_marginals (π : Measure (ℝ × ℝ)) (μ ν : Measure ℝ)
    (m : ℝ) (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν) :
    (manuscriptCenteredCoupling π m).map Prod.fst = μ ∧
      (manuscriptCenteredCoupling π m).map Prod.snd = manuscriptCenteredMeasure ν m := by
  constructor
  · rw [manuscriptCenteredCoupling, Measure.map_map (by fun_prop) (by fun_prop)]
    exact hfst
  · rw [manuscriptCenteredCoupling, manuscriptCenteredMeasure,
      Measure.map_map (by fun_prop) (by fun_prop), ← hsnd,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

theorem manuscript_centered_coupling_cost (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (m : ℝ) (hi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) π) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) (manuscriptCenteredCoupling π m) ∧
      (∫ z, |z.1 - z.2| ∂manuscriptCenteredCoupling π m) ≤
        (∫ z, |z.1 - z.2| ∂π) + |m| := by
  have hpoint (z : ℝ × ℝ) : |z.1 - (z.2 - m)| ≤ |z.1 - z.2| + |m| := by
    rw [show z.1 - (z.2 - m) = (z.1 - z.2) + m by ring]
    exact abs_add_le _ _
  have hi' : Integrable (fun z : ℝ × ℝ => |z.1 - (z.2 - m)|) π := by
    apply (hi.add (integrable_const |m|)).mono' (by fun_prop)
    simpa only [Real.norm_eq_abs, abs_abs] using ae_of_all π hpoint
  constructor
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hi'
  · rw [manuscriptCenteredCoupling, integral_map (by fun_prop) (by fun_prop)]
    have hh := integral_mono_ae hi' (hi.add (integrable_const |m|)) (ae_of_all π hpoint)
    simp only [Pi.add_apply] at hh
    rw [integral_add hi (integrable_const |m|)] at hh
    simpa only [integral_const, probReal_univ, one_smul] using hh

theorem manuscript_centering_wasserstein_actual (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) (m : ℝ) :
    wassersteinOne μ (manuscriptCenteredMeasure ν m) ≤ wassersteinOne μ ν + |m| := by
  have hnonempty : (transportCosts μ ν).Nonempty := by
    refine ⟨∫ z : ℝ × ℝ, |z.1 - z.2| ∂μ.prod ν, μ.prod ν, inferInstance, ?_, ?_, ?_, rfl⟩
    · simp
    · simp
    · exact ((hμ.comp_fst ν).sub (hν.comp_snd μ)).abs
  have hlower : wassersteinOne μ (manuscriptCenteredMeasure ν m) - |m| ≤ wassersteinOne μ ν := by
    apply le_csInf hnonempty
    rintro r ⟨π, hπ, hfst, hsnd, hi, rfl⟩
    letI : IsProbabilityMeasure π := hπ
    have hc := manuscript_centered_coupling_cost π m hi
    have hmarg := manuscript_centered_coupling_marginals π μ ν m hfst hsnd
    have hprob : IsProbabilityMeasure (manuscriptCenteredCoupling π m) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hw := wassersteinOne_le_coupling_cost μ (manuscriptCenteredMeasure ν m)
      (manuscriptCenteredCoupling π m) hprob hmarg.1 hmarg.2 hc.1
    linarith [hc.2]
  linarith

theorem manuscript_centered_transport_two_w (P : StandardizedLaw) (Q : Measure ℝ)
    [IsProbabilityMeasure Q] (w : ℝ) (hQ : Integrable (fun x : ℝ => x) Q)
    (hW : wassersteinOne P.measure Q ≤ w) (hm : |rawMean Q| ≤ w) :
    wassersteinOne P.measure (manuscriptCenteredMeasure Q (rawMean Q)) ≤ 2 * w := by
  have hh := manuscript_centering_wasserstein_actual P.measure Q P.first_integrable hQ (rawMean Q)
  linarith

end BerryEsseen
