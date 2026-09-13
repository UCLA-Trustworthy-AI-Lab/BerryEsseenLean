import BerryEsseen.SumMoments
import BerryEsseen.JitterLowFrequency
import BerryEsseen.GaussianHermiteCDF

/-! Finite first moments for the actual laws and signed densities to which
the manuscript smoothing lemma is applied.  These facts use the defining
moments of `StandardizedLaw` and compact support of the uniform jitter. -/
noncomputable section
open MeasureTheory Set
namespace BerryEsseen

theorem uniformJitter_first_integrable (h : ℝ) :
    Integrable (fun x : ℝ => x) (uniformJitter h) := by
  unfold uniformJitter
  have hi : Integrable (fun x : ℝ => x)
      (volume.restrict (Icc (-h / 2) (h / 2))) :=
    continuous_id.integrableOn_Icc
  exact hi.smul_measure (c := ENNReal.ofReal (1 / h)) ENNReal.ofReal_ne_top

theorem spanJitter_first_integrable (h : ℝ) :
    Integrable (fun x : ℝ => x) (spanJitter h) := by
  unfold spanJitter
  split_ifs
  · exact uniformJitter_first_integrable h
  · exact integrable_dirac (by simp)

theorem convolution_first_integrable (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ)
    (hν : Integrable (fun x : ℝ => x) ν) :
    Integrable (fun x : ℝ => x) (μ ∗ ν) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

theorem normalizedIIDMap_first_integrable (P : StandardizedLaw) (n : ℕ) :
    Integrable (fun x : ℝ => x)
      ((iidSumLaw P.measure n).map (fun x => x / Real.sqrt (n : ℝ))) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  exact (iidSumLaw_moments P n).1.div_const _

theorem normalizedJitteredSumLaw_first_integrable (P : StandardizedLaw) (n : ℕ) (h : ℝ) :
    Integrable (fun x : ℝ => x) (normalizedJitteredSumLaw P n h) := by
  letI := spanJitter_probability h
  unfold normalizedJitteredSumLaw
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  exact (convolution_first_integrable _ _ (iidSumLaw_moments P n).1
    (spanJitter_first_integrable h)).div_const _

theorem edgeworthDensity_first_integrable (n : ℕ) (κ : ℝ) :
    Integrable (fun x : ℝ => x * edgeworthDensity n κ x) := by
  convert (gaussian_monomial_integrable 1).add
    (((gaussian_monomial_integrable 4).sub
      ((gaussian_monomial_integrable 2).const_mul 3)).const_mul
      (κ / (6 * Real.sqrt (n : ℝ)))) using 1
  funext x
  dsimp [edgeworthDensity, gaussianHermiteThree]
  ring

end BerryEsseen
