import BerryEsseen.EffectiveConfinementMass
import BerryEsseen.WassersteinBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_affine_wasserstein_le (K : PublishedWassersteinDuality)
    (P Q : StandardizedLaw) (a b : ℝ) (hb : 0 < b) :
    wassersteinOne (P.measure.map (fun x => a + b * x)) (Q.measure.map (fun x => a + b * x)) ≤
      b * wassersteinOne P.measure Q.measure := by
  let A := fun x : ℝ => a + b * x
  letI : IsProbabilityMeasure (P.measure.map A) := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (Q.measure.map A) := Measure.isProbabilityMeasure_map (by fun_prop)
  apply wassersteinOne_le_of_lipschitz K (P.measure.map A) (Q.measure.map A)
    (confinement_affine_first_integrable P a b) (confinement_affine_first_integrable Q a b)
  intro f hf
  let g := fun x : ℝ => f (A x) / b
  have hg : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    dsimp [g]
    rw [← sub_div, abs_div, abs_of_pos hb]
    apply (div_le_iff₀ hb).mpr
    have h := lipschitz_one_pointwise f hf (A x) (A y)
    have he : |A x - A y| = |x - y| * b := by
      rw [show A x - A y = b * (x - y) by dsimp [A]; ring, abs_mul, abs_of_pos hb]
      ring
    rwa [he] at h
  have hm := mul_le_mul_of_nonneg_left
    (lipschitz_integral_le_wassersteinOne K P.measure Q.measure P.first_integrable Q.first_integrable g hg) hb.le
  have he : (∫ x, f x ∂P.measure.map A) - (∫ x, f x ∂Q.measure.map A) =
      b * ((∫ x, g x ∂P.measure) - ∫ x, g x ∂Q.measure) := by
    rw [integral_map (by fun_prop) hf.continuous.measurable.aestronglyMeasurable,
      integral_map (by fun_prop) hf.continuous.measurable.aestronglyMeasurable]
    dsimp [g]
    rw [integral_div, integral_div]
    field_simp [hb.ne']
  exact he.le.trans hm

theorem manuscript_affine_wasserstein_eq (K : PublishedWassersteinDuality)
    (P Q : StandardizedLaw) (a b : ℝ) (hb : 0 < b) :
    wassersteinOne (P.measure.map (fun x => a + b * x)) (Q.measure.map (fun x => a + b * x)) =
      b * wassersteinOne P.measure Q.measure := by
  apply le_antisymm (manuscript_affine_wasserstein_le K P Q a b hb)
  let A := fun x : ℝ => a + b * x
  let μ := P.measure.map A
  let ν := Q.measure.map A
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hμ := confinement_affine_first_integrable P a b
  have hν := confinement_affine_first_integrable Q a b
  have hrev : wassersteinOne P.measure Q.measure ≤ wassersteinOne μ ν / b := by
    apply wassersteinOne_le_of_lipschitz K P.measure Q.measure P.first_integrable Q.first_integrable
    intro f hf
    let g := fun y : ℝ => b * f ((y - a) / b)
    have hg : LipschitzWith 1 g := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      dsimp [g]
      rw [← mul_sub, abs_mul, abs_of_pos hb]
      have h := mul_le_mul_of_nonneg_left (lipschitz_one_pointwise f hf ((x - a) / b) ((y - a) / b)) hb.le
      have he : b * |(x - a) / b - (y - a) / b| = |x - y| := by
        rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hb]
        field_simp [hb.ne']
      exact h.trans_eq he
    have hgi := lipschitz_integral_le_wassersteinOne K μ ν hμ hν g hg
    have hcomp (x : ℝ) : g (A x) = b * f x := by
      dsimp [g, A]
      rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hb.ne']
    have hintP : (∫ x, g x ∂μ) = b * ∫ x, f x ∂P.measure := by
      rw [integral_map (by fun_prop) hg.continuous.measurable.aestronglyMeasurable]
      simp only [hcomp, integral_const_mul]
    have hintQ : (∫ x, g x ∂ν) = b * ∫ x, f x ∂Q.measure := by
      rw [integral_map (by fun_prop) hg.continuous.measurable.aestronglyMeasurable]
      simp only [hcomp, integral_const_mul]
    rw [hintP, hintQ] at hgi
    apply (le_div_iff₀ hb).mpr
    nlinarith only [hgi]
  have hm := (le_div_iff₀ hb).mp hrev
  nlinarith only [hm]

theorem manuscript_esseen_affine_wasserstein_bound (K : PublishedWassersteinDuality)
    (P : StandardizedLaw)
    (hW : wassersteinOne P.measure esseenLaw.measure ≤ Real.exp (-7 * appendixA)) :
    wassersteinOne (P.measure.map (fun x => pE + sigmaE * x))
      (esseenLaw.measure.map (fun x => pE + sigmaE * x)) ≤ Real.exp (-7 * appendixA) := by
  have hσ : sigmaE ≤ 1 := by nlinarith [sigmaE_sq, sigmaE_pos, pE_add_qE, sq_nonneg (pE - qE)]
  have h1 := (manuscript_affine_wasserstein_eq K P esseenLaw pE sigmaE sigmaE_pos).le
  have h2 := mul_le_mul_of_nonneg_left hW sigmaE_pos.le
  have h3 := mul_le_mul_of_nonneg_right hσ (Real.exp_pos (-7 * appendixA)).le
  nlinarith only [h1, h2, h3]

/-- Collapse to the neighboring integer, bound its actual transport cost,
and use the Wasserstein triangle inequality as in the final paragraph of the manuscript. -/
theorem manuscript_two_interval_mass_via_transport (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ζ w p : ℝ) (hζ : ζ < 1 / 2)
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν)
    (hνm : (∫ x, x ∂ν) = p) (hW : wassersteinOne μ ν ≤ w)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |μ.real (Icc (1 - ζ) (1 + ζ)) - p| ≤ ζ + w := by
  let C := Icc (1 - ζ) (1 + ζ)
  let b : ℝ → ℝ := C.indicator (fun _ => 1)
  have hC : MeasurableSet C := measurableSet_Icc
  have hbm : Measurable b := measurable_const.indicator hC
  have hbi : Integrable b μ := (integrable_const 1).indicator hC
  let ρ := μ.map b
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hbm.aemeasurable
  have hρi : Integrable (fun x : ℝ => x) ρ :=
    (integrable_map_measure (by fun_prop) hbm.aemeasurable).mpr hbi
  have hρm : (∫ x, x ∂ρ) = μ.real C := by
    rw [integral_map hbm.aemeasurable (by fun_prop)]
    exact integral_indicator_one hC
  have hcost : ∀ᵐ x ∂μ, |b x - x| ≤ ζ := by
    filter_upwards [hb] with x hx
    rcases hx with hx | hx
    · have hxC : x ∉ C := by intro h; have := h.1; linarith [hx.2]
      simp only [b, indicator_of_notMem hxC, zero_sub, abs_neg]
      exact abs_le.mpr hx
    · have hxC : x ∈ C := hx
      simp only [b, indicator_of_mem hxC]
      exact abs_le.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hcollapse : wassersteinOne ρ μ ≤ ζ := by
    apply (wassersteinOne_map_le K μ b hbm hμ hbi).trans
    calc
      (∫ x, |b x - x| ∂μ) ≤ ∫ _, ζ ∂μ := integral_mono_ae (hbi.sub hμ).abs (integrable_const _) hcost
      _ = ζ := by simp
  have htriangle := wassersteinOne_triangle K ρ μ ν hρi hμ hν
  have hid : LipschitzWith 1 (fun x : ℝ => x) := LipschitzWith.id
  have hneg : LipschitzWith 1 (fun x : ℝ => -x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp
  have hp := lipschitz_integral_le_wassersteinOne K ρ ν hρi hν (fun x => x) hid
  have hm := lipschitz_integral_le_wassersteinOne K ρ ν hρi hν (fun x => -x) hneg
  rw [hρm, hνm] at hp
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg, hρm, hνm] at hm
  apply abs_le.mpr
  constructor <;> linarith only [hp, hm, htriangle, hcollapse, hW]

theorem manuscript_confinement_half_eta_mass (K : PublishedWassersteinDuality)
    (P : StandardizedLaw)
    (hW : wassersteinOne P.measure esseenLaw.measure ≤ Real.exp (-7 * appendixA))
    (hb : ∀ x ∈ P.measure.support,
      pE + sigmaE * x ∈ Icc (-(appendixEtaStar / 2)) (appendixEtaStar / 2) ∪
        Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2)) :
    |(P.measure.map (fun x => pE + sigmaE * x)).real (Ioi (1 / 2)) - pE| < appendixEtaStar := by
  let μ := P.measure.map (fun x => pE + sigmaE * x)
  let ν := esseenLaw.measure.map (fun x => pE + sigmaE * x)
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hζ : appendixEtaStar / 2 < 1 / 2 := by linarith [appendixEtaStar_bounds.1.2]
  have hae := confinement_affine_intervals_ae P pE sigmaE (appendixEtaStar / 2) hb
  have hm := manuscript_two_interval_mass_via_transport K μ ν (appendixEtaStar / 2)
    (Real.exp (-7 * appendixA)) pE hζ
    (confinement_affine_first_integrable P pE sigmaE)
    (confinement_affine_first_integrable esseenLaw pE sigmaE)
    (confinement_affine_mean esseenLaw pE sigmaE)
    (manuscript_esseen_affine_wasserstein_bound K P hW) hae
  have he := exponential_relative_sixteenth 1 (7 * appendixA) (2 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(7 * appendixA) = -7 * appendixA by ring, show -(2 * appendixA) = -2 * appendixA by ring] at he
  rw [upper_interval_mass_eq μ (appendixEtaStar / 2) hζ hae]
  dsimp [appendixEtaStar] at hm ⊢
  nlinarith only [hm, he, Real.exp_pos (-2 * appendixA)]

end BerryEsseen
