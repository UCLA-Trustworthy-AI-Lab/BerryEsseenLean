import BerryEsseen.ConvolutionContact
import BerryEsseen.GaussianPrimitives
import BerryEsseen.InfluenceCalculus
import BerryEsseen.ConvolutionDerivative
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Integration of the actual moment, convolution, and Gaussian derivatives
into the contamination argument. The variational conclusions require the
explicit premise that contamination cannot increase the objective. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def signedRatio (P : StandardizedLaw) (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (n + 1 : ℝ) *
    (cdf (iidSumLaw P.measure (n + 1)) t - normalCDF (t / Real.sqrt (n + 1 : ℝ))) /
      thirdMoment P

def contaminationObjective (P : StandardizedLaw) (n : ℕ) (t y e : ℝ) : ℝ :=
  let s := Real.sqrt (n + 1 : ℝ)
  s * Real.sqrt (contaminatedVariance P y e) ^ 3 / contaminatedThird P y e *
    (cdf (iidSumLaw (contaminatedMeasure P y e) (n + 1)) t -
      normalCDF ((t - s ^ 2 * (∫ x, x ∂contaminatedMeasure P y e)) /
        (s * Real.sqrt (contaminatedVariance P y e))))

theorem contaminationObjective_zero (P : StandardizedLaw) (n : ℕ) (t y : ℝ) :
    contaminationObjective P n t y 0 = signedRatio P n t := by
  have hz : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  simp [contaminationObjective, signedRatio, contaminated_variance_formula P y hz,
    contaminated_third_formula P y hz, contaminationThirdExtension_zero,
    contaminatedMeasure_zero, P.mean_zero]
  ring

/-- A reusable chain-rule wrapper. The CDF derivative premise is discharged
in `contamination_influence` below. -/
theorem contamination_influence_of_cdf_derivative (P : StandardizedLaw) (n : ℕ) (t y : ℝ)
    (hF : HasDerivWithinAt
      (fun e => cdf (iidSumLaw (contaminatedMeasure P y e) (n + 1)) t)
      ((n + 1 : ℝ) * (cdf (iidSumLaw P.measure n) (t - y) -
        cdf (iidSumLaw P.measure (n + 1)) t)) (Icc 0 1) 0) :
    HasDerivWithinAt (contaminationObjective P n t y)
      (influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
        (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
        (signedRatio P n t) y / thirdMoment P) (Icc 0 1) 0 := by
  let s := Real.sqrt (n + 1 : ℝ)
  let F := fun e => cdf (iidSumLaw (contaminatedMeasure P y e) (n + 1)) t
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hsz : s * (t / s) = t := by field_simp
  have hz : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hm0 : (∫ x, x ∂contaminatedMeasure P y 0) = 0 := by
    rw [contaminated_mean P y hz]; ring
  have hv0 : contaminatedVariance P y 0 = 1 := by
    rw [contaminated_variance_formula P y hz]; ring
  have hρ0 : contaminatedThird P y 0 = thirdMoment P := by
    rw [contaminated_third_formula P y hz, contaminationThirdExtension_zero]
  have hF0 : F 0 = cdf (iidSumLaw P.measure (n + 1)) t := by
    dsimp [F]; rw [contaminatedMeasure_zero]
  have hF' : HasDerivWithinAt F
      (s ^ 2 * (cdf (iidSumLaw P.measure n) (t - y) - F 0)) (Icc 0 1) 0 := by
    rw [hs2, hF0]
    exact hF
  have hR : signedRatio P n t = s * (F 0 - normalCDF (t / s)) / thirdMoment P := by
    rw [hF0]; rfl
  have hd := contamination_chain_rule_within
    (fun e => ∫ x, x ∂contaminatedMeasure P y e) (contaminatedVariance P y)
    (contaminatedThird P y) F normalCDF s (t / s) y (thirdMoment P)
    (signedSecondMoment P) (cdf (iidSumLaw P.measure n) (t - y))
    (signedRatio P n t) (standardNormalDensity (t / s)) hs
    (ne_of_gt (thirdMoment_pos P)) hm0 hv0 hρ0 hR
    (contaminated_mean_right_derivative P y) (contaminated_variance_right_derivative P y)
    (contaminated_third_right_derivative P y) hF' (normalCDF_hasDerivAt (t / s))
  rw [hsz] at hd
  convert hd using 1
  dsimp [influenceNumerator]
  rw [hF0]
  ring

theorem right_derivative_nonpos_at_maximum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt f d (Icc 0 1) 0)
    (hmax : ∀ e ∈ Icc 0 1, f e ≤ f 0) : d ≤ 0 := by
  have hm : IsLocalMaxOn f (Icc 0 1) 0 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact hmax e he
  have ht : (1 : ℝ) ∈ posTangentConeAt (Icc 0 1) (0 : ℝ) := by
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Icc 0 1 := by
      rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using sub_mem_posTangentConeAt_of_segment_subset hseg
  have h := hm.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt ht
  simpa using h

theorem influence_contact_of_cdf_derivatives_and_maximum (P : StandardizedLaw)
    (n : ℕ) (t : ℝ)
    (hF : ∀ y, HasDerivWithinAt
      (fun e => cdf (iidSumLaw (contaminatedMeasure P y e) (n + 1)) t)
      ((n + 1 : ℝ) * (cdf (iidSumLaw P.measure n) (t - y) -
        cdf (iidSumLaw P.measure (n + 1)) t)) (Icc 0 1) 0)
    (hmax : ∀ y e, e ∈ Icc 0 1 →
      contaminationObjective P n t y e ≤ contaminationObjective P n t y 0) :
    ∀ y ∈ P.measure.support,
      influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
        (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
        (signedRatio P n t) y = 0 := by
  apply influenceNumerator_contact P n t _ _ _ _ (Real.sqrt_nonneg _)
  intro y
  have h := right_derivative_nonpos_at_maximum
    (contamination_influence_of_cdf_derivative P n t y (hF y)) (hmax y)
  simpa using (div_le_iff₀ (thirdMoment_pos P)).1 h

/-- The full contamination derivative for the actual convolution CDF and
actual moments, with no derivative premise. -/
theorem contamination_influence (P : StandardizedLaw) (n : ℕ) (t y : ℝ) :
    HasDerivWithinAt (contaminationObjective P n t y)
      (influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
        (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
        (signedRatio P n t) y / thirdMoment P) (Icc 0 1) 0 :=
  contamination_influence_of_cdf_derivative P n t y
    (contaminated_convolution_cdf_derivative P n t y)

theorem influence_contact_at_contamination_maximum (P : StandardizedLaw)
    (n : ℕ) (t : ℝ)
    (hmax : ∀ y e, e ∈ Icc 0 1 →
      contaminationObjective P n t y e ≤ contaminationObjective P n t y 0) :
    ∀ y ∈ P.measure.support,
      influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
        (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
        (signedRatio P n t) y = 0 :=
  influence_contact_of_cdf_derivatives_and_maximum P n t
    (fun y => contaminated_convolution_cdf_derivative P n t y) hmax

end BerryEsseen
