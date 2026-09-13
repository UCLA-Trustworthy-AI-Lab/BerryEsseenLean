import BerryEsseen.Standardization
import BerryEsseen.RawInfluence
import BerryEsseen.ClassicalBounds

/-! The manuscript's contamination influence lemma for a globally maximizing
pair. All contamination maximality premises are discharged by standardizing
the actual contaminated measure. Existence of a maximizing pair is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BerryEsseen

theorem abs_signedRatio_eq_normalized (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    |signedRatio P n t| =
      normalizedDiscrepancy P (n + 1) (t / Real.sqrt (n + 1 : ℝ)) := by
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
  have ht : Real.sqrt (n + 1 : ℝ) * (t / Real.sqrt (n + 1 : ℝ)) = t := by field_simp
  simp only [signedRatio, normalizedDiscrepancy, discrepancy, Nat.cast_add, Nat.cast_one,
    ht, cdf_eq_real, Measure.real, abs_div, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (thirdMoment_pos P)]

theorem signedRatio_le_extremalConstant (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ) :
    signedRatio P n t ≤ extremalConstant (n + 1) := by
  calc
    signedRatio P n t ≤ |signedRatio P n t| := le_abs_self _
    _ = _ := abs_signedRatio_eq_normalized P n t
    _ ≤ _ := normalizedDiscrepancy_le_extremalConstant H P (n + 1) (by omega) _

theorem contaminationObjective_eq_standardized_signedRatio (P : StandardizedLaw)
    (n : ℕ) (t y e : ℝ) (he : e ∈ Ico 0 1) :
    contaminationObjective P n t y e =
      signedRatio (standardizedContamination P y e he) n
        ((t - (n + 1 : ℝ) * (e * y)) / Real.sqrt (contaminatedVariance P y e)) := by
  letI := contaminatedMeasure_probability P y ⟨he.1, he.2.le⟩
  have hs : 0 < Real.sqrt (contaminatedVariance P y e) :=
    Real.sqrt_pos.2 (contaminatedVariance_pos P y he)
  have hn : Real.sqrt (n + 1 : ℝ) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hcdf := standardized_sum_cdf (contaminatedMeasure P y e) (e * y)
    (Real.sqrt (contaminatedVariance P y e)) hs (n + 1) t
  simp only [Nat.cast_add, Nat.cast_one] at hcdf
  unfold contaminationObjective signedRatio
  dsimp only
  rw [standardizedContamination_measure, hcdf, standardizedContamination_third,
    hn, contaminated_mean P y ⟨he.1, he.2.le⟩]
  rw [div_div]
  rw [mul_comm (Real.sqrt (contaminatedVariance P y e)) (Real.sqrt (n + 1 : ℝ))]
  simp only [div_eq_mul_inv, inv_inv, mul_inv_rev]
  ring

theorem contaminationObjective_one (P : StandardizedLaw) (n : ℕ) (t y : ℝ) :
    contaminationObjective P n t y 1 = 0 := by
  simp [contaminationObjective, contaminatedVariance, contaminatedThird, contaminatedMeasure]

theorem contaminationObjective_maximal (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hpos : 0 ≤ signedRatio P n t) :
    ∀ y e, e ∈ Icc 0 1 → contaminationObjective P n t y e ≤ contaminationObjective P n t y 0 := by
  intro y e he
  rw [contaminationObjective_zero]
  rcases he.2.eq_or_lt with he1 | he1
  · subst e
    rwa [contaminationObjective_one]
  · rw [contaminationObjective_eq_standardized_signedRatio P n t y e ⟨he.1, he1⟩, hattain]
    exact signedRatio_le_extremalConstant H _ n _

/-- The derivative is nonpositive at every contamination point. -/
theorem influence_nonpos_at_extremizer (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hpos : 0 ≤ signedRatio P n t) (y : ℝ) :
    influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
      (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
      (signedRatio P n t) y ≤ 0 := by
  have h := right_derivative_nonpos_at_maximum (contamination_influence P n t y)
    (contaminationObjective_maximal H P n t hattain hpos y)
  simpa using (div_le_iff₀ (thirdMoment_pos P)).1 h

/-- Full support contact in Lemma `lem:influence`, from global maximality. -/
theorem influence_contact_at_extremizer (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hpos : 0 ≤ signedRatio P n t) :
    ∀ y ∈ P.measure.support,
      influenceNumerator P n t (Real.sqrt (n + 1 : ℝ))
        (t / Real.sqrt (n + 1 : ℝ)) (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)))
        (signedRatio P n t) y = 0 :=
  influence_contact_at_contamination_maximum P n t
    (contaminationObjective_maximal H P n t hattain hpos)

theorem influence_contact_equation (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hpos : 0 ≤ signedRatio P n t) (x : ℝ) (hx : x ∈ P.measure.support) :
    (n + 1 : ℝ) * (cdf (iidSumLaw P.measure n) (t - x) -
        cdf (iidSumLaw P.measure (n + 1)) t) =
      -Real.sqrt (n + 1 : ℝ) * standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) * x -
      ((t / Real.sqrt (n + 1 : ℝ)) * standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) / 2) *
        (x ^ 2 - 1) +
      signedRatio P n t / Real.sqrt (n + 1 : ℝ) *
        (|x| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * x -
          3 / 2 * thirdMoment P * (x ^ 2 - 1)) := by
  have hc := influence_contact_at_extremizer H P n t hattain hpos x hx
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
  have hs2 : Real.sqrt (n + 1 : ℝ) ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  unfold influenceNumerator at hc
  generalize hφ : standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) = φ at hc ⊢
  generalize hz : t / Real.sqrt (n + 1 : ℝ) = z at hc ⊢
  nth_rw 1 [← hs2]
  apply (mul_left_cancel₀ hs)
  field_simp
  linear_combination 2 * hc

theorem signedSecondMoment_abs_le_one (P : StandardizedLaw) : |signedSecondMoment P| ≤ 1 := by
  have h := norm_integral_le_integral_norm (f := fun x : ℝ => x * |x|) (μ := P.measure)
  have he (x : ℝ) : ‖x * |x|‖ = x ^ 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_abs, ← sq, sq_abs]
  simp_rw [he] at h
  simpa only [Real.norm_eq_abs, P.second_one] using h

end BerryEsseen
