import BerryEsseen.BoundedRawStandardization
import BerryEsseen.EffectiveFiniteApproximation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem appendix_retention_tiny : appendixRetention ≤ 1 / (10 : ℝ) ^ 20 := by
  have h := exponential_sixteenth_bound ((10 : ℝ) ^ 20) (100 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have he : Real.exp (-(100 * appendixA)) = appendixRetention := by unfold appendixRetention; congr 1; ring
  rw [he] at h
  linarith

theorem effective_rounded_moment_bounds (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hβ : thirdMoment P ≤ 1.84)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention) :
    |rawMean Q| ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      rawStdDev Q ∈ Icc 0.99 1.01 ∧
      |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention ∧
      |rawThirdAbsoluteMoment Q - thirdMoment P| +
        |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 2 * (10 : ℝ) ^ 9 * appendixRetention ∧
      rawThirdAbsoluteMoment Q ≤ 1.85 ∧
      ∃ Z : StandardizedLaw,
        Z.measure = standardizedMeasure Q (rawMean Q) (rawStdDev Q) ∧
        Z.measure.support ⊆ Icc (-15) 15 ∧ thirdMoment Z < 2 := by
  have hτ := appendix_retention_bounds.1
  have hw : (10 : ℝ) ^ 5 * appendixRetention ∈ Icc 0 1 :=
    ⟨by positivity, appendix_retention_bounds.2.2⟩
  obtain ⟨hm, hv, hρ, hκ⟩ := bounded_transport_moment_errors K P Q _ hw hP hQ hW
  have htiny := appendix_retention_tiny
  have hs0 : 0 ≤ rawStdDev Q := Real.sqrt_nonneg _
  have hslo : 0.99 ≤ rawStdDev Q := by
    by_contra h
    have hlt : rawStdDev Q < 0.99 := lt_of_not_ge h
    have hsq := mul_self_le_mul_self hs0 hlt.le
    nlinarith only [hsq, (abs_le.mp hv).1, htiny]
  have hshi : rawStdDev Q ≤ 1.01 := by
    by_contra h
    have hlt : 1.01 < rawStdDev Q := lt_of_not_ge h
    have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1.01) hlt.le
    nlinarith only [hsq, (abs_le.mp hv).2, htiny]
  have hρbound : rawThirdAbsoluteMoment Q ≤ 1.85 := by
    have hu := (abs_le.mp hρ).2
    nlinarith only [hu, htiny, hβ]
  obtain ⟨Z, hmap⟩ := bounded_raw_standardization Q 13 (by norm_num) hQ (by linarith)
  have hZβ : thirdMoment Z < 2 := by
    have hformula := (raw_moments_of_standardized_representation Q Z (rawMean Q) (rawStdDev Q)
      (by linarith) hmap).2.2
    have hcub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.99) hslo 3
    have hZpos := thirdMoment_pos Z
    by_contra hbad
    have hb : 2 ≤ thirdMoment Z := le_of_not_gt hbad
    have hm := mul_le_mul hcub hb (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ rawStdDev Q ^ 3)
    nlinarith only [hm, hformula, hρbound]
  refine ⟨hm, ⟨hslo, hshi⟩, ?_, ?_, hρbound, Z, hmap, ?_, hZβ⟩
  · nlinarith only [hv, hτ]
  · nlinarith only [hρ, hκ, hτ]
  · exact bounded_raw_standardization_support Q Z hmap hQ (hm.trans hw.2) hslo

end BerryEsseen
