import BerryEsseen.BoundedMomentPerturbation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem bounded_shifted_power_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R m : ℝ) (hR : 0 ≤ R) (hx : ∀ᵐ x ∂μ, |x| ≤ R) (k : ℕ) :
    Integrable (fun x : ℝ => (x - m) ^ k) μ ∧ Integrable (fun x : ℝ => |x - m| ^ k) μ := by
  have hi : Integrable (fun x : ℝ => (x - m) ^ k) μ :=
    real_function_integrable_of_abs_le μ _ ((R + |m|) ^ k) (by fun_prop) (by
      filter_upwards [hx] with x hx
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg (x - m)) ((abs_sub x m).trans (by linarith)) k)
  exact ⟨hi, by simpa only [Real.norm_eq_abs, abs_pow] using hi.norm⟩

theorem bounded_raw_standardization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0 ≤ R) (hx : ∀ᵐ x ∂μ, |x| ≤ R) (hσ : 0 < rawStdDev μ) :
    ∃ Z : StandardizedLaw, Z.measure = standardizedMeasure μ (rawMean μ) (rawStdDev μ) := by
  have h1 := real_function_integrable_of_abs_le μ (fun x : ℝ => x) R measurable_id hx
  have h2 := (bounded_shifted_power_integrable μ R (rawMean μ) hR hx 2).1
  have h3 := (bounded_shifted_power_integrable μ R (rawMean μ) hR hx 3).2
  have hv : (∫ x, (x - rawMean μ) ^ 2 ∂μ) = rawStdDev μ ^ 2 := by
    exact (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (x - rawMean μ)))).symm
  exact ⟨standardizedLaw μ (rawMean μ) (rawStdDev μ) hσ h1 h2 h3 rfl hv, rfl⟩

theorem bounded_raw_standardization_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Z : StandardizedLaw) (hmap : Z.measure = standardizedMeasure μ (rawMean μ) (rawStdDev μ))
    (hμ : ∀ᵐ x ∂μ, |x| ≤ 13) (hm : |rawMean μ| ≤ 1) (hσ : 0.99 ≤ rawStdDev μ) :
    Z.measure.support ⊆ Icc (-15) 15 := by
  apply Measure.support_subset_of_isClosed isClosed_Icc
  rw [hmap, standardizedMeasure]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
  filter_upwards [hμ] with x hx
  change (x - rawMean μ) / rawStdDev μ ∈ Icc (-15) 15
  apply abs_le.mp
  rw [abs_div, abs_of_pos (show 0 < rawStdDev μ by linarith)]
  apply (div_le_iff₀ (show 0 < rawStdDev μ by linarith)).mpr
  have hb : |x - rawMean μ| ≤ 14 := (abs_sub x _).trans (by linarith)
  linarith

end BerryEsseen
