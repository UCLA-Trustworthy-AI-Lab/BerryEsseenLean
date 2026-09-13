import BerryEsseen.ContaminationMoments
import BerryEsseen.ConvolutionContact

/-! Affine standardization of actual measures and their finite sum laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BerryEsseen

def standardizedMeasure (μ : Measure ℝ) (m σ : ℝ) : Measure ℝ :=
  μ.map (fun x => (x - m) / σ)

instance standardizedMeasure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ : ℝ) : IsProbabilityMeasure (standardizedMeasure μ m σ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem standardizedMeasure_first_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ : ℝ) (hi : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun x : ℝ => x) (standardizedMeasure μ m σ) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  exact (hi.sub (integrable_const m)).div_const σ

theorem standardizedMeasure_second_integrable (μ : Measure ℝ) (m σ : ℝ)
    (hi : Integrable (fun x : ℝ => (x - m) ^ 2) μ) :
    Integrable (fun x : ℝ => x ^ 2) (standardizedMeasure μ m σ) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  simpa only [Function.comp_def, div_pow] using hi.div_const (σ ^ 2)

theorem standardizedMeasure_third_integrable (μ : Measure ℝ) (m σ : ℝ)
    (hi : Integrable (fun x : ℝ => |x - m| ^ 3) μ) :
    Integrable (fun x : ℝ => |x| ^ 3) (standardizedMeasure μ m σ) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  simpa only [Function.comp_def, abs_div, div_pow] using hi.div_const (|σ| ^ 3)

theorem standardizedMeasure_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ : ℝ) (hi : Integrable (fun x : ℝ => x) μ) (hm : (∫ x, x ∂μ) = m) :
    (∫ x, x ∂standardizedMeasure μ m σ) = 0 := by
  rw [standardizedMeasure, integral_map (by fun_prop) (by fun_prop), integral_div,
    integral_sub hi (integrable_const m), hm]
  simp

theorem standardizedMeasure_second (μ : Measure ℝ) (m σ : ℝ) (hσ : σ ≠ 0)
    (hv : (∫ x, (x - m) ^ 2 ∂μ) = σ ^ 2) :
    (∫ x, x ^ 2 ∂standardizedMeasure μ m σ) = 1 := by
  rw [standardizedMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [div_pow]
  rw [integral_div, hv, div_self (pow_ne_zero _ hσ)]

theorem standardizedMeasure_third (μ : Measure ℝ) (m σ : ℝ) (hσ : 0 ≤ σ) :
    (∫ x, |x| ^ 3 ∂standardizedMeasure μ m σ) = (∫ x, |x - m| ^ 3 ∂μ) / σ ^ 3 := by
  rw [standardizedMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_div, div_pow, abs_of_nonneg hσ]
  exact integral_div _ _

def standardizedLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (m σ : ℝ)
    (hσ : 0 < σ) (h1 : Integrable (fun x : ℝ => x) μ)
    (h2 : Integrable (fun x : ℝ => (x - m) ^ 2) μ)
    (h3 : Integrable (fun x : ℝ => |x - m| ^ 3) μ)
    (hm : (∫ x, x ∂μ) = m) (hv : (∫ x, (x - m) ^ 2 ∂μ) = σ ^ 2) : StandardizedLaw where
  measure := standardizedMeasure μ m σ
  probability := inferInstance
  first_integrable := standardizedMeasure_first_integrable μ m σ h1
  second_integrable := standardizedMeasure_second_integrable μ m σ h2
  third_integrable := standardizedMeasure_third_integrable μ m σ h3
  mean_zero := standardizedMeasure_mean μ m σ h1 hm
  second_one := standardizedMeasure_second μ m σ hσ.ne' hv

theorem iidSumLaw_standardizedMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ : ℝ) (n : ℕ) :
    iidSumLaw (standardizedMeasure μ m σ) n =
      (iidSumLaw μ n).map (fun x => (x - (n : ℝ) * m) / σ) := by
  induction n with
  | zero =>
    simp only [iidSumLaw, Nat.cast_zero, zero_mul, sub_zero]
    rw [Measure.map_dirac (by fun_prop)]
    simp
  | succ n ih =>
    rw [iidSumLaw, ih, standardizedMeasure, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop), iidSumLaw,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    rcases x with ⟨x₁, x₂⟩
    dsimp
    push_cast
    ring

theorem standardized_sum_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m σ : ℝ) (hσ : 0 < σ) (n : ℕ) (t : ℝ) :
    cdf (iidSumLaw (standardizedMeasure μ m σ) n) ((t - (n : ℝ) * m) / σ) =
      cdf (iidSumLaw μ n) t := by
  rw [cdf_eq_real, cdf_eq_real, iidSumLaw_standardizedMeasure]
  change (((iidSumLaw μ n).map (fun x => (x - (n : ℝ) * m) / σ))
    (Iic ((t - (n : ℝ) * m) / σ))).toReal = _
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_preimage, mem_Iic, div_le_div_iff_of_pos_right hσ, sub_le_sub_iff_right]

theorem integrable_contaminatedMeasure (P : StandardizedLaw) (y e : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f P.measure) :
    Integrable f (contaminatedMeasure P y e) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

theorem contaminatedVariance_pos (P : StandardizedLaw) (y : ℝ)
    {e : ℝ} (he : e ∈ Ico 0 1) : 0 < contaminatedVariance P y e := by
  rw [contaminated_variance_formula P y ⟨he.1, he.2.le⟩]
  have he0 := he.1
  have hp : 0 < (1 - e) * (1 + e * y ^ 2) :=
    mul_pos (sub_pos.2 he.2) (by positivity)
  nlinarith

def standardizedContamination (P : StandardizedLaw) (y e : ℝ) (he : e ∈ Ico 0 1) :
    StandardizedLaw := by
  letI := contaminatedMeasure_probability P y ⟨he.1, he.2.le⟩
  refine standardizedLaw (contaminatedMeasure P y e) (e * y)
    (Real.sqrt (contaminatedVariance P y e))
    (Real.sqrt_pos.2 (contaminatedVariance_pos P y he))
    (integrable_contaminatedMeasure P y e P.first_integrable)
    (integrable_contaminatedMeasure P y e (shifted_second_integrable P (e * y)))
    (integrable_contaminatedMeasure P y e (shifted_abs_cube_integrable P (e * y)))
    (contaminated_mean P y ⟨he.1, he.2.le⟩) ?_
  rw [Real.sq_sqrt (contaminatedVariance_pos P y he).le]
  unfold contaminatedVariance
  rw [contaminated_mean P y ⟨he.1, he.2.le⟩]

theorem standardizedContamination_measure (P : StandardizedLaw) (y e : ℝ)
    (he : e ∈ Ico 0 1) :
    (standardizedContamination P y e he).measure =
      standardizedMeasure (contaminatedMeasure P y e) (e * y)
        (Real.sqrt (contaminatedVariance P y e)) := rfl

theorem standardizedContamination_third (P : StandardizedLaw) (y e : ℝ)
    (he : e ∈ Ico 0 1) :
    thirdMoment (standardizedContamination P y e he) =
      contaminatedThird P y e / Real.sqrt (contaminatedVariance P y e) ^ 3 := by
  change (∫ x, |x| ^ 3 ∂standardizedMeasure _ _ _) = _
  rw [standardizedMeasure_third _ _ _ (Real.sqrt_nonneg _)]
  unfold contaminatedThird
  rw [contaminated_mean P y ⟨he.1, he.2.le⟩]

end BerryEsseen
