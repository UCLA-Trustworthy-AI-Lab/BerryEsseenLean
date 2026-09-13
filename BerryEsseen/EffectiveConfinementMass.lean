import BerryEsseen.EffectiveIntervals

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- A law concentrated near zero and one has its upper-cluster mass within the
cluster radius of its mean. -/
theorem two_interval_mass_deviation_from_mean (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ζ m : ℝ) (hζ : ζ < 1 / 2) (hi : Integrable (fun x : ℝ => x) μ)
    (hm : (∫ x, x ∂μ) = m)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |μ.real (Icc (1 - ζ) (1 + ζ)) - m| ≤ ζ := by
  let A := Icc (1 - ζ) (1 + ζ)
  let b : ℝ → ℝ := A.indicator (fun _ => 1)
  have hA : MeasurableSet A := measurableSet_Icc
  have hbi : Integrable b μ := (integrable_const 1).indicator hA
  have hbeq : (∫ x, b x ∂μ) = μ.real A := integral_indicator_one hA
  have hpoint : ∀ᵐ x ∂μ, ‖b x - x‖ ≤ ζ := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs]
    rcases hx with hx | hx
    · have hxA : x ∉ A := by
        intro h
        have := h.1
        linarith [hx.2]
      simp only [b, indicator_of_notMem hxA, zero_sub, abs_neg]
      exact abs_le.mpr hx
    · have hxA : x ∈ A := hx
      simp only [b, indicator_of_mem hxA]
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2]
  have hint := norm_integral_le_of_norm_le_const hpoint
  rw [integral_sub hbi hi, hbeq, hm, Real.norm_eq_abs, probReal_univ, mul_one] at hint
  exact hint

theorem two_interval_mass_deviation_from_mean_support
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ζ m : ℝ) (hζ : ζ < 1 / 2) (hi : Integrable (fun x : ℝ => x) μ)
    (hm : (∫ x, x ∂μ) = m)
    (hb : μ.support ⊆ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |μ.real (Icc (1 - ζ) (1 + ζ)) - m| ≤ ζ := by
  apply two_interval_mass_deviation_from_mean μ ζ m hζ hi hm
  filter_upwards [μ.support_mem_ae] with x hx
  exact hb hx

theorem confinement_affine_first_integrable (P : StandardizedLaw) (a b : ℝ) :
    Integrable (fun x : ℝ => x) (P.measure.map (fun x => a + b * x)) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  exact (integrable_const a).add (P.first_integrable.const_mul b)

theorem confinement_affine_mean (P : StandardizedLaw) (a b : ℝ) :
    (∫ x, x ∂P.measure.map (fun x => a + b * x)) = a := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_add (integrable_const a) (P.first_integrable.const_mul b),
    integral_const_mul, P.mean_zero]
  simp

theorem confinement_affine_intervals_ae (P : StandardizedLaw) (a b ζ : ℝ)
    (hb : ∀ x ∈ P.measure.support,
      a + b * x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    ∀ᵐ x ∂P.measure.map (fun x => a + b * x),
      x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ) := by
  apply (ae_map_iff (by fun_prop) (measurableSet_Icc.union measurableSet_Icc)).2
  filter_upwards [P.measure.support_mem_ae] with x hx
  exact hb x hx

theorem confinement_affine_intervals_support (P : StandardizedLaw) (a b ζ : ℝ)
    (hb : ∀ x ∈ P.measure.support,
      a + b * x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    (P.measure.map (fun x => a + b * x)).support ⊆
      Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ) := by
  apply Measure.support_subset_of_isClosed (isClosed_Icc.union isClosed_Icc)
  exact confinement_affine_intervals_ae P a b ζ hb

theorem confinement_affine_upper_mass (P : StandardizedLaw) (a b ζ : ℝ)
    (hζ : ζ < 1 / 2)
    (hb : ∀ x ∈ P.measure.support,
      a + b * x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |(P.measure.map (fun x => a + b * x)).real (Icc (1 - ζ) (1 + ζ)) - a| ≤ ζ := by
  letI : IsProbabilityMeasure (P.measure.map (fun x => a + b * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact two_interval_mass_deviation_from_mean _ ζ a hζ
    (confinement_affine_first_integrable P a b) (confinement_affine_mean P a b)
    (confinement_affine_intervals_ae P a b ζ hb)

theorem confinement_esseen_affine_upper_mass (P : StandardizedLaw) (ζ : ℝ)
    (hζ : ζ < 1 / 2)
    (hb : ∀ x ∈ P.measure.support,
      pE + sigmaE * x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |(P.measure.map (fun x => pE + sigmaE * x)).real
      (Icc (1 - ζ) (1 + ζ)) - pE| ≤ ζ :=
  confinement_affine_upper_mass P pE sigmaE ζ hζ hb

theorem confinement_affine_upper_half_mass (P : StandardizedLaw) (a b ζ : ℝ)
    (hζ : ζ < 1 / 2)
    (hb : ∀ x ∈ P.measure.support,
      a + b * x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |(P.measure.map (fun x => a + b * x)).real (Ioi (1 / 2)) - a| ≤ ζ := by
  rw [upper_interval_mass_eq _ ζ hζ (confinement_affine_intervals_ae P a b ζ hb)]
  exact confinement_affine_upper_mass P a b ζ hζ hb

theorem confinement_esseen_affine_upper_half_mass (P : StandardizedLaw) (ζ : ℝ)
    (hζ : ζ < 1 / 2)
    (hb : ∀ x ∈ P.measure.support,
      pE + sigmaE * x ∈ Icc (-ζ) ζ ∪ Icc (1 - ζ) (1 + ζ)) :
    |(P.measure.map (fun x => pE + sigmaE * x)).real (Ioi (1 / 2)) - pE| ≤ ζ :=
  confinement_affine_upper_half_mass P pE sigmaE ζ hζ hb

theorem confinement_esseen_affine_half_eta_mass (P : StandardizedLaw)
    (hb : ∀ x ∈ P.measure.support,
      pE + sigmaE * x ∈ Icc (- (appendixEtaStar / 2)) (appendixEtaStar / 2) ∪
        Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2)) :
    |(P.measure.map (fun x => pE + sigmaE * x)).real (Ioi (1 / 2)) - pE| <
      appendixEtaStar := by
  have hη := appendixEtaStar_bounds.1
  have h := confinement_esseen_affine_upper_half_mass P (appendixEtaStar / 2)
    (by linarith [hη.2]) hb
  linarith [hη.1]

end BerryEsseen
