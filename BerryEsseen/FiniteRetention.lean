import BerryEsseen.FiniteLatticeRounding
import BerryEsseen.ManuscriptLatticeCouplings

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def retainedAtoms (μ : Measure ℝ) (F : Finset ℝ) (τ : ℝ) : Finset ℝ := by
  classical
  exact F.filter (fun x => τ ≤ μ.real {x})

def retainedMeasure (μ : Measure ℝ) (F : Finset ℝ) (τ : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond μ (retainedAtoms μ F τ : Set ℝ)

theorem retainedAtoms_subset (μ : Measure ℝ) (F : Finset ℝ) (τ : ℝ) : retainedAtoms μ F τ ⊆ F := by
  classical
  exact Finset.filter_subset _ _

theorem retained_outside_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hF : ∀ᵐ x ∂μ, x ∈ F) :
    μ.real (retainedAtoms μ F τ : Set ℝ)ᶜ ≤ (F.card : ℝ) * τ := by
  classical
  let D := F \ retainedAtoms μ F τ
  have hmass : μ.real (retainedAtoms μ F τ : Set ℝ)ᶜ = μ.real (D : Set ℝ) := by
    apply measureReal_congr
    filter_upwards [hF] with x hx
    apply propext
    change (x ∉ retainedAtoms μ F τ) ↔ x ∈ D
    simp only [D, Finset.mem_sdiff, hx, true_and]
  rw [hmass, ← sum_measureReal_singleton D]
  calc
    (∑ x ∈ D, μ.real {x}) ≤ ∑ _x ∈ D, τ := by
      apply Finset.sum_le_sum
      intro x hx
      have hxF := (Finset.mem_sdiff.mp hx).1
      have hxnot := (Finset.mem_sdiff.mp hx).2
      have hlt : ¬ τ ≤ μ.real {x} := by
        intro h
        exact hxnot (Finset.mem_filter.mpr ⟨hxF, h⟩)
      exact (lt_of_not_ge hlt).le
    _ = (D.card : ℝ) * τ := by simp
    _ ≤ (F.card : ℝ) * τ := by
      apply mul_le_mul_of_nonneg_right _ hτ
      exact_mod_cast (Finset.card_le_card (show D ⊆ F from Finset.sdiff_subset))

theorem retained_mass_nonzero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hF : ∀ᵐ x ∂μ, x ∈ F)
    (hsmall : (F.card : ℝ) * τ < 1) : μ (retainedAtoms μ F τ : Set ℝ) ≠ 0 := by
  have hr := retained_outside_mass μ F τ hτ hF
  have he := probReal_compl_eq_one_sub (retainedAtoms μ F τ).finite_toSet.measurableSet (μ := μ)
  intro hz
  have hzr : μ.real (retainedAtoms μ F τ : Set ℝ) = 0 := by simp [Measure.real, hz]
  linarith

theorem retainedMeasure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hF : ∀ᵐ x ∂μ, x ∈ F)
    (hsmall : (F.card : ℝ) * τ < 1) : IsProbabilityMeasure (retainedMeasure μ F τ) :=
  cond_isProbabilityMeasure (retained_mass_nonzero μ F τ hτ hF hsmall)

theorem retainedMeasure_support (μ : Measure ℝ) (F : Finset ℝ) (τ : ℝ) :
    (retainedMeasure μ F τ).support ⊆ (retainedAtoms μ F τ : Set ℝ) := by
  apply Measure.support_subset_of_isClosed (retainedAtoms μ F τ).finite_toSet.isClosed
  unfold retainedMeasure ProbabilityTheory.cond
  apply Measure.ae_smul_measure
  exact ae_restrict_mem (retainedAtoms μ F τ).finite_toSet.measurableSet

theorem retainedMeasure_atom_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hF : ∀ᵐ x ∂μ, x ∈ F)
    (hsmall : (F.card : ℝ) * τ < 1) (x : ℝ) (hx : x ∈ retainedAtoms μ F τ) :
    τ ≤ (retainedMeasure μ F τ).real {x} := by
  classical
  have hnz := retained_mass_nonzero μ F τ hτ hF hsmall
  have hs : 0 < μ.real (retainedAtoms μ F τ : Set ℝ) := ENNReal.toReal_pos hnz (measure_ne_top _ _)
  have hs1 : μ.real (retainedAtoms μ F τ : Set ℝ) ≤ 1 := measureReal_le_one
  have hraw : τ ≤ μ.real {x} := (Finset.mem_filter.mp hx).2
  have hid : (retainedMeasure μ F τ).real {x} = μ.real {x} / μ.real (retainedAtoms μ F τ : Set ℝ) := by
    unfold retainedMeasure ProbabilityTheory.cond Measure.real
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      Measure.restrict_apply (measurableSet_singleton x)]
    rw [inter_eq_left.mpr (show ({x} : Set ℝ) ⊆ (retainedAtoms μ F τ : Set ℝ) from
      singleton_subset_iff.mpr hx)]
    ring
  rw [hid]
  apply (le_div_iff₀ hs).mpr
  have hm := mul_le_mul_of_nonneg_left hs1 hτ
  linarith

theorem retainedMeasure_bounded (μ : Measure ℝ) (F : Finset ℝ) (τ R : ℝ)
    (hx : ∀ᵐ x ∂μ, |x| ≤ R) : ∀ᵐ x ∂retainedMeasure μ F τ, |x| ≤ R := by
  unfold retainedMeasure ProbabilityTheory.cond
  apply Measure.ae_smul_measure
  exact ae_restrict_of_ae hx

theorem retainedMeasure_wasserstein (K : PublishedWassersteinDuality)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (F : Finset ℝ) (τ R : ℝ)
    (hτ : 0 ≤ τ) (hR : 0 ≤ R) (hF : ∀ᵐ x ∂μ, x ∈ F)
    (hsmall : (F.card : ℝ) * τ < 1) (hx : ∀ᵐ x ∂μ, |x| ≤ R) :
    wassersteinOne μ (retainedMeasure μ F τ) ≤ 2 * R * (F.card : ℝ) * τ := by
  have hi := real_function_integrable_of_abs_le μ (fun x : ℝ => x) R measurable_id hx
  have h := manuscript_wasserstein_conditioning_actual μ (retainedAtoms μ F τ : Set ℝ)
    (retainedAtoms μ F τ).finite_toSet.measurableSet (retained_mass_nonzero μ F τ hτ hF hsmall)
    hi R R hx (retainedMeasure_bounded μ F τ R hx)
  have hm := mul_le_mul_of_nonneg_left (retained_outside_mass μ F τ hτ hF) (show 0 ≤ 2 * R by positivity)
  change wassersteinOne μ (retainedMeasure μ F τ) ≤ _ at h
  nlinarith only [h, hm]

end BerryEsseen
