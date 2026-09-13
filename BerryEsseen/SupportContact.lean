import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

/-! The measure-theoretic step from almost-everywhere contact to contact at
EVERY support point. No lower bound on point masses is needed. -/
open MeasureTheory Filter Set
namespace BerryEsseen

theorem ae_zero_of_nonpos_integral_zero (μ : Measure ℝ) (I : ℝ → ℝ)
    (hi : Integrable I μ) (hnonpos : ∀ x, I x ≤ 0)
    (hzero : (∫ x, I x ∂μ) = 0) : I =ᵐ[μ] 0 := by
  have hneg : (∫ x, -I x ∂μ) = 0 := by rw [integral_neg, hzero, neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.2 (hnonpos x)) hi.neg).1 hneg
  filter_upwards [hae] with x hx
  simpa using hx

theorem contact_on_entire_support (μ : Measure ℝ) (I : ℝ → ℝ)
    (hi : Integrable I μ) (hnonpos : ∀ x, I x ≤ 0)
    (hzero : (∫ x, I x ∂μ) = 0) (husc : UpperSemicontinuous I) :
    ∀ x ∈ μ.support, I x = 0 := by
  have hae := ae_zero_of_nonpos_integral_zero μ I hi hnonpos hzero
  have hfull : I ⁻¹' Ici 0 ∈ ae μ := by
    filter_upwards [hae] with x hx
    change 0 ≤ I x
    simpa using le_of_eq hx.symm
  have hsub := Measure.support_subset_of_isClosed (husc.isClosed_preimage 0) hfull
  intro x hx
  exact le_antisymm (hnonpos x) (hsub hx)

end BerryEsseen
