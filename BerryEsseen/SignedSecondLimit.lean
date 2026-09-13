import BerryEsseen.EsseenLaw
import BerryEsseen.BoundedMomentLimits

/-! The signed second moment appearing in the actual contact equation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

def clippedSignedSecondBCF (A : ℝ) (hA : 0 ≤ A) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => clippedReal A x * |clippedReal A x|)
    (by unfold clippedReal; fun_prop) (A ^ 2) (fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_abs, ← sq]
      exact pow_le_pow_left₀ (abs_nonneg _) (clippedReal_abs_le A x hA) 2)

theorem bounded_signedSecondMoment_tendsto (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ A) :
    Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 (signedSecondMoment Q)) := by
  have hQ := bounded_support_weak_limit P Q hw A hb
  have he (R : StandardizedLaw) (hR : ∀ᵐ x ∂R.measure, |x| ≤ A) :
      (∫ x, clippedSignedSecondBCF A hA x ∂R.measure) = signedSecondMoment R := by
    apply integral_congr_ae
    filter_upwards [hR] with x hx
    change clippedReal A x * |clippedReal A x| = x * |x|
    rw [clippedReal_eq_self_of_abs_le A x hx]
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw (clippedSignedSecondBCF A hA)
  change Tendsto (fun j => ∫ x, clippedSignedSecondBCF A hA x ∂(P j).measure) atTop
    (𝓝 (∫ x, clippedSignedSecondBCF A hA x ∂Q.measure)) at hh
  simpa only [he Q hQ, he _ (hb _)] using hh

theorem signedSecondMoment_esseen : signedSecondMoment esseenLaw = qE - pE := by
  change (∫ x, x * |x| ∂esseenMeasure) = qE - pE
  rw [integral_esseen, abs_neg, abs_of_pos aE_pos, abs_of_pos bE_pos]
  unfold aE bE
  field_simp [sigmaE_pos.ne']
  rw [sigmaE_sq]
  ring

end BerryEsseen
