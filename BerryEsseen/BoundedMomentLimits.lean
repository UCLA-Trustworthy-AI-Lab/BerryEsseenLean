import BerryEsseen.WeightedCharacteristicLimits

/-! Weak limits of the bounded extremizers retain both third moments exactly. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

theorem bounded_support_weak_limit (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (A : ℝ) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ A) :
    ∀ᵐ x ∂Q.measure, |x| ≤ A := by
  let K := {x : ℝ | |x| ≤ A}
  have hK : IsClosed K := isClosed_le continuous_abs continuous_const
  have hmass : ∀ j, (P j).measure K = 1 := fun j => (mem_ae_iff_prob_eq_one hK.measurableSet).1 (hb j)
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hw hK
  change atTop.limsup (fun j => (P j).measure K) ≤ Q.measure K at hlim
  simp only [hmass, limsup_const] at hlim
  exact (mem_ae_iff_prob_eq_one hK.measurableSet).2 (le_antisymm prob_le_one hlim)

theorem clippedReal_eq_self_of_abs_le (A x : ℝ) (hx : |x| ≤ A) : clippedReal A x = x := by
  unfold clippedReal
  rw [min_eq_left (abs_le.1 hx).2, max_eq_right (abs_le.1 hx).1]

def clippedThirdBCF (A : ℝ) (hA : 0 ≤ A) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (clippedReal A x) ^ 3)
    (by unfold clippedReal; fun_prop) (A ^ 3) (fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (clippedReal_abs_le A x hA) 3)

def clippedAbsThirdBCF (A : ℝ) (hA : 0 ≤ A) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => |clippedReal A x| ^ 3)
    (by unfold clippedReal; fun_prop) (A ^ 3) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (clippedReal_abs_le A x hA) 3)

theorem bounded_signedThirdMoment_tendsto (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ A) :
    Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 (signedThirdMoment Q)) := by
  have hQ := bounded_support_weak_limit P Q hw A hb
  have he (R : StandardizedLaw) (hR : ∀ᵐ x ∂R.measure, |x| ≤ A) :
      (∫ x, clippedThirdBCF A hA x ∂R.measure) = signedThirdMoment R := by
    apply integral_congr_ae
    filter_upwards [hR] with x hx
    change (clippedReal A x) ^ 3 = x ^ 3
    rw [clippedReal_eq_self_of_abs_le A x hx]
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw (clippedThirdBCF A hA)
  change Tendsto (fun j => ∫ x, clippedThirdBCF A hA x ∂(P j).measure) atTop
    (𝓝 (∫ x, clippedThirdBCF A hA x ∂Q.measure)) at hh
  simpa only [he Q hQ, he _ (hb _)] using hh

theorem bounded_thirdMoment_tendsto (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ A) :
    Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)) := by
  have hQ := bounded_support_weak_limit P Q hw A hb
  have he (R : StandardizedLaw) (hR : ∀ᵐ x ∂R.measure, |x| ≤ A) :
      (∫ x, clippedAbsThirdBCF A hA x ∂R.measure) = thirdMoment R := by
    apply integral_congr_ae
    filter_upwards [hR] with x hx
    change |clippedReal A x| ^ 3 = |x| ^ 3
    rw [clippedReal_eq_self_of_abs_le A x hx]
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw (clippedAbsThirdBCF A hA)
  change Tendsto (fun j => ∫ x, clippedAbsThirdBCF A hA x ∂(P j).measure) atTop
    (𝓝 (∫ x, clippedAbsThirdBCF A hA x ∂Q.measure)) at hh
  simpa only [he Q hQ, he _ (hb _)] using hh

end BerryEsseen
