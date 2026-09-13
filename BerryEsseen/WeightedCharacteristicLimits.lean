import BerryEsseen.CharacteristicDerivatives
import BerryEsseen.MomentPreservation

/-! Weak convergence of the first two weighted characteristic functions.
The proof uses truncation and third moments, without fourth moments. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

theorem tendsto_of_uniform_integral_approximation
    (x : ℕ → ℂ) (l : ℂ) (a : ℝ → ℕ → ℂ) (b : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hlim : ∀ A : ℝ, 0 < A → Tendsto (a A) atTop (𝓝 (b A)))
    (hx : ∀ A : ℝ, 0 < A → ∀ j, ‖x j - a A j‖ ≤ C / A)
    (hl : ∀ A : ℝ, 0 < A → ‖b A - l‖ ≤ C / A) : Tendsto x atTop (𝓝 l) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let A : ℝ := 1 + 8 * C / ε
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmall : C / A < ε / 4 := by
    apply (div_lt_iff₀ hA).2
    dsimp [A]
    field_simp
    nlinarith
  filter_upwards [(Metric.tendsto_nhds.1 (hlim A hA)) (ε / 2) (by positivity)] with j hj
  rw [dist_eq_norm] at hj ⊢
  have h1 := norm_sub_le_norm_sub_add_norm_sub (x j) (a A j) l
  have h2 := norm_sub_le_norm_sub_add_norm_sub (a A j) (b A) l
  have hxa := hx A hA j
  have hbl := hl A hA
  linarith

def clippedFirstCharBCF (A : ℝ) (hA : 0 ≤ A) (u : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => (clippedReal A x : ℂ) * realPhase u x)
    (by unfold clippedReal realPhase; fun_prop) A (fun x => by
      rw [norm_mul, realPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact clippedReal_abs_le A x hA)

def clippedSecondCharBCF (A u : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => (clippedSquare A x : ℂ) * realPhase u x)
    (by unfold clippedSquare realPhase; fun_prop) (A ^ 2) (fun x => by
      rw [norm_mul, realPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
        clippedSquare, abs_of_nonneg (le_min (sq_nonneg x) (sq_nonneg A))]
      exact min_le_right _ _)

theorem weightedCharFun_first_clip_error (P : StandardizedLaw) (A : ℝ) (hA : 0 < A) (u : ℝ) :
    ‖weightedCharFun P.measure 1 u - ∫ x, clippedFirstCharBCF A hA.le u x ∂P.measure‖ ≤ 1 / A := by
  have hi : Integrable (fun x : ℝ => (x : ℂ) * realPhase u x) P.measure := by
    simpa only [pow_one] using weightedCharFun_integrable P.measure 1
      (by simpa only [pow_one] using P.first_integrable) u
  have hc := (clippedFirstCharBCF A hA.le u).integrable P.measure
  unfold weightedCharFun
  simp only [pow_one]
  rw [← integral_sub hi hc]
  calc
    _ ≤ ∫ x, ‖(x : ℂ) * realPhase u x - clippedFirstCharBCF A hA.le u x‖ ∂P.measure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, x ^ 2 / A ∂P.measure := by
      apply integral_mono (hi.sub hc).norm (P.second_integrable.div_const A)
      intro x
      change ‖(x : ℂ) * realPhase u x - (clippedReal A x : ℂ) * realPhase u x‖ ≤ _
      rw [← sub_mul, norm_mul, realPhase_norm, mul_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      exact clippedReal_error A x hA
    _ = _ := by rw [integral_div, P.second_one]

theorem weightedCharFun_second_clip_error (P : StandardizedLaw) (A : ℝ) (hA : 0 < A) (u : ℝ) :
    ‖weightedCharFun P.measure 2 u - ∫ x, clippedSecondCharBCF A u x ∂P.measure‖ ≤ thirdMoment P / A := by
  have hi := weightedCharFun_integrable P.measure 2 P.second_integrable u
  have hc := (clippedSecondCharBCF A u).integrable P.measure
  rw [weightedCharFun, ← integral_sub hi hc]
  calc
    _ ≤ ∫ x, ‖(x : ℂ) ^ 2 * realPhase u x - clippedSecondCharBCF A u x‖ ∂P.measure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, |x| ^ 3 / A ∂P.measure := by
      apply integral_mono (hi.sub hc).norm (P.third_integrable.div_const A)
      intro x
      change ‖(x : ℂ) ^ 2 * realPhase u x - (clippedSquare A x : ℂ) * realPhase u x‖ ≤ _
      rw [← sub_mul, norm_mul, realPhase_norm, mul_one, ← Complex.ofReal_pow,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (sub_nonneg.2 (min_le_left _ _))]
      exact clippedSquare_error A x hA
    _ = _ := by rw [integral_div]; rfl

theorem weak_weightedCharFun_first (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure)) (u : ℝ) :
    Tendsto (fun j => weightedCharFun (P j).measure 1 u) atTop (𝓝 (weightedCharFun Q.measure 1 u)) := by
  let a : ℝ → ℕ → ℂ := fun A j => ∫ x, (clippedReal A x : ℂ) * realPhase u x ∂(P j).measure
  let b : ℝ → ℂ := fun A => ∫ x, (clippedReal A x : ℂ) * realPhase u x ∂Q.measure
  apply tendsto_of_uniform_integral_approximation _ _ a b 1 (by norm_num)
  · intro A hA
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hw
      (clippedFirstCharBCF A hA.le u)
  · intro A hA j
    exact weightedCharFun_first_clip_error (P j) A hA u
  · intro A hA
    rw [norm_sub_rev]
    exact weightedCharFun_first_clip_error Q A hA u

theorem weak_limit_thirdMoment_bound (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) : thirdMoment Q ≤ B := by
  exact (weak_limit_integrable_moment_bound Q.toProbabilityMeasure
    (fun j => (P j).toProbabilityMeasure) hw (fun x : ℝ => |x| ^ 3)
    (by fun_prop) (fun x => by positivity) B (fun j => (P j).third_integrable) hB).2

theorem weak_weightedCharFun_second (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B) (u : ℝ) :
    Tendsto (fun j => weightedCharFun (P j).measure 2 u) atTop (𝓝 (weightedCharFun Q.measure 2 u)) := by
  have hB0 : 0 ≤ B := (thirdMoment_pos (P 0)).le.trans (hB 0)
  have hQ := weak_limit_thirdMoment_bound P Q hw B hB
  let a : ℝ → ℕ → ℂ := fun A j => ∫ x, clippedSecondCharBCF A u x ∂(P j).measure
  let b : ℝ → ℂ := fun A => ∫ x, clippedSecondCharBCF A u x ∂Q.measure
  apply tendsto_of_uniform_integral_approximation _ _ a b B hB0
  · intro A _
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hw (clippedSecondCharBCF A u)
  · intro A hA j
    exact (weightedCharFun_second_clip_error (P j) A hA u).trans
      (div_le_div_of_nonneg_right (hB j) hA.le)
  · intro A hA
    rw [norm_sub_rev]
    exact (weightedCharFun_second_clip_error Q A hA u).trans
      (div_le_div_of_nonneg_right hQ hA.le)

end BerryEsseen
