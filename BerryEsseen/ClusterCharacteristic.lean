import BerryEsseen.EffectiveLowFrequency
import BerryEsseen.ClusterNormalization
import BerryEsseen.CharacteristicDerivatives
import BerryEsseen.PhaseConcentration

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem CenteredFourthLaw.charFun_sub_one_quadratic_bound (P : CenteredFourthLaw) (u : ℝ) :
    ‖charFun P.measure u - 1‖ ≤ P.secondMoment * u ^ 2 / 2 := by
  let f := fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1 - (u * x : ℝ) * Complex.I
  have hpoint (x : ℝ) : ‖f x‖ ≤ (u ^ 2 / 2) * x ^ 2 := by
    have h := unitExp_linear_remainder_sharp (u * x)
    convert h using 1 <;> ring
  have hf : Integrable f P.measure := ((P.integrable_pow 2 (by omega)).const_mul (u ^ 2 / 2)).mono' (by dsimp only [f]; fun_prop)
    (ae_of_all _ hpoint)
  have he : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I)) P.measure := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
  have he0 : Integrable (fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1) P.measure := he.sub (integrable_const _)
  have hlin : Integrable (fun x : ℝ => (x : ℂ) * ((u : ℂ) * Complex.I)) P.measure := P.first_integrable.ofReal.mul_const _
  have hfun : f = fun x : ℝ => Complex.exp ((u * x : ℝ) * Complex.I) - 1 - (x : ℂ) * ((u : ℂ) * Complex.I) := by
    funext x
    dsimp only [f]
    push_cast
    ring
  have hmean : (∫ x : ℝ, (x : ℂ) ∂P.measure) = 0 := by
    simpa only [P.mean_zero, Complex.ofReal_zero] using (integral_complex_ofReal (f := fun x : ℝ => x) (μ := P.measure))
  have hint : (∫ x, f x ∂P.measure) = charFun P.measure u - 1 := by
    rw [hfun]
    dsimp only
    rw [integral_sub he0 hlin, integral_sub he (integrable_const _),
      integral_mul_const, hmean, zero_mul, sub_zero]
    simp only [integral_const, probReal_univ, one_smul]
    rw [charFun_apply_real]
    simp only [Complex.ofReal_mul]
  rw [← hint]
  calc
    _ ≤ ∫ x, ‖f x‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (u ^ 2 / 2) * x ^ 2 ∂P.measure := integral_mono hf.norm ((P.integrable_pow 2 (by omega)).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul]; unfold CenteredFourthLaw.secondMoment; ring


theorem CenteredFourthLaw.weightedCharFun_one_bound (P : CenteredFourthLaw) (u : ℝ) :
    ‖weightedCharFun P.measure 1 u‖ ≤ P.secondMoment * |u| := by
  have hmean : (∫ x : ℝ, (x : ℂ) ∂P.measure) = 0 := by
    simpa only [P.mean_zero, Complex.ofReal_zero] using
      (integral_complex_ofReal (f := fun x : ℝ => x) (μ := P.measure))
  let f : ℝ → ℂ := fun x => (x : ℂ) * (realPhase u x - 1)
  have hpoint (x : ℝ) : ‖f x‖ ≤ |u| * x ^ 2 := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := u * x)
    have he : Complex.exp (Complex.I * (u * x : ℝ)) = realPhase u x := by
      unfold realPhase
      congr 1
      push_cast
      ring
    rw [he, Real.norm_eq_abs, abs_mul] at h
    have hm := mul_le_mul_of_nonneg_left h (abs_nonneg x)
    simpa only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      hm.trans_eq (by rw [mul_left_comm, ← sq, sq_abs])
  have hf : Integrable f P.measure := ((P.integrable_pow 2 (by omega)).const_mul |u|).mono'
    (by unfold f realPhase; fun_prop) (ae_of_all _ hpoint)
  have hi := weightedCharFun_integrable P.measure 1 (P.integrable_pow 1 (by omega)) u
  have he : (∫ x, f x ∂P.measure) = weightedCharFun P.measure 1 u := by
    have hfun : f = fun x : ℝ => (x : ℂ) * realPhase u x - (x : ℂ) := by
      funext x
      dsimp [f]
      ring
    rw [hfun, integral_sub (by simpa only [pow_one] using hi) P.first_integrable.ofReal, hmean, sub_zero]
    simp only [weightedCharFun, pow_one]
  rw [← he]
  calc
    _ ≤ ∫ x, ‖f x‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |u| * x ^ 2 ∂P.measure :=
      integral_mono hf.norm ((P.integrable_pow 2 (by omega)).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul]; unfold CenteredFourthLaw.secondMoment; ring

theorem CenteredFourthLaw.weightedCharFun_two_bound (P : CenteredFourthLaw) (u : ℝ) :
    ‖weightedCharFun P.measure 2 u‖ ≤ P.secondMoment := by
  unfold weightedCharFun
  calc
    _ ≤ ∫ x, ‖(x : ℂ) ^ 2 * realPhase u x‖ ∂P.measure := norm_integral_le_integral_norm _
    _ = P.secondMoment := by
      congr 1
      funext x
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, realPhase_norm, mul_one, sq_abs]

def CenteredFourthLaw.cfDerivative (P : CenteredFourthLaw) (u : ℝ) : ℂ :=
  Complex.I * weightedCharFun P.measure 1 u

def CenteredFourthLaw.cfSecondDerivative (P : CenteredFourthLaw) (u : ℝ) : ℂ :=
  -weightedCharFun P.measure 2 u

theorem CenteredFourthLaw.charFun_hasDerivAt (P : CenteredFourthLaw) (u : ℝ) :
    HasDerivAt (charFun P.measure) (P.cfDerivative u) u := by
  have h := weightedCharFun_hasDerivAt P.measure 0 (P.integrable_pow 0 (by omega))
    (P.integrable_pow 1 (by omega)) u
  convert h using 1
  funext t
  exact (weightedCharFun_zero P.measure t).symm

theorem CenteredFourthLaw.cfDerivative_hasDerivAt (P : CenteredFourthLaw) (u : ℝ) :
    HasDerivAt P.cfDerivative (P.cfSecondDerivative u) u := by
  have h := (weightedCharFun_hasDerivAt P.measure 1 (P.integrable_pow 1 (by omega))
    (P.integrable_pow 2 (by omega)) u).const_mul Complex.I
  simpa only [cfDerivative, cfSecondDerivative, ← mul_assoc, Complex.I_mul_I, neg_one_mul] using h

theorem CenteredFourthLaw.cfDerivative_bound (P : CenteredFourthLaw) (u : ℝ) :
    ‖P.cfDerivative u‖ ≤ P.secondMoment * |u| := by
  simpa only [cfDerivative, norm_mul, Complex.norm_I, one_mul] using P.weightedCharFun_one_bound u

theorem CenteredFourthLaw.cfSecondDerivative_bound (P : CenteredFourthLaw) (u : ℝ) :
    ‖P.cfSecondDerivative u‖ ≤ P.secondMoment := by
  simpa only [cfSecondDerivative, norm_neg] using P.weightedCharFun_two_bound u

theorem charFun_mixtureMeasure (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    charFun (mixtureMeasure μ ν p) u =
      ((1 - p : ℝ) : ℂ) * charFun μ u + (p : ℂ) * charFun ν u := by
  rw [charFun_eq_integral_realPhase, mixtureMeasure,
    integral_add_measure ((realPhase_integrable μ u).smul_measure ENNReal.ofReal_ne_top)
      ((realPhase_integrable ν u).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2), Complex.real_smul,
    ← charFun_eq_integral_realPhase]

theorem charFun_twoClusterMeasure (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc 0 1) (u : ℝ) :
    charFun (twoClusterMeasure P Q p) u =
      ((1 - p : ℝ) : ℂ) * charFun P.measure u +
        (p : ℂ) * realPhase u 1 * charFun Q.measure u := by
  letI : IsProbabilityMeasure (Q.measure.map (fun x : ℝ => 1 + x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [twoClusterMeasure, charFun_mixtureMeasure _ _ p hp, charFun_map_const_add]
  simp only [real_inner_comm (1 : ℝ), RCLike.inner_apply, conj_trivial, mul_one,
    realPhase, mul_one]
  ring

def rawBernoulliCF (p u : ℝ) : ℂ := ((1 - p : ℝ) : ℂ) + (p : ℂ) * realPhase u 1

theorem twoCluster_characteristic_difference_bound (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    ‖charFun (twoClusterMeasure P Q p) u - rawBernoulliCF p u‖ ≤
      averageNoiseVariance P Q p * u ^ 2 / 2 := by
  rw [charFun_twoClusterMeasure P Q p hp]
  have he : ((1 - p : ℝ) : ℂ) * charFun P.measure u +
      (p : ℂ) * realPhase u 1 * charFun Q.measure u - rawBernoulliCF p u =
      ((1 - p : ℝ) : ℂ) * (charFun P.measure u - 1) +
      ((p : ℂ) * realPhase u 1) * (charFun Q.measure u - 1) := by
    unfold rawBernoulliCF
    ring
  rw [he]
  have h := norm_add_le (((1 - p : ℝ) : ℂ) * (charFun P.measure u - 1))
    (((p : ℂ) * realPhase u 1) * (charFun Q.measure u - 1))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, realPhase_norm, mul_one,
    abs_of_nonneg hp.1, abs_of_nonneg (sub_nonneg.mpr hp.2)] at h
  have hP := mul_le_mul_of_nonneg_left (P.charFun_sub_one_quadratic_bound u) (sub_nonneg.mpr hp.2)
  have hQ := mul_le_mul_of_nonneg_left (Q.charFun_sub_one_quadratic_bound u) hp.1
  unfold averageNoiseVariance
  nlinarith only [h, hP, hQ]

theorem phase_weighted_sum_norm_le (p u : ℝ) (hp : p ∈ Icc 0 1)
    (z w : ℂ) (A B : ℝ) (hz : ‖z‖ ≤ A) (hw : ‖w‖ ≤ B) :
    ‖((1 - p : ℝ) : ℂ) * z + (p : ℂ) * realPhase u 1 * w‖ ≤ (1 - p) * A + p * B := by
  have h := norm_add_le (((1 - p : ℝ) : ℂ) * z) ((p : ℂ) * realPhase u 1 * w)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, realPhase_norm, mul_one,
    abs_of_nonneg hp.1, abs_of_nonneg (sub_nonneg.mpr hp.2)] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hp.2))
    (mul_le_mul_of_nonneg_left hw hp.1))

theorem CenteredFourthLaw.cfDerivative_bounded (P : CenteredFourthLaw) (ε : ℝ)
    (hb : ∀ᵐ x ∂P.measure, |x| ≤ ε) (u : ℝ) : ‖P.cfDerivative u‖ ≤ ε := by
  rw [cfDerivative, norm_mul, Complex.norm_I, one_mul]
  unfold weightedCharFun
  calc
    _ ≤ ∫ x, ‖(x : ℂ) ^ 1 * realPhase u x‖ ∂P.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ, ε ∂P.measure := by
      apply integral_mono_ae (weightedCharFun_integrable P.measure 1 (P.integrable_pow 1 (by omega)) u).norm
        (integrable_const _)
      filter_upwards [hb] with x hx
      simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, realPhase_norm, mul_one, pow_one] using hx
    _ = ε := by simp

def rawTwoClusterDerivative (P Q : CenteredFourthLaw) (p u : ℝ) : ℂ :=
  ((1 - p : ℝ) : ℂ) * P.cfDerivative u +
    (p : ℂ) * realPhase u 1 * (Complex.I * charFun Q.measure u + Q.cfDerivative u)

def rawTwoClusterSecondDerivative (P Q : CenteredFourthLaw) (p u : ℝ) : ℂ :=
  ((1 - p : ℝ) : ℂ) * P.cfSecondDerivative u +
    (p : ℂ) * realPhase u 1 * (-charFun Q.measure u + 2 * Complex.I * Q.cfDerivative u + Q.cfSecondDerivative u)

def rawBernoulliDerivative (p u : ℝ) : ℂ := (p : ℂ) * realPhase u 1 * Complex.I

def rawBernoulliSecondDerivative (p u : ℝ) : ℂ := -(p : ℂ) * realPhase u 1

theorem rawTwoCluster_hasDerivAt (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc 0 1) (u : ℝ) :
    HasDerivAt (charFun (twoClusterMeasure P Q p)) (rawTwoClusterDerivative P Q p u) u := by
  have h := ((P.charFun_hasDerivAt u).const_mul ((1 - p : ℝ) : ℂ)).add
    (((realPhase_hasDerivAt u 1).const_mul (p : ℂ)).mul (Q.charFun_hasDerivAt u))
  convert h using 1
  · funext t
    exact charFun_twoClusterMeasure P Q p hp t
  · simp only [rawTwoClusterDerivative, Complex.ofReal_one, mul_one]
    ring

theorem rawTwoClusterDerivative_hasDerivAt (P Q : CenteredFourthLaw) (p u : ℝ) :
    HasDerivAt (rawTwoClusterDerivative P Q p) (rawTwoClusterSecondDerivative P Q p u) u := by
  have h := ((P.cfDerivative_hasDerivAt u).const_mul ((1 - p : ℝ) : ℂ)).add
    (((realPhase_hasDerivAt u 1).const_mul (p : ℂ)).mul
      (((Q.charFun_hasDerivAt u).const_mul Complex.I).add (Q.cfDerivative_hasDerivAt u)))
  convert h using 1
  simp only [rawTwoClusterSecondDerivative, Complex.ofReal_one, mul_one, Pi.add_apply]
  linear_combination -(p : ℂ) * realPhase u 1 * charFun Q.measure u * Complex.I_sq

theorem rawBernoulliCF_hasDerivAt (p u : ℝ) :
    HasDerivAt (rawBernoulliCF p) (rawBernoulliDerivative p u) u := by
  convert ((realPhase_hasDerivAt u 1).const_mul (p : ℂ)).const_add ((1 - p : ℝ) : ℂ) using 1
  simp only [rawBernoulliDerivative, Complex.ofReal_one, mul_one]
  ring

theorem rawBernoulliDerivative_hasDerivAt (p u : ℝ) :
    HasDerivAt (rawBernoulliDerivative p) (rawBernoulliSecondDerivative p u) u := by
  convert (((realPhase_hasDerivAt u 1).const_mul (p : ℂ)).mul_const Complex.I) using 1
  simp only [rawBernoulliSecondDerivative, Complex.ofReal_one, mul_one]
  linear_combination -(p : ℂ) * realPhase u 1 * Complex.I_sq

theorem rawBernoulliCF_norm_le (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    ‖rawBernoulliCF p u‖ ≤ 1 := by
  have h := phase_weighted_sum_norm_le p u hp 1 1 1 1 (by simp) (by simp)
  simpa only [rawBernoulliCF, mul_one, sub_add_cancel] using h

theorem rawBernoulliDerivative_norm (p : ℝ) (hp : 0 ≤ p) (u : ℝ) :
    ‖rawBernoulliDerivative p u‖ = p := by
  simp only [rawBernoulliDerivative, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    realPhase_norm, Complex.norm_I, mul_one, abs_of_nonneg hp]

theorem rawBernoulliSecondDerivative_norm (p : ℝ) (hp : 0 ≤ p) (u : ℝ) :
    ‖rawBernoulliSecondDerivative p u‖ = p := by
  simp only [rawBernoulliSecondDerivative, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    realPhase_norm, mul_one, abs_of_nonneg hp]

theorem rawTwoClusterDerivative_norm_le (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc 0 1) (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε)
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) (u : ℝ) :
    ‖rawTwoClusterDerivative P Q p u‖ ≤ p + ε := by
  have h1 : ‖Complex.I * charFun Q.measure u + Q.cfDerivative u‖ ≤ 1 + ε := by
    apply (norm_add_le _ _).trans
    simpa only [norm_mul, Complex.norm_I, one_mul] using
      add_le_add (norm_charFun_le_one (μ := Q.measure) u) (Q.cfDerivative_bounded ε hQ u)
  have h := phase_weighted_sum_norm_le p u hp _ _ ε (1 + ε) (P.cfDerivative_bounded ε hP u) h1
  change ‖rawTwoClusterDerivative P Q p u‖ ≤ _ at h
  convert h using 1 <;> ring

theorem twoCluster_characteristic_derivative_difference (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    ‖rawTwoClusterDerivative P Q p u - rawBernoulliDerivative p u‖ ≤
      averageNoiseVariance P Q p * (|u| + u ^ 2 / 2) := by
  have hQ : ‖Complex.I * (charFun Q.measure u - 1) + Q.cfDerivative u‖ ≤
      Q.secondMoment * (|u| + u ^ 2 / 2) := by
    have h := norm_add_le (Complex.I * (charFun Q.measure u - 1)) (Q.cfDerivative u)
    simp only [norm_mul, Complex.norm_I, one_mul] at h
    nlinarith only [h, Q.charFun_sub_one_quadratic_bound u, Q.cfDerivative_bound u]
  have hP : ‖P.cfDerivative u‖ ≤ P.secondMoment * (|u| + u ^ 2 / 2) :=
    (P.cfDerivative_bound u).trans (by nlinarith [mul_nonneg P.secondMoment_nonneg (sq_nonneg u)])
  have h := phase_weighted_sum_norm_le p u hp _ _ _ _ hP hQ
  have he : rawTwoClusterDerivative P Q p u - rawBernoulliDerivative p u =
      ((1 - p : ℝ) : ℂ) * P.cfDerivative u + (p : ℂ) * realPhase u 1 *
        (Complex.I * (charFun Q.measure u - 1) + Q.cfDerivative u) := by
    unfold rawTwoClusterDerivative rawBernoulliDerivative
    ring
  rw [he]
  convert h using 1
  unfold averageNoiseVariance
  ring

theorem twoCluster_characteristic_second_derivative_difference (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Icc 0 1) (u : ℝ) :
    ‖rawTwoClusterSecondDerivative P Q p u - rawBernoulliSecondDerivative p u‖ ≤
      averageNoiseVariance P Q p * (1 + 2 * |u| + u ^ 2 / 2) := by
  have hQ : ‖-(charFun Q.measure u - 1) + 2 * Complex.I * Q.cfDerivative u + Q.cfSecondDerivative u‖ ≤
      Q.secondMoment * (1 + 2 * |u| + u ^ 2 / 2) := by
    have h := norm_add_le (-(charFun Q.measure u - 1) + 2 * Complex.I * Q.cfDerivative u) (Q.cfSecondDerivative u)
    have h' := norm_add_le (-(charFun Q.measure u - 1)) (2 * Complex.I * Q.cfDerivative u)
    simp only [norm_neg, norm_mul, Complex.norm_I, mul_one] at h'
    rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] at h'
    nlinarith only [h, h', Q.charFun_sub_one_quadratic_bound u, Q.cfDerivative_bound u, Q.cfSecondDerivative_bound u]
  have hP : ‖P.cfSecondDerivative u‖ ≤ P.secondMoment * (1 + 2 * |u| + u ^ 2 / 2) :=
    (P.cfSecondDerivative_bound u).trans (by nlinarith [mul_nonneg P.secondMoment_nonneg (sq_nonneg u), mul_nonneg P.secondMoment_nonneg (abs_nonneg u)])
  have h := phase_weighted_sum_norm_le p u hp _ _ _ _ hP hQ
  have he : rawTwoClusterSecondDerivative P Q p u - rawBernoulliSecondDerivative p u =
      ((1 - p : ℝ) : ℂ) * P.cfSecondDerivative u + (p : ℂ) * realPhase u 1 *
        (-(charFun Q.measure u - 1) + 2 * Complex.I * Q.cfDerivative u + Q.cfSecondDerivative u) := by
    unfold rawTwoClusterSecondDerivative rawBernoulliSecondDerivative
    ring
  rw [he]
  convert h using 1
  unfold averageNoiseVariance
  ring

end BerryEsseen
