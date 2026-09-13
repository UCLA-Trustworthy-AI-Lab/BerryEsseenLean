import BerryEsseen.ExtremizerLimit
import BerryEsseen.SignedSecondLimit
import BerryEsseen.ContactAlgebra

/-! Actual contact, limiting support and separation estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def sqrtStepCorrection (x : ℝ) : ℝ := (1 + 1 / x) / (Real.sqrt (1 + 1 / x) + 1)

theorem sqrt_step_correction_identity (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x + 1) ^ 3 / Real.sqrt x = x + 1 + sqrtStepCorrection x := by
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 (by linarith)
  have hr2 := Real.sq_sqrt hx.le
  have hs2 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have he : Real.sqrt (1 + 1 / x) = Real.sqrt (x + 1) / Real.sqrt x := by
    rw [← Real.sqrt_div (by linarith : 0 ≤ x + 1)]
    congr 1
    field_simp
  unfold sqrtStepCorrection
  rw [he]
  have hden : Real.sqrt (x + 1) / Real.sqrt x + 1 ≠ 0 := by positivity
  field_simp [hr.ne', hx.ne', hden]
  linear_combination x * (Real.sqrt (x + 1) ^ 2 + x + 1 + Real.sqrt (x + 1) * Real.sqrt x) * hs2 - (x + 1) ^ 2 * hr2

theorem sqrtStepCorrection_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ sqrtStepCorrection x := by
  unfold sqrtStepCorrection
  positivity

theorem sqrtStepCorrection_tendsto : Tendsto sqrtStepCorrection atTop (𝓝 (1 / 2)) := by
  have hi : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hn : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 1) := by simpa using hi.const_add 1
  have hs : Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x) + 1) atTop (𝓝 2) := by
    simpa only [Real.sqrt_one, show (1 : ℝ) + 1 = 2 by norm_num] using
      (Real.continuous_sqrt.tendsto 1 |>.comp hn).add_const 1
  exact hn.div hs (by norm_num)

theorem violating_extremalConstant_tendsto (H : ClassicalBerryEsseenBounds)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hv : ∀ j, cE < extremalConstant (n j)) :
    Tendsto (fun j => extremalConstant (n j)) atTop (𝓝 cE) := by
  have hh := ((extremalExcess_tendsto_zero H).comp hn).add_const cE
  have he (j : ℕ) : extremalExcess (n j) + cE = extremalConstant (n j) := by
    unfold extremalExcess
    rw [max_eq_left (sub_nonneg.2 (hv j).le)]
    ring
  simpa only [Function.comp_apply, he, zero_add] using hh

/-- The positive recursive error left after the constant cancellation. -/
def contactRecursiveError (n : ℕ) : ℝ :=
  sqrtStepCorrection (n : ℝ) * (cE + 4.75 / Real.sqrt (n : ℝ)) - cE / 2 +
    scaledDrop extremalConstant (n + 1)

theorem contactRecursiveError_tendsto (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0)) :
    Tendsto (fun j => contactRecursiveError (n j)) atTop (𝓝 0) := by
  have hnc : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hc := sqrtStepCorrection_tendsto.comp hnc
  have hs := Real.tendsto_sqrt_atTop.comp hnc
  have hi := hs.const_div_atTop (4.75 : ℝ)
  have he := ((hc.mul (hi.const_add cE)).sub_const (cE / 2)).add hd
  convert he using 1 <;> norm_num [contactRecursiveError, Function.comp_def] <;> ring

theorem contact_recursive_bound (H : ClassicalBerryEsseenBounds) (n : ℕ) (hn : 1 ≤ n)
    (hv : cE ≤ extremalConstant (n + 1)) :
    Real.sqrt (n + 1 : ℝ) ^ 3 / Real.sqrt (n : ℝ) * extremalConstant n -
      (n + 1 : ℝ) * extremalConstant (n + 1) - extremalConstant (n + 1) / 2 ≤ contactRecursiveError n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [sqrt_step_correction_identity (n : ℝ) hnpos]
  have hc := mul_le_mul_of_nonneg_left (extremalConstant_bounds H n hn).2
    (sqrtStepCorrection_nonneg (n : ℝ) hnpos)
  have hd := mul_le_mul_of_nonneg_left (le_max_left (extremalConstant n - extremalConstant (n + 1)) 0)
    (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hdeq : (n + 1 : ℝ) * max (extremalConstant n - extremalConstant (n + 1)) 0 =
      scaledDrop extremalConstant (n + 1) := by
    simp only [scaledDrop, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [hdeq] at hd
  unfold contactRecursiveError
  nlinarith

theorem extremizer_sharp_contact_bound (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (y : ℝ) (hy : y ∈ P.measure.support) :
    0 ≤ gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y +
      thirdMoment P * contactRecursiveError n +
      3 / 2 * extremalConstant (n + 1) * thirdMoment P * y ^ 2 -
      extremalConstant (n + 1) * |y| ^ 3 +
      3 * extremalConstant (n + 1) * signedSecondMoment P * y := by
  have hp : 0 ≤ signedRatio P n t := by rw [hattain]; exact cE_pos.le.trans hv.le
  have hc := influence_contact_at_extremizer H P n t hattain hp y hy
  have hb := influenceNumerator_gaussian_bound H P n hn t y
  rw [hc, hattain] at hb
  have hr := mul_le_mul_of_nonneg_left (contact_recursive_bound H n hn hv.le) (thirdMoment_pos P).le
  nlinarith only [hb, hr]

theorem gaussianHn_moving_limit (n : ℕ → ℕ) (z v : ℕ → ℝ) (y L : ℝ)
    (hn : Tendsto n atTop atTop) (hz : Tendsto z atTop (𝓝 0))
    (hy : Tendsto v atTop (𝓝 y)) (hb : ∀ j, |v j| ≤ L) :
    Tendsto (fun j => gaussianHn (n j) (z j) (v j)) atTop (𝓝 (phi0 / 6 * (y ^ 3 - 3 * y))) := by
  apply (gaussianHn_uniform_limit n z hn hz L).tendsto_comp (by fun_prop)
  exact tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall (fun j => abs_le.1 (hb j))⟩

theorem extremizer_limiting_contact_polynomial (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (v : ℕ → ℝ) (y : ℝ) (hvSupp : ∀ j, v j ∈ (P j).measure.support)
    (hy : Tendsto v atTop (𝓝 y)) : contactPolynomial cStar betaE y ≤ 0 := by
  have hb (j : ℕ) : ∀ᵐ x ∂(P j).measure, |x| ≤ 10 := by
    filter_upwards [(P j).measure.support_mem_ae] with x hx
    exact abs_le.2 (hsupp j hx)
  have hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) := by
    simpa only [thirdMoment_esseen] using bounded_thirdMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 (qE - pE)) := by
    simpa only [signedSecondMoment_esseen] using bounded_signedSecondMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hn' : Tendsto (fun j => n j + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hn
  have hR := violating_extremalConstant_tendsto H (fun j => n j + 1) hn' hv
  have hG := gaussianHn_moving_limit (fun j => n j + 1) _ v y 10 hn' hz hy
    (fun j => abs_le.2 (hsupp j (hvSupp j)))
  have hlim := (((hG.add (hβ.mul (contactRecursiveError_tendsto n hn hd))).add
      (((hR.const_mul (3 / 2)).mul hβ).mul (hy.pow 2))).sub
      (hR.mul (hy.abs.pow 3))).add (((hR.const_mul 3).mul hM).mul hy)
  have hnonneg := ge_of_tendsto hlim (Eventually.of_forall (fun j => by
    simpa only [gaussianHn, Nat.cast_add, Nat.cast_one] using
      extremizer_sharp_contact_bound H (P j) (n j) (hn1 j) (t j) (hattain j) (hv j) (v j) (hvSupp j)))
  apply contact_polynomial_of_limit
  convert hnonneg using 1 <;> ring

theorem esseen_contact_left_root :
    3 * cStar * betaE / (2 * (cStar + 1)) = Real.sqrt 10 / 2 * aE := by
  have hp : (cStar + 1) * pE = 3 := by
    unfold cStar pE
    nlinarith [sqrt10_sq]
  have hc : cStar + 1 ≠ 0 := by linarith [cStar_gt_one]
  rw [show 3 * cStar * betaE = 3 * (cStar * betaE) by ring, beta_identity]
  unfold aE
  field_simp [hc, sigmaE_pos.ne']
  nlinarith only [hp]

theorem esseen_contact_right_root :
    3 * cStar * betaE / (2 * (cStar - 1)) = Real.sqrt 10 / 2 * bE := by
  have hp : (cStar - 1) * qE = 3 := by
    unfold cStar qE pE
    nlinarith [sqrt10_sq]
  have hc : cStar - 1 ≠ 0 := by linarith [cStar_gt_one]
  rw [show 3 * cStar * betaE = 3 * (cStar * betaE) by ring, beta_identity]
  unfold bE
  field_simp [hc, sigmaE_pos.ne']
  nlinarith only [hp]

theorem esseen_contact_polynomial_interval (y : ℝ) (h : contactPolynomial cStar betaE y ≤ 0) :
    y ∈ Icc (-(Real.sqrt 10 / 2 * aE)) (Real.sqrt 10 / 2 * bE) := by
  have hb : 0 ≤ betaE := by rw [← thirdMoment_esseen]; exact (thirdMoment_pos _).le
  have hi := contact_polynomial_interval cStar betaE y cStar_gt_one hb h
  simpa only [esseen_contact_left_root, esseen_contact_right_root] using hi

theorem extremizer_support_limit_interval (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (v : ℕ → ℝ) (y : ℝ) (hvSupp : ∀ j, v j ∈ (P j).measure.support)
    (hy : Tendsto v atTop (𝓝 y)) :
    y ∈ Icc (-(Real.sqrt 10 / 2 * aE)) (Real.sqrt 10 / 2 * bE) :=
  esseen_contact_polynomial_interval y
    (extremizer_limiting_contact_polynomial H P n t hn hn1 hattain hv hd hw hz hsupp v y hvSupp hy)

end BerryEsseen
