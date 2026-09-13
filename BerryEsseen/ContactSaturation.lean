import BerryEsseen.ManuscriptContactEstimates

/-! Actual contact, limiting support and separation estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def contactCorrection (P : StandardizedLaw) (n : ℕ) (t y : ℝ) : ℝ :=
  gaussianH (Real.sqrt (n + 1 : ℝ)) (t / Real.sqrt (n + 1 : ℝ)) y +
    3 / 2 * signedRatio P n t * thirdMoment P * (y ^ 2 - 1) -
    signedRatio P n t * (|y| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * y)

theorem contact_scaled_cdf_exact (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (y : ℝ) (hy : y ∈ P.measure.support) :
    Real.sqrt (n + 1 : ℝ) * (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - y) -
      normalCDF ((t - y) / Real.sqrt (n : ℝ))) =
        signedRatio P n t * thirdMoment P - contactCorrection P n t y / (n + 1 : ℝ) := by
  have hp : 0 ≤ signedRatio P n t := by rw [hattain]; exact cE_pos.le.trans hv.le
  have hc := influence_contact_at_extremizer H P n t hattain hp y hy
  have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have hF : Real.sqrt (n + 1 : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw P.measure (n + 1)) t - normalCDF (t / Real.sqrt (n + 1 : ℝ))) =
        signedRatio P n t * thirdMoment P := by
    unfold signedRatio
    field_simp [(thirdMoment_pos P).ne']
  unfold influenceNumerator at hc
  unfold contactCorrection gaussianH
  rw [gaussian_predecessor_argument n hn t y]
  have hnz : (n + 1 : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hnz)
  conv_rhs => rw [mul_sub, mul_div_cancel₀ _ hnz]
  linear_combination hc + Real.sqrt (n + 1 : ℝ) ^ 2 * hF +
    (signedRatio P n t * thirdMoment P - Real.sqrt (n + 1 : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - y) -
        normalCDF ((t - y) / Real.sqrt (n : ℝ)))) * hs2

theorem esseen_resonance_multiplier_zero (r : ℝ) (hr : r ≠ 0)
    (hres : r ∈ resonanceSubgroup esseenLaw.measure) : Real.sinc (hE * r / 2) = 0 := by
  have ha : -aE ∈ esseenLaw.measure.support := by change -aE ∈ esseenMeasure.support; rw [esseen_support]; simp
  have hb : bE ∈ esseenLaw.measure.support := by change bE ∈ esseenMeasure.support; rw [esseen_support]; simp
  obtain ⟨k, hk⟩ := resonance_support_difference esseenLaw.measure r hres bE (-aE) hb ha
  have he : r * hE = 2 * Real.pi * (k : ℝ) := by
    rw [← span_identity]
    convert hk using 1 <;> ring
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, mul_zero] at he
    exact (mul_ne_zero hr hE_pos.ne') he
  have he' : r = 2 * Real.pi * (k : ℝ) / hE := (eq_div_iff hE_pos.ne').2 he
  rw [he']
  exact spanJitter_multiplier_resonance_zero hE hE_pos k hk0

theorem sqrt_successor_ratio_tendsto (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hn1 : ∀ j, 1 ≤ n j) :
    Tendsto (fun j => Real.sqrt (n j + 1 : ℝ) / Real.sqrt (n j : ℝ)) atTop (𝓝 1) := by
  have hnc : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hi := hnc.const_div_atTop (1 : ℝ)
  have hs := (Real.continuous_sqrt.tendsto 1).comp (by simpa only [add_zero] using hi.const_add 1)
  have he (j : ℕ) : Real.sqrt (n j + 1 : ℝ) / Real.sqrt (n j : ℝ) = Real.sqrt (1 + 1 / (n j : ℝ)) := by
    have hnj : (n j : ℝ) ≠ 0 := by exact_mod_cast (show n j ≠ 0 by have := hn1 j; omega)
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  change Tendsto (fun j => Real.sqrt (1 + 1 / (n j : ℝ))) atTop (𝓝 (Real.sqrt 1)) at hs
  simpa only [← he, Real.sqrt_one] using hs

theorem sqrt_predecessor_ratio_tendsto (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hn1 : ∀ j, 1 ≤ n j) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using (sqrt_successor_ratio_tendsto n hn hn1).inv₀ (by norm_num)

theorem contactCorrection_tendsto
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t v : ℕ → ℝ) (y β M R L : ℝ)
    (hn : Tendsto n atTop atTop)
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hy : Tendsto v atTop (𝓝 y)) (hb : ∀ j, |v j| ≤ L)
    (hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 β))
    (hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 M))
    (hR : Tendsto (fun j => signedRatio (P j) (n j) (t j)) atTop (𝓝 R)) :
    Tendsto (fun j => contactCorrection (P j) (n j) (t j) (v j)) atTop
      (𝓝 (phi0 / 6 * (y ^ 3 - 3 * y) + 3 / 2 * R * β * (y ^ 2 - 1) - R * (|y| ^ 3 - β - 3 * M * y))) := by
  have hn' : Tendsto (fun j => n j + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hn
  have hg := gaussianHn_moving_limit (fun j => n j + 1) _ v y L hn' hz hy hb
  have he := (hg.add (((hR.const_mul (3 / 2)).mul hβ).mul ((hy.pow 2).sub_const 1))).sub
    (hR.mul (((hy.abs.pow 3).sub hβ).sub ((hM.const_mul 3).mul hy)))
  simpa only [contactCorrection, gaussianHn, Nat.cast_add, Nat.cast_one] using he

/-- Subtract the two manuscript first-order estimates. This is uniform
on the entire support and uses neither the full H limit nor convergence
of the chosen support point. -/
theorem manuscript_contact_saturation_error (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (v L : ℝ)
    (hvsupp : v ∈ P.measure.support) (hvL : |v| ≤ L) :
    |Real.sqrt (n + 1 : ℝ) * (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - v) -
        normalCDF ((t - v) / Real.sqrt (n : ℝ))) - signedRatio P n t * thirdMoment P| ≤
      (manuscriptContactFirstConstant L + manuscriptNormalFirstConstant L) /
        Real.sqrt (n + 1 : ℝ) := by
  let s := Real.sqrt (n + 1 : ℝ)
  let z := t / s
  let A := ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - v) -
    ProbabilityTheory.cdf (iidSumLaw P.measure (n + 1)) t + standardNormalDensity z * v / s
  let B := normalCDF ((t - v) / Real.sqrt (n : ℝ)) - normalCDF z + standardNormalDensity z * v / s
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hA : |A| ≤ manuscriptContactFirstConstant L / (n + 1 : ℝ) :=
    manuscript_contact_first_order H P n hn t hattain hv v L hvsupp hvL
  have hB : |B| ≤ manuscriptNormalFirstConstant L / (n + 1 : ℝ) := by
    have hb := manuscript_normal_first_order n hn (t / Real.sqrt (n + 1 : ℝ)) v L hvL
    rw [gaussian_predecessor_argument n hn t v] at hb
    exact hb
  have hF : s * (ProbabilityTheory.cdf (iidSumLaw P.measure (n + 1)) t - normalCDF z) =
      signedRatio P n t * thirdMoment P := by
    unfold signedRatio
    dsimp [s, z]
    field_simp [(thirdMoment_pos P).ne']
  have he : s * (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - v) -
      normalCDF ((t - v) / Real.sqrt (n : ℝ))) - signedRatio P n t * thirdMoment P = s * (A - B) := by
    rw [← hF]
    dsimp [A, B]
    ring
  rw [show Real.sqrt (n + 1 : ℝ) = s from rfl, he, abs_mul, abs_of_pos hs]
  have hb := mul_le_mul_of_nonneg_left ((abs_sub A B).trans (add_le_add hA hB)) hs.le
  apply hb.trans_eq
  rw [← hs2]
  field_simp [hs.ne']
  <;> ring

/-- The original contact saturation proof: the two uniform O(1/n)
remainders cancel their common linear term and vanish after multiplication
by sqrt(n). The full Gaussian H limit is not used. -/
theorem contact_previous_discrepancy_tendsto (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t v : ℕ → ℝ) (y β M R L : ℝ)
    (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hy : Tendsto v atTop (𝓝 y)) (hb : ∀ j, |v j| ≤ L)
    (hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 β))
    (hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 M))
    (hR : Tendsto (fun j => signedRatio (P j) (n j) (t j)) atTop (𝓝 R))
    (hvsupp : ∀ j, v j ∈ (P j).measure.support) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j)) (t j - v j) -
        normalCDF ((t j - v j) / Real.sqrt (n j : ℝ)))) atTop (𝓝 (R * β)) := by
  have hnc : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hden : Tendsto (fun j => Real.sqrt (n j + 1 : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hnc.atTop_add tendsto_const_nhds)
  have herr : Tendsto (fun j => Real.sqrt (n j + 1 : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j)) (t j - v j) -
        normalCDF ((t j - v j) / Real.sqrt (n j : ℝ))) -
      signedRatio (P j) (n j) (t j) * thirdMoment (P j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_)
      (hden.const_div_atTop (manuscriptContactFirstConstant L + manuscriptNormalFirstConstant L))
    rw [Real.norm_eq_abs]
    exact manuscript_contact_saturation_error H (P j) (n j) (hn1 j) (t j)
      (hattain j) (hv j) (v j) L (hvsupp j) (hb j)
  have hs : Tendsto (fun j => Real.sqrt (n j + 1 : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j)) (t j - v j) -
        normalCDF ((t j - v j) / Real.sqrt (n j : ℝ)))) atTop (𝓝 (R * β)) := by
    simpa only [sub_add_cancel, zero_add] using herr.add (hR.mul hβ)
  have hout := (sqrt_predecessor_ratio_tendsto n hn hn1).mul hs
  simp only [one_mul] at hout
  convert hout using 1
  funext j
  have hsn : Real.sqrt (n j + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hsn]


theorem predecessor_threshold_tendsto_zero
    (n : ℕ → ℕ) (t v : ℕ → ℝ) (y : ℝ)
    (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hy : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun j => (t j - v j) / Real.sqrt (n j : ℝ)) atTop (𝓝 0) := by
  have hnc : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hden : Tendsto (fun j => Real.sqrt (n j + 1 : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hnc.atTop_add tendsto_const_nhds)
  have hh := (sqrt_successor_ratio_tendsto n hn hn1).mul (hz.sub (hy.div_atTop hden))
  simp only [sub_self, mul_zero] at hh
  convert hh using 1
  funext j
  have hsn : Real.sqrt (n j + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hsn]

theorem normalized_jitter_cdf_as_raw (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (h x : ℝ) :
    ((normalizedJitteredSumLaw P n h) (Iic x)).toReal =
      ProbabilityTheory.cdf (iidSumLaw P.measure n ∗ spanJitter h) (Real.sqrt (n : ℝ) * x) := by
  letI := spanJitter_probability h
  letI := normalizedJitteredSumLaw_probability P n h
  change (normalizedJitteredSumLaw P n h).real (Iic x) = _
  rw [← ProbabilityTheory.cdf_eq_real]
  unfold normalizedJitteredSumLaw
  exact cdf_map_div_positive _ _ (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))) x

theorem jitter_shifted_discrepancy_tendsto (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (w : ℕ → ℝ) (hw0 : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j) ∗ uniformJitter hE)
        (Real.sqrt (n j : ℝ) * w j + hE / 2) - normalCDF (w j))) atTop (𝓝 (cE * betaE)) := by
  have hκ : Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 kappaE) := by
    simpa only [signedThirdMoment_esseen] using bounded_signedThirdMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hu := bounded_jitter_uniform_expansion W S P esseenLaw hw hβ hb n hn hn2 hE hE_pos.le esseen_resonance_multiplier_zero
  let x : ℕ → ℝ := fun j => w j + hE / (2 * Real.sqrt (n j : ℝ))
  have herr : Tendsto (fun j => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) hE (x j)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.1 hu ε hε] with j hj
    simpa only [Real.dist_eq, sub_zero, zero_sub, abs_neg] using hj (x j)
  have hc : Continuous (fun a : ℝ × ℝ => edgeworthEnvelope hE a.1 a.2) := by
    unfold edgeworthEnvelope
    exact (show Continuous (fun a : ℝ × ℝ => hE / 2 + a.1 / 6 * (1 - a.2 ^ 2)) by fun_prop).mul
      (standardNormalDensity_continuous.comp continuous_snd)
  have henv : Tendsto (fun j => edgeworthEnvelope hE (signedThirdMoment (P j)) (w j)) atTop (𝓝 (cE * betaE)) := by
    have he := (hc.tendsto (kappaE, 0)).comp (hκ.prodMk_nhds hw0)
    convert he using 1
    simp only [edgeworthEnvelope, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one, standardNormalDensity_zero]
    rw [esseen_peak_identity]
  have hew : Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (edgeworthCDF (n j) (signedThirdMoment (P j)) (x j) - normalCDF (w j)) -
        edgeworthEnvelope hE (signedThirdMoment (P j)) (w j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_) (edgeworthShiftConstant_scaled_tendsto_zero n hn hE)
    rw [Real.norm_eq_abs]
    exact edgeworthCDF_shift_remainder (n j) (by have := hn2 j; omega)
      (signedThirdMoment (P j)) hE (w j) ((signedThirdMoment_abs_le _).trans (hβ j))
  have he := herr.add (hew.add henv)
  simp only [zero_add] at he
  convert he using 1
  funext j
  unfold jitterCDFError
  rw [normalized_jitter_cdf_as_raw (P j) (n j) (by have := hn2 j; omega)]
  have hs : Real.sqrt (n j : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by have := hn2 j; omega))).ne'
  have hx : Real.sqrt (n j : ℝ) * x j = Real.sqrt (n j : ℝ) * w j + hE / 2 := by dsimp [x]; field_simp
  rw [hx]
  simp only [spanJitter, if_pos hE_pos]
  ring

theorem extremizer_jitter_contact_saturation
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (v : ℕ → ℝ) (y : ℝ) (hvsupp : ∀ j, v j ∈ (P j).measure.support)
    (hy : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j) ∗ uniformJitter hE) (t j - v j + hE / 2) -
        ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j)) (t j - v j))) atTop (𝓝 0) := by
  have hn1 (j : ℕ) : 1 ≤ n j := by have := hn2 j; omega
  have hb (j : ℕ) : ∀ᵐ x ∂(P j).measure, |x| ≤ 10 := by
    filter_upwards [(P j).measure.support_mem_ae] with x hx
    exact abs_le.2 (hsupp j hx)
  have hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) := by
    simpa only [thirdMoment_esseen] using bounded_thirdMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 (qE - pE)) := by
    simpa only [signedSecondMoment_esseen] using bounded_signedSecondMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hn' : Tendsto (fun j => n j + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hn
  have hR : Tendsto (fun j => signedRatio (P j) (n j) (t j)) atTop (𝓝 cE) := by
    simpa only [hattain] using violating_extremalConstant_tendsto H (fun j => n j + 1) hn' hv
  have hβ2 (j : ℕ) : thirdMoment (P j) ≤ 2 := by
    have hc := extremizer_thirdMoment_cutoff H (P j) (n j) (t j) (by rw [hattain j]; exact hv j)
    linarith [momentCutoff_bounds.2]
  have hprev := contact_previous_discrepancy_tendsto H P n t v y betaE (qE - pE) cE 10
    hn hn1 hattain hv hz hy (fun j => abs_le.2 (hsupp j (hvsupp j))) hβ hM hR hvsupp
  have hw0 := predecessor_threshold_tendsto_zero n t v y hn hn1 hz hy
  have hjitter := jitter_shifted_discrepancy_tendsto W S P hw hβ2 hb n hn hn2 _ hw0
  have he := hjitter.sub hprev
  simp only [sub_self] at he
  convert he using 1
  funext j
  have hs : Real.sqrt (n j : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by have := hn2 j; omega))).ne'
  rw [mul_div_cancel₀ _ hs]
  ring

end BerryEsseen
