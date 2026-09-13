import BerryEsseen.ContactSaturation

/-! Actual contact, limiting support and separation estimates. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem raw_jitter_flat_increment_limit
    (μ : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (a u d : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (h D : ℝ) (hh : 0 < h)
    (hD : D ∈ Ioo 0 h) (hd : Tendsto d atTop (𝓝 D))
    (haverage : Tendsto (fun j => a j *
      (ProbabilityTheory.cdf (μ j ∗ uniformJitter h) (u j + h / 2) - ProbabilityTheory.cdf (μ j) (u j))) atTop (𝓝 0)) :
    Tendsto (fun j => a j * (ProbabilityTheory.cdf (μ j) (u j + d j) - ProbabilityTheory.cdf (μ j) (u j))) atTop (𝓝 0) := by
  let q : ℝ := (h - D) / (2 * h)
  have hq : 0 < q := div_pos (sub_pos.2 hD.2) (by positivity)
  have hev : ∀ᶠ j in atTop, 0 ≤ d j ∧ d j ≤ (h + D) / 2 := by
    filter_upwards [hd.eventually (lt_mem_nhds hD.1), hd.eventually (gt_mem_nhds (by linarith [hD.2] : D < (h + D) / 2))] with j hj hk
    exact ⟨hj.le, hk.le⟩
  apply squeeze_zero' ?_ ?_ (by simpa only [zero_div] using haverage.div_const q)
  · filter_upwards [hev] with j hj
    exact mul_nonneg (ha j) (sub_nonneg.2 (ProbabilityTheory.monotone_cdf (μ j) (by linarith [hj.1])))
  · filter_upwards [hev] with j hj
    have hinc : 0 ≤ ProbabilityTheory.cdf (μ j) (u j + d j) - ProbabilityTheory.cdf (μ j) (u j) :=
      sub_nonneg.2 (ProbabilityTheory.monotone_cdf (μ j) (by linarith [hj.1]))
    have hfrac : q ≤ (h - d j) / h := by
      dsimp [q]
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * h) hh).2
      nlinarith [hj.2]
    have hb := mul_le_mul_of_nonneg_left (uniformJitter_controls_cdf_increment (μ j) hh (u j) (d j) hj.1 (by linarith [hj.2, hD.2])) (ha j)
    have hqbound := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfrac hinc) (ha j)
    apply (le_div_iff₀ hq).2
    nlinarith only [hb, hqbound]

def contactEquationRemainder (P : StandardizedLaw) (n : ℕ) (t v : ℝ) : ℝ :=
  -(t / Real.sqrt (n + 1 : ℝ) * standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) / 2) * (v ^ 2 - 1) +
    signedRatio P n t / Real.sqrt (n + 1 : ℝ) *
      (|v| ^ 3 - thirdMoment P - 3 * signedSecondMoment P * v - 3 / 2 * thirdMoment P * (v ^ 2 - 1))

theorem contactEquationRemainder_tendsto_zero
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t v : ℕ → ℝ) (y β M R : ℝ)
    (hn : Tendsto n atTop atTop)
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hy : Tendsto v atTop (𝓝 y))
    (hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 β))
    (hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 M))
    (hR : Tendsto (fun j => signedRatio (P j) (n j) (t j)) atTop (𝓝 R)) :
    Tendsto (fun j => contactEquationRemainder (P j) (n j) (t j) (v j)) atTop (𝓝 0) := by
  have hφ : Tendsto (fun j => standardNormalDensity (t j / Real.sqrt (n j + 1 : ℝ))) atTop (𝓝 phi0) := by
    simpa only [standardNormalDensity_zero] using (standardNormalDensity_continuous.tendsto 0).comp hz
  have hnc : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hs := Real.tendsto_sqrt_atTop.comp (hnc.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have he := ((((hz.mul hφ).div_const 2).neg).mul ((hy.pow 2).sub_const 1)).add
    ((hR.div_atTop hs).mul ((((hy.abs.pow 3).sub hβ).sub ((hM.const_mul 3).mul hy)).sub
      ((hβ.const_mul (3 / 2)).mul ((hy.pow 2).sub_const 1))))
  simpa only [contactEquationRemainder, zero_mul, zero_div, neg_zero, zero_add] using he

theorem contact_cdf_increment_exact (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (t x y : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (hx : x ∈ P.measure.support) (hy : y ∈ P.measure.support) :
    Real.sqrt (n : ℝ) * (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - x) -
      ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - y)) =
    Real.sqrt (n : ℝ) / Real.sqrt (n + 1 : ℝ) *
      (standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) * (y - x) +
        (contactEquationRemainder P n t x - contactEquationRemainder P n t y) / Real.sqrt (n + 1 : ℝ)) := by
  have hp : 0 ≤ signedRatio P n t := by rw [hattain]; exact cE_pos.le.trans hv.le
  have hcx := influence_contact_equation H P n t hattain hp x hx
  have hcy := influence_contact_equation H P n t hattain hp y hy
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
  have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1 : ℝ) by positivity)
  have he : Real.sqrt (n + 1 : ℝ) * (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - x) -
      ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - y)) =
      standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) * (y - x) +
        (contactEquationRemainder P n t x - contactEquationRemainder P n t y) / Real.sqrt (n + 1 : ℝ) := by
    apply (mul_left_cancel₀ hs)
    conv_rhs => rw [mul_add, mul_div_cancel₀ _ hs]
    unfold contactEquationRemainder
    linear_combination hcx - hcy +
      (ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - x) - ProbabilityTheory.cdf (iidSumLaw P.measure n) (t - y)) * hs2
  rw [← he]
  field_simp [hs]

theorem contact_increment_tendsto (H : ClassicalBerryEsseenBounds)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t x y : ℕ → ℝ) (a b β M R : ℝ)
    (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b))
    (hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 β))
    (hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 M))
    (hR : Tendsto (fun j => signedRatio (P j) (n j) (t j)) atTop (𝓝 R))
    (hxsupp : ∀ j, x j ∈ (P j).measure.support) (hysupp : ∀ j, y j ∈ (P j).measure.support) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      (ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j)) (t j - x j) -
        ProbabilityTheory.cdf (iidSumLaw (P j).measure (n j)) (t j - y j))) atTop (𝓝 (phi0 * (b - a))) := by
  have hrx := contactEquationRemainder_tendsto_zero P n t x a β M R hn hz hx hβ hM hR
  have hry := contactEquationRemainder_tendsto_zero P n t y b β M R hn hz hy hβ hM hR
  have hφ : Tendsto (fun j => standardNormalDensity (t j / Real.sqrt (n j + 1 : ℝ))) atTop (𝓝 phi0) := by
    simpa only [standardNormalDensity_zero] using (standardNormalDensity_continuous.tendsto 0).comp hz
  have hnc : Tendsto (fun j => (n j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hs := Real.tendsto_sqrt_atTop.comp (hnc.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have he := (sqrt_predecessor_ratio_tendsto n hn hn1).mul
    ((hφ.mul (hy.sub hx)).add ((hrx.sub hry).div_atTop hs))
  simpa only [contact_cdf_increment_exact H _ _ _ _ _ (hattain _) (hv _) (hxsupp _) (hysupp _),
    add_zero, one_mul] using he

theorem extremizer_no_short_positive_gap
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (x y : ℕ → ℝ) (a b : ℝ) (hxsupp : ∀ j, x j ∈ (P j).measure.support)
    (hysupp : ∀ j, y j ∈ (P j).measure.support)
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b))
    (hgap : b - a ∈ Ioo 0 hE) : False := by
  have havg := extremizer_jitter_contact_saturation H W S P n t hn hn2 hattain hv hw hz hsupp y b hysupp hy
  have hflat := raw_jitter_flat_increment_limit (fun j => iidSumLaw (P j).measure (n j))
    (fun j => Real.sqrt (n j : ℝ)) (fun j => t j - y j) (fun j => y j - x j)
    (fun j => Real.sqrt_nonneg _) hE (b - a) hE_pos hgap (hy.sub hx) havg
  have hident (j : ℕ) : t j - y j + (y j - x j) = t j - x j := by ring
  simp only [hident] at hflat
  have hb (j : ℕ) : ∀ᵐ v ∂(P j).measure, |v| ≤ 10 := by
    filter_upwards [(P j).measure.support_mem_ae] with v hv
    exact abs_le.2 (hsupp j hv)
  have hβ : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 betaE) := by
    simpa only [thirdMoment_esseen] using bounded_thirdMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hM : Tendsto (fun j => signedSecondMoment (P j)) atTop (𝓝 (qE - pE)) := by
    simpa only [signedSecondMoment_esseen] using bounded_signedSecondMoment_tendsto P esseenLaw hw 10 (by norm_num) hb
  have hn' : Tendsto (fun j => n j + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hn
  have hR : Tendsto (fun j => signedRatio (P j) (n j) (t j)) atTop (𝓝 cE) := by
    simpa only [hattain] using violating_extremalConstant_tendsto H (fun j => n j + 1) hn' hv
  have hcontact := contact_increment_tendsto H P n t x y a b betaE (qE - pE) cE hn
    (fun j => by have := hn2 j; omega) hattain hv hz hx hy hβ hM hR hxsupp hysupp
  have he := tendsto_nhds_unique hflat hcontact
  have hpos := mul_pos phi0_pos hgap.1
  linarith

theorem extremizer_support_limit_separation
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (x y : ℕ → ℝ) (a b : ℝ) (hxsupp : ∀ j, x j ∈ (P j).measure.support)
    (hysupp : ∀ j, y j ∈ (P j).measure.support)
    (hx : Tendsto x atTop (𝓝 a)) (hy : Tendsto y atTop (𝓝 b)) :
    a = b ∨ hE ≤ |a - b| := by
  by_cases he : a = b
  · exact Or.inl he
  right
  by_contra h
  have habs : |a - b| < hE := lt_of_not_ge h
  rcases lt_or_gt_of_ne he with hlt | hgt
  · exact extremizer_no_short_positive_gap H W S P n t hn hn2 hattain hv hw hz hsupp x y a b
      hxsupp hysupp hx hy ⟨by linarith, by rw [abs_of_neg (by linarith : a - b < 0)] at habs; linarith⟩
  · exact extremizer_no_short_positive_gap H W S P n t hn hn2 hattain hv hw hz hsupp y x b a
      hysupp hxsupp hy hx ⟨by linarith, by rw [abs_of_pos (by linarith : 0 < a - b)] at habs; exact habs⟩

end BerryEsseen
