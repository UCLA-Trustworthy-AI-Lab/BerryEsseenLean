import BerryEsseen.BoundedJitterEnvelopes
import BerryEsseen.BoundedMomentLimits

/-! The limiting envelopes and the sharp moment saturation forced by violations. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem edgeworthEnvelope_parameter_bound (h κ κ' x : ℝ) :
    |edgeworthEnvelope h κ x - edgeworthEnvelope h κ' x| ≤ phi0 / 6 * |κ - κ'| := by
  have he : edgeworthEnvelope h κ x - edgeworthEnvelope h κ' x =
      (κ - κ') / 6 * ((1 - x ^ 2) * standardNormalDensity x) := by
    unfold edgeworthEnvelope
    ring
  rw [he, abs_mul, abs_div]
  have hgauss : |(1 - x ^ 2) * standardNormalDensity x| ≤ phi0 := by
    simpa only [show 1 - x ^ 2 = -(x ^ 2 - 1) by ring, neg_mul, abs_neg] using gaussian_second_derivative_bound x
  have hb := mul_le_mul_of_nonneg_left hgauss (div_nonneg (abs_nonneg (κ - κ')) (by norm_num : (0 : ℝ) ≤ 6))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  exact hb.trans_eq (by ring)

theorem bounded_jitter_limit_envelopes (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      edgeworthEnvelope (-h) (signedThirdMoment Q) x - ε ≤
        Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤
        edgeworthEnvelope h (signedThirdMoment Q) x + ε := by
  have hκ := bounded_signedThirdMoment_tendsto P Q hw 10 (by norm_num) hb
  have hκ0 : Tendsto (fun j => phi0 / 6 * |signedThirdMoment (P j) - signedThirdMoment Q|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero] using ((hκ.sub_const (signedThirdMoment Q)).abs).const_mul (phi0 / 6)
  intro ε hε
  filter_upwards [bounded_jitter_envelopes W S P Q hw hβ hb n hn hn2 h hh hzero (ε / 2) (by linarith),
    hκ0.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hj hsmall
  intro x
  have hplus := edgeworthEnvelope_parameter_bound h (signedThirdMoment (P j)) (signedThirdMoment Q) x
  have hminus := edgeworthEnvelope_parameter_bound (-h) (signedThirdMoment (P j)) (signedThirdMoment Q) x
  have hp := (abs_le.1 hplus).2
  have hm := (abs_le.1 hminus).1
  have henv := hj x
  constructor <;> linarith [henv.1, henv.2]

theorem bounded_violation_limit_moment_lower (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (z : ℕ → ℝ) (hviol : ∀ j, cE * thirdMoment (P j) ≤
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) (z j) - normalCDF (z j))) :
    cE * thirdMoment Q ≤ (h / 2 + |signedThirdMoment Q| / 6) * phi0 := by
  have hlim := (bounded_thirdMoment_tendsto P Q hw 10 (by norm_num) hb).const_mul cE
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_tendsto hlim
  filter_upwards [bounded_jitter_limit_envelopes W S P Q hw hβ hb n hn hn2 h hh hzero ε hε] with j hj
  have hu := (hj (z j)).2
  have he := (le_abs_self (edgeworthEnvelope h (signedThirdMoment Q) (z j))).trans
    (edgeworthEnvelope_abs_bound h (signedThirdMoment Q) (z j))
  rw [abs_of_nonneg hh] at he
  exact (hviol j).trans (hu.trans (add_le_add he le_rfl))

end BerryEsseen
