import BerryEsseen.ContactSaturation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem bounded_jitter_shifted_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (a : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      |Real.sqrt (n j : ℝ) *
        (cdf (iidSumLaw (P j).measure (n j) ∗ spanJitter h) (Real.sqrt (n j : ℝ) * x + a / 2) - normalCDF x) -
        edgeworthEnvelope a (signedThirdMoment (P j)) x| < ε := by
  have hU := bounded_jitter_uniform_expansion W S P Q hw hβ hb n hn hn2 h hh hzero
  have hC := edgeworthShiftConstant_scaled_tendsto_zero n hn a
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 hU (ε / 2) (by linarith),
    hC.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hjU hjC
  intro x
  have hn1 : 1 ≤ n j := by have := hn2 j; omega
  have hs : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by omega))
  have hp := edgeworthCDF_shift_remainder (n j) hn1 (signedThirdMoment (P j)) a x
    ((signedThirdMoment_abs_le (P j)).trans (hβ j))
  have herr : |Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h
      (x + a / (2 * Real.sqrt (n j : ℝ)))| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjU (x + a / (2 * Real.sqrt (n j : ℝ)))
  unfold jitterCDFError at herr
  rw [normalized_jitter_cdf_as_raw (P j) (n j) hn1] at herr
  have he : Real.sqrt (n j : ℝ) * (x + a / (2 * Real.sqrt (n j : ℝ))) =
      Real.sqrt (n j : ℝ) * x + a / 2 := by field_simp [hs.ne']
  rw [he] at herr
  have hdecomp : Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (P j).measure (n j) ∗ spanJitter h) (Real.sqrt (n j : ℝ) * x + a / 2) - normalCDF x) -
      edgeworthEnvelope a (signedThirdMoment (P j)) x =
    Real.sqrt (n j : ℝ) *
      (cdf (iidSumLaw (P j).measure (n j) ∗ spanJitter h) (Real.sqrt (n j : ℝ) * x + a / 2) -
        edgeworthCDF (n j) (signedThirdMoment (P j)) (x + a / (2 * Real.sqrt (n j : ℝ)))) +
    (Real.sqrt (n j : ℝ) * (edgeworthCDF (n j) (signedThirdMoment (P j))
      (x + a / (2 * Real.sqrt (n j : ℝ))) - normalCDF x) - edgeworthEnvelope a (signedThirdMoment (P j)) x) := by ring
  rw [hdecomp]
  apply (abs_add_le _ _).trans_lt
  have hh := add_lt_add herr (hp.trans_lt hjC)
  convert hh using 1 <;> ring

end BerryEsseen
