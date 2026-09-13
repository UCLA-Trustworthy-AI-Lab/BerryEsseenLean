import BerryEsseen.EdgeworthEnvelopes
import BerryEsseen.ActualJitterSandwich

/-! Both CDF envelopes for the actual unsmoothed sums in the bounded class. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem bounded_jitter_envelopes (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      edgeworthEnvelope (-h) (signedThirdMoment (P j)) x - ε ≤
        Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤
        edgeworthEnvelope h (signedThirdMoment (P j)) x + ε := by
  have hU := bounded_jitter_uniform_expansion W S P Q hw hβ hb n hn hn2 h hh hzero
  have hC := edgeworthShiftConstant_scaled_tendsto_zero n hn h
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.1 hU) (ε / 2) (by linarith),
    hC.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hjU hjC
  intro x
  let s := Real.sqrt (n j : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by have := hn2 j; omega))
  have hn1 : 1 ≤ n j := by have := hn2 j; omega
  have hκ := (signedThirdMoment_abs_le (P j)).trans (hβ j)
  have hp := edgeworthCDF_shift_remainder (n j) hn1 (signedThirdMoment (P j)) h x hκ
  have hm := edgeworthCDF_shift_remainder (n j) hn1 (signedThirdMoment (P j)) (-h) x hκ
  rw [edgeworthShiftConstant_neg,
    show x + -h / (2 * Real.sqrt (n j : ℝ)) = x - h / (2 * Real.sqrt (n j : ℝ)) by ring] at hm
  have hJu : |s * jitterCDFError (P j) (n j) h (x + h / (2 * s))| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjU (x + h / (2 * s))
  have hJl : |s * jitterCDFError (P j) (n j) h (x - h / (2 * s))| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjU (x - h / (2 * s))
  unfold jitterCDFError at hJu hJl
  have hsp := actual_normalized_jitter_sandwich (P j) (n j) hn1 h hh x
  have hslu := mul_le_mul_of_nonneg_left hsp.2 hs.le
  have hsll := mul_le_mul_of_nonneg_left hsp.1 hs.le
  have hpU := (abs_le.1 hp).2
  have hmL := (abs_le.1 hm).1
  have hjUpper := (abs_lt.1 hJu).2
  have hjLower := (abs_lt.1 hJl).1
  change edgeworthShiftConstant h / s < ε / 2 at hjC
  change s * (edgeworthCDF (n j) (signedThirdMoment (P j)) (x + h / (2 * s)) - normalCDF x) -
    edgeworthEnvelope h (signedThirdMoment (P j)) x ≤ edgeworthShiftConstant h / s at hpU
  change -(edgeworthShiftConstant h / s) ≤
    s * (edgeworthCDF (n j) (signedThirdMoment (P j)) (x - h / (2 * s)) - normalCDF x) -
      edgeworthEnvelope (-h) (signedThirdMoment (P j)) x at hmL
  change edgeworthEnvelope (-h) (signedThirdMoment (P j)) x - ε ≤
    s * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
    s * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤ edgeworthEnvelope h (signedThirdMoment (P j)) x + ε
  constructor <;> nlinarith

theorem edgeworthEnvelope_abs_bound (h κ x : ℝ) :
    |edgeworthEnvelope h κ x| ≤ (|h| / 2 + |κ| / 6) * phi0 := by
  have h1 : |h / 2 * standardNormalDensity x| ≤ |h| / 2 * phi0 := by
    rw [abs_mul, abs_div, abs_of_pos (standardNormalDensity_pos x)]
    norm_num
    exact mul_le_mul_of_nonneg_left (standardNormalDensity_le_phi0 x) (by positivity)
  have h2 : |κ / 6 * ((1 - x ^ 2) * standardNormalDensity x)| ≤ |κ| / 6 * phi0 := by
    rw [abs_mul, abs_div]
    norm_num
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [show 1 - x ^ 2 = -(x ^ 2 - 1) by ring, neg_mul, abs_neg, abs_mul] using gaussian_second_derivative_bound x
  have he : edgeworthEnvelope h κ x = h / 2 * standardNormalDensity x +
      κ / 6 * ((1 - x ^ 2) * standardNormalDensity x) := by unfold edgeworthEnvelope; ring
  rw [he]
  calc
    _ ≤ |h / 2 * standardNormalDensity x| + |κ / 6 * ((1 - x ^ 2) * standardNormalDensity x)| := abs_add_le _ _
    _ ≤ |h| / 2 * phi0 + |κ| / 6 * phi0 := add_le_add h1 h2
    _ = _ := by ring

end BerryEsseen
