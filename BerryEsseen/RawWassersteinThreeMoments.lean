import BerryEsseen.RawCubicIntegralLimits
import BerryEsseen.RawNormalization
import BerryEsseen.WassersteinMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem real_first_second_cubic_growth (x : ℝ) :
    |x| ≤ 1 + |x| ^ 3 ∧ |x ^ 2| ≤ 1 + |x| ^ 3 := by
  rw [abs_of_nonneg (sq_nonneg x)]
  by_cases hx : |x| ≤ 1
  · constructor <;> nlinarith [abs_nonneg x, sq_abs x, pow_nonneg (abs_nonneg x) 3]
  · have h1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hmul := mul_nonneg (sq_nonneg (|x|)) (sub_nonneg.mpr h1)
    constructor <;> nlinarith [abs_nonneg x, sq_abs x]

theorem raw_first_second_integrable_of_third (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Integrable (fun x : ℝ => x) μ ∧ Integrable (fun x : ℝ => x ^ 2) μ := by
  constructor
  · exact cubic_growth_integrable μ hi (fun x => x) continuous_id 1 (by norm_num)
      (fun x => by simpa only [one_mul] using (real_first_second_cubic_growth x).1)
  · exact cubic_growth_integrable μ hi (fun x => x ^ 2) (by fun_prop) 1 (by norm_num)
      (fun x => by simpa only [one_mul] using (real_first_second_cubic_growth x).2)

theorem shifted_cubic_growth (m x : ℝ) :
    |(|x - m| ^ 3)| ≤ (4 * (1 + |m| ^ 3)) * (1 + |x| ^ 3) := by
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  have h := shifted_abs_cube_bound x m
  nlinarith [mul_nonneg (pow_nonneg (abs_nonneg x) 3) (pow_nonneg (abs_nonneg m) 3)]

theorem raw_shifted_third_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) (m : ℝ) :
    Integrable (fun x : ℝ => |x - m| ^ 3) μ :=
  cubic_growth_integrable μ hi (fun x => |x - m| ^ 3) (by fun_prop)
    (4 * (1 + |m| ^ 3)) (by positivity) (shifted_cubic_growth m)

theorem raw_shifted_second_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) (m : ℝ) :
    Integrable (fun x : ℝ => (x - m) ^ 2) μ := by
  obtain ⟨h1, h2⟩ := raw_first_second_integrable_of_third μ hi
  have hs := (h2.sub (h1.const_mul (2 * m))).add (integrable_const (m ^ 2))
  convert hs using 1
  funext x
  dsimp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem raw_variance_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    (∫ x, (x - rawMean μ) ^ 2 ∂μ) = (∫ x, x ^ 2 ∂μ) - rawMean μ ^ 2 := by
  obtain ⟨h1, h2⟩ := raw_first_second_integrable_of_third μ hi
  have he (x : ℝ) : (x - rawMean μ) ^ 2 = x ^ 2 - 2 * rawMean μ * x + rawMean μ ^ 2 := by ring
  simp_rw [he]
  have hl : Integrable (fun x : ℝ => 2 * rawMean μ * x) μ := h1.const_mul (2 * rawMean μ)
  have hd : Integrable (fun x : ℝ => x ^ 2 - 2 * rawMean μ * x) μ := h2.sub hl
  rw [integral_add hd (integrable_const _), integral_sub h2 hl, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change (∫ x, x ^ 2 ∂μ) - 2 * rawMean μ * rawMean μ + rawMean μ ^ 2 = _
  ring

theorem weak_cubic_raw_first_second_tendsto
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hw : Tendsto μj atTop (𝓝 μ))
    (hm : Tendsto (fun j => ∫ x, |x| ^ 3 ∂(μj j : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ 3 ∂(μ : Measure ℝ)))) :
    Tendsto (fun j => rawMean (μj j : Measure ℝ)) atTop (𝓝 (rawMean (μ : Measure ℝ))) ∧
      Tendsto (fun j => ∫ x, x ^ 2 ∂(μj j : Measure ℝ)) atTop
        (𝓝 (∫ x, x ^ 2 ∂(μ : Measure ℝ))) := by
  constructor
  · exact weak_cubic_moment_integral_tendsto μj μ hi hiQ hw hm (fun x => x) continuous_id 1
      (by norm_num) (fun x => by simpa only [one_mul] using (real_first_second_cubic_growth x).1)
  · exact weak_cubic_moment_integral_tendsto μj μ hi hiQ hw hm (fun x => x ^ 2) (by fun_prop) 1
      (by norm_num) (fun x => by simpa only [one_mul] using (real_first_second_cubic_growth x).2)

theorem weak_cubic_rawStdDev_tendsto
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hw : Tendsto μj atTop (𝓝 μ))
    (hm : Tendsto (fun j => ∫ x, |x| ^ 3 ∂(μj j : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ 3 ∂(μ : Measure ℝ)))) :
    Tendsto (fun j => rawStdDev (μj j : Measure ℝ)) atTop (𝓝 (rawStdDev (μ : Measure ℝ))) := by
  obtain ⟨h1, h2⟩ := weak_cubic_raw_first_second_tendsto μj μ hi hiQ hw hm
  have hc := (h2.sub (h1.pow 2)).sqrt
  simpa only [rawStdDev, raw_variance_identity _ hiQ, raw_variance_identity _ (hi _)] using hc

theorem centered_cubic_shift_pointwise (a b x : ℝ) (hab : |a - b| ≤ 1) :
    |(|x - a| ^ 3) - (|x - b| ^ 3)| ≤
      6 * (x ^ 2 + (|b| + 1) ^ 2) * |a - b| := by
  let R := |x| + |b| + 1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have ha : |a| ≤ |b| + 1 := by
    have ht := abs_sub_le a b 0
    simp only [sub_zero] at ht
    linarith
  have hx : |x - a| ≤ R := by
    have ht := abs_sub_le x 0 a
    simp only [sub_zero, zero_sub, abs_neg] at ht
    dsimp only [R]
    linarith
  have hy : |x - b| ≤ R := by
    have ht := abs_sub_le x 0 b
    simp only [sub_zero, zero_sub, abs_neg] at ht
    dsimp only [R]
    linarith
  have hc := absolute_cube_difference_bounded R (x - a) (x - b) hR hx hy
  have he : (x - a) - (x - b) = -(a - b) := by ring
  rw [he, abs_neg] at hc
  have hR2 : R ^ 2 ≤ 2 * (x ^ 2 + (|b| + 1) ^ 2) := by
    dsimp only [R]
    nlinarith [sq_nonneg (|x| - (|b| + 1)), sq_abs x]
  exact hc.trans (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))

theorem centered_cubic_integral_shift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) (a b : ℝ) (hab : |a - b| ≤ 1) :
    |(∫ x, |x - a| ^ 3 ∂μ) - (∫ x, |x - b| ^ 3 ∂μ)| ≤
      6 * ((∫ x, x ^ 2 ∂μ) + (|b| + 1) ^ 2) * |a - b| := by
  have hia := raw_shifted_third_integrable μ hi a
  have hib := raw_shifted_third_integrable μ hi b
  have hi2 := (raw_first_second_integrable_of_third μ hi).2
  rw [← integral_sub hia hib]
  calc
    _ ≤ ∫ x, ‖|x - a| ^ 3 - |x - b| ^ 3‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, 6 * (x ^ 2 + (|b| + 1) ^ 2) * |a - b| ∂μ := by
      apply integral_mono (hia.sub hib).norm
        (((hi2.add (integrable_const _)).const_mul 6).mul_const _)
      intro x
      exact centered_cubic_shift_pointwise a b x hab
    _ = _ := by
      rw [integral_mul_const, integral_const_mul, integral_add hi2 (integrable_const _)]
      simp

theorem weak_cubic_rawThirdAbsoluteMoment_tendsto
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hw : Tendsto μj atTop (𝓝 μ))
    (hm : Tendsto (fun j => ∫ x, |x| ^ 3 ∂(μj j : Measure ℝ)) atTop
      (𝓝 (∫ x, |x| ^ 3 ∂(μ : Measure ℝ)))) :
    Tendsto (fun j => rawThirdAbsoluteMoment (μj j : Measure ℝ)) atTop
      (𝓝 (rawThirdAbsoluteMoment (μ : Measure ℝ))) := by
  let m := rawMean (μ : Measure ℝ)
  obtain ⟨hmean, hsecond⟩ := weak_cubic_raw_first_second_tendsto μj μ hi hiQ hw hm
  have hfixed := weak_cubic_moment_integral_tendsto μj μ hi hiQ hw hm
    (fun x => |x - m| ^ 3) (by fun_prop) (4 * (1 + |m| ^ 3)) (by positivity) (shifted_cubic_growth m)
  have hzero : Tendsto (fun j => rawMean (μj j : Measure ℝ) - m) atTop (𝓝 0) := by
    simpa only [m, sub_self] using hmean.sub_const m
  have hmajor : Tendsto (fun j => 6 * ((∫ x, x ^ 2 ∂(μj j : Measure ℝ)) + (|m| + 1) ^ 2) *
      |rawMean (μj j : Measure ℝ) - m|) atTop (𝓝 0) := by
    simpa only [abs_zero, mul_zero] using
      ((hsecond.add_const ((|m| + 1) ^ 2)).const_mul 6).mul hzero.abs
  have herr : Tendsto (fun j => rawThirdAbsoluteMoment (μj j : Measure ℝ) -
      ∫ x, |x - m| ^ 3 ∂(μj j : Measure ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [Metric.tendsto_nhds.1 hzero 1 (by norm_num)] with j hj
    rw [Real.dist_eq, sub_zero] at hj
    exact centered_cubic_integral_shift (μj j : Measure ℝ) (hi j) (rawMean (μj j : Measure ℝ)) m hj.le
  simpa only [sub_add_cancel, zero_add, rawThirdAbsoluteMoment, m] using herr.add hfixed

theorem wassersteinThree_raw_moments_tendsto
    (W : PublishedWassersteinThreeTopology)
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hW : Tendsto (fun j => wassersteinThree (μj j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => rawMean (μj j : Measure ℝ)) atTop (𝓝 (rawMean (μ : Measure ℝ))) ∧
      Tendsto (fun j => rawStdDev (μj j : Measure ℝ)) atTop (𝓝 (rawStdDev (μ : Measure ℝ))) ∧
      Tendsto (fun j => rawThirdAbsoluteMoment (μj j : Measure ℝ)) atTop
        (𝓝 (rawThirdAbsoluteMoment (μ : Measure ℝ))) := by
  obtain ⟨hw, hm⟩ := (W.tendsto_iff μj μ hi hiQ).1 hW
  exact ⟨(weak_cubic_raw_first_second_tendsto μj μ hi hiQ hw hm).1,
    weak_cubic_rawStdDev_tendsto μj μ hi hiQ hw hm,
    weak_cubic_rawThirdAbsoluteMoment_tendsto μj μ hi hiQ hw hm⟩

end BerryEsseen
