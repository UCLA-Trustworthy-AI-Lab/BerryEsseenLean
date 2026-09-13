import BerryEsseen.RawWassersteinThreeStandardization
import BerryEsseen.RawJitterCDFBridge
import BerryEsseen.GeneralJitterExpansion

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- Actual raw sum plus one raw uniform jitter, evaluated after centering and scaling.
This expression remains defined for any finite initial rows with zero variance. -/
def rawJitterCDFError (μ : Measure ℝ) (n : ℕ) (d x : ℝ) : ℝ :=
  cdf (iidSumLaw μ n ∗ spanJitter d)
    ((n : ℝ) * rawMean μ + rawStdDev μ * Real.sqrt (n : ℝ) * x) -
  edgeworthCDF n ((∫ y, (y - rawMean μ) ^ 3 ∂μ) / rawStdDev μ ^ 3) x

theorem rawJitterCDFError_eq_standardized (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hσ : 0 < rawStdDev (μ : Measure ℝ)) (n : ℕ) (hn : 1 ≤ n)
    (d : ℝ) (hd : 0 ≤ d) (x : ℝ) :
    rawJitterCDFError (μ : Measure ℝ) n d x =
      jitterCDFError (rawStandardizedLaw μ hi hσ) n (d / rawStdDev (μ : Measure ℝ)) x := by
  let Z := rawStandardizedLaw μ hi hσ
  letI := normalizedJitteredSumLaw_probability Z n (d / rawStdDev (μ : Measure ℝ))
  unfold rawJitterCDFError jitterCDFError
  rw [rawStandardizedLaw_signedThirdMoment μ hi hσ]
  congr 1
  change _ = (normalizedJitteredSumLaw Z n (d / rawStdDev (μ : Measure ℝ))).real (Iic x)
  rw [← cdf_eq_real]
  exact (standardized_normalized_spanJitter_cdf (μ : Measure ℝ) Z (rawMean (μ : Measure ℝ))
    (rawStdDev (μ : Measure ℝ)) hσ rfl n hn d hd x).symm

theorem raw_wassersteinThree_variable_jitter_expansion_of_pos
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hW : Tendsto (fun j => wassersteinThree (μj j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0))
    (hσj : ∀ j, 0 < rawStdDev (μj j : Measure ℝ))
    (hσQ : 0 < rawStdDev (μ : Measure ℝ))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (d : ℝ) (hd : 0 ≤ d ∧ (0 < d → IsLatticeSpan (μ : Measure ℝ) d) ∧
      ∀ e : ℝ, IsLatticeSpan (μ : Measure ℝ) e → e ≤ d)
    (dj : ℕ → ℝ) (hdj : ∀ j, 0 ≤ dj j) (hdlim : Tendsto dj atTop (𝓝 d)) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * rawJitterCDFError (μj j : Measure ℝ) (n j) (dj j) x)
      (fun _ => 0) atTop := by
  let P : ℕ → StandardizedLaw := fun j => rawStandardizedLaw (μj j) (hi j) (hσj j)
  let Q := rawStandardizedLaw μ hiQ hσQ
  have hW' := raw_standardization_wassersteinThree_tendsto W μj μ hi hiQ hW hσj hσQ
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW'
  have hs := (wassersteinThree_raw_moments_tendsto W μj μ hi hiQ hW).2.1
  have hspan := rawStandardizedLaw_maximalSpan μ hiQ hσQ d hd
  have hzero := maximal_span_resonance_multiplier Q (d / rawStdDev (μ : Measure ℝ))
    hspan.1 hspan.2.1 hspan.2.2
  have hU := general_variable_jitter_uniform_expansion W S P Q hw hm n hn
    (d / rawStdDev (μ : Measure ℝ)) hspan.1 hzero
    (fun j => dj j / rawStdDev (μj j : Measure ℝ))
    (fun j => div_nonneg (hdj j) (hσj j).le) (hdlim.div hs hσQ.ne')
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 hU ε hε,
    hn.eventually (eventually_ge_atTop 1)] with j hj hn1
  intro x
  simpa only [rawJitterCDFError_eq_standardized (μj j) (hi j) (hσj j) (n j) hn1 (dj j) (hdj j) x] using hj x

/-- The full unstandardized variable-width remark. Only the limiting law has
positive variance; arbitrary finitely many degenerate rows are allowed. The
maximal span may be zero. The error uses the actual CDF and actual centered
third moment of each raw law. -/
theorem raw_wassersteinThree_variable_jitter_expansion
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hW : Tendsto (fun j => wassersteinThree (μj j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0))
    (hσQ : 0 < rawStdDev (μ : Measure ℝ))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (d : ℝ) (hd : 0 ≤ d ∧ (0 < d → IsLatticeSpan (μ : Measure ℝ) d) ∧
      ∀ e : ℝ, IsLatticeSpan (μ : Measure ℝ) e → e ≤ d)
    (dj : ℕ → ℝ) (hdj : ∀ j, 0 ≤ dj j) (hdlim : Tendsto dj atTop (𝓝 d)) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * rawJitterCDFError (μj j : Measure ℝ) (n j) (dj j) x)
      (fun _ => 0) atTop := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (rawStdDev_eventually_pos_of_wassersteinThree W μj μ hi hiQ hW hσQ)
  have hU := raw_wassersteinThree_variable_jitter_expansion_of_pos W S
    (fun j => μj (j + J)) μ (fun j => hi (j + J)) hiQ
    (hW.comp (tendsto_add_atTop_nat J))
    (fun j => hJ (j + J) (by omega)) hσQ
    (fun j => n (j + J)) (hn.comp (tendsto_add_atTop_nat J)) d hd
    (fun j => dj (j + J)) (fun j => hdj (j + J)) (hdlim.comp (tendsto_add_atTop_nat J))
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hU ε hε)
  apply eventually_atTop.2
  refine ⟨N + J, ?_⟩
  intro j hj x
  have hh := hN (j - J) (by omega) x
  simpa only [Nat.sub_add_cancel (show J ≤ j by omega)] using hh

/-- Equivalent original-threshold statement: the remainder is uniform over every
raw threshold, with the actual row mean, variance, and signed centered moment. -/
theorem raw_wassersteinThree_variable_jitter_expansion_at_raw
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hW : Tendsto (fun j => wassersteinThree (μj j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0))
    (hσQ : 0 < rawStdDev (μ : Measure ℝ))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (d : ℝ) (hd : 0 ≤ d ∧ (0 < d → IsLatticeSpan (μ : Measure ℝ) d) ∧
      ∀ e : ℝ, IsLatticeSpan (μ : Measure ℝ) e → e ≤ d)
    (dj : ℕ → ℝ) (hdj : ∀ j, 0 ≤ dj j) (hdlim : Tendsto dj atTop (𝓝 d)) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ t : ℝ,
      |Real.sqrt (n j : ℝ) *
        (cdf (iidSumLaw (μj j : Measure ℝ) (n j) ∗ spanJitter (dj j)) t -
          edgeworthCDF (n j)
            ((∫ y, (y - rawMean (μj j : Measure ℝ)) ^ 3 ∂(μj j : Measure ℝ)) /
              rawStdDev (μj j : Measure ℝ) ^ 3)
            ((t - (n j : ℝ) * rawMean (μj j : Measure ℝ)) /
              (rawStdDev (μj j : Measure ℝ) * Real.sqrt (n j : ℝ))))| < ε := by
  have hU := raw_wassersteinThree_variable_jitter_expansion W S μj μ hi hiQ hW hσQ n hn d hd dj hdj hdlim
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 hU ε hε,
    rawStdDev_eventually_pos_of_wassersteinThree W μj μ hi hiQ hW hσQ,
    hn.eventually (eventually_ge_atTop 1)] with j hj hσj hnj
  intro t
  have hr : 0 < Real.sqrt (n j : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n j by omega))
  have hh := hj ((t - (n j : ℝ) * rawMean (μj j : Measure ℝ)) /
    (rawStdDev (μj j : Measure ℝ) * Real.sqrt (n j : ℝ)))
  have he : (n j : ℝ) * rawMean (μj j : Measure ℝ) + rawStdDev (μj j : Measure ℝ) *
      Real.sqrt (n j : ℝ) * ((t - (n j : ℝ) * rawMean (μj j : Measure ℝ)) /
        (rawStdDev (μj j : Measure ℝ) * Real.sqrt (n j : ℝ))) = t := by
    field_simp
    ring
  simpa only [Real.dist_eq, zero_sub, abs_neg, rawJitterCDFError, he] using hh

end BerryEsseen
