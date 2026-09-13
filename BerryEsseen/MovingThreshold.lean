import BerryEsseen.SumMoments

/-! Closed-set portmanteau for moving thresholds, retaining atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem weak_cdf_limsup_le (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ)) (t : ℝ) :
    atTop.limsup (fun j => cdf (μs j : Measure ℝ) t) ≤ cdf (μ : Measure ℝ) t := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (isClosed_Iic (a := t))
  have hb : ∀ᶠ j in atTop, (μs j : Measure ℝ) (Iic t) ≤ 1 :=
    Eventually.of_forall (fun j => prob_le_one)
  simp only [cdf_eq_real, Measure.real]
  rw [ENNReal.limsup_toReal_eq (b := 1) (by norm_num) hb]
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

theorem moving_cdf_lower_limit (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ)) (ts : ℕ → ℝ) (t : ℝ) (ht : Tendsto ts atTop (𝓝 t))
    (a : ℕ → ℝ) (b : ℝ) (ha : Tendsto a atTop (𝓝 b))
    (hle : ∀ j, a j ≤ cdf (μs j : Measure ℝ) (ts j)) : b ≤ cdf (μ : Measure ℝ) t := by
  have hb (ε : ℝ) (hε : 0 < ε) : b ≤ cdf (μ : Measure ℝ) (t + ε) := by
    have he : ∀ᶠ j in atTop, a j ≤ cdf (μs j : Measure ℝ) (t + ε) := by
      filter_upwards [ht.eventually (eventually_lt_nhds (by linarith : t < t + ε))] with j hj
      exact (hle j).trans ((monotone_cdf _) hj.le)
    apply le_trans _ (weak_cdf_limsup_le μs μ hμ (t + ε))
    apply le_limsup_of_le
      (show IsBoundedUnder (· ≤ ·) atTop (fun j => cdf (μs j : Measure ℝ) (t + ε)) from
        ⟨1, by
          change ∀ᶠ j in atTop, cdf (μs j : Measure ℝ) (t + ε) ≤ 1
          exact Eventually.of_forall (fun j => cdf_le_one _ _)⟩)
    intro c hc
    apply le_of_tendsto ha
    filter_upwards [he, hc] with j hj hj'
    exact hj.trans hj'
  have ht' : Tendsto (fun j : ℕ => t + 1 / ((j : ℝ) + 1)) atTop (𝓝[Ici t] t) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
    · exact Eventually.of_forall (fun j => by
        change t ≤ t + 1 / ((j : ℝ) + 1)
        exact le_add_of_nonneg_right (by positivity))
  have hc := ((cdf (μ : Measure ℝ)).right_continuous t).tendsto.comp ht'
  exact ge_of_tendsto hc (Eventually.of_forall (fun j => hb (1 / ((j : ℝ) + 1)) (by positivity)))

end BerryEsseen
