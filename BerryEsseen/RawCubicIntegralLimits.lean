import BerryEsseen.GeneralThirdMomentTails
import BerryEsseen.BoundedMomentLimits

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

theorem cubic_growth_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : 0 ≤ C) (hfbound : ∀ x, |f x| ≤ C * (1 + |x| ^ 3)) :
    Integrable f μ := by
  apply (((integrable_const (1 : ℝ)).add hi).const_mul C).mono' hf.measurable.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using hfbound x

theorem raw_cappedAbsoluteThird_integral_tendsto (μ : Measure ℝ)
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) :
    Tendsto (fun N : ℕ => ∫ x, cappedAbsoluteThirdBCF (N : ℝ) (by positivity) x ∂μ)
      atTop (𝓝 (∫ x, |x| ^ 3 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => |x| ^ 3)
  · intro N
    exact (cappedAbsoluteThirdBCF (N : ℝ) (by positivity)).continuous.measurable.aestronglyMeasurable
  · exact hi
  · intro N
    filter_upwards [] with x
    change ‖min (|x| ^ 3) (N : ℝ)‖ ≤ |x| ^ 3
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by positivity) (by positivity))]
    exact min_le_left _ _
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually (eventually_ge_atTop (|x| ^ 3))]
      with N hN
    change |x| ^ 3 = min (|x| ^ 3) (N : ℝ)
    exact (min_eq_left hN).symm

def cubicGrowthClippedBCF (f : ℝ → ℝ) (hf : Continuous f)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) : ℝ →ᵇ ℝ :=
  (clippedRealBCF (C * (1 + A)) (by positivity)).compContinuous ⟨f, hf⟩

theorem cubic_growth_clipped_error (f : ℝ → ℝ) (hf : Continuous f)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hfbound : ∀ x, |f x| ≤ C * (1 + |x| ^ 3)) (x : ℝ) :
    |f x - cubicGrowthClippedBCF f hf C A hC hA x| ≤
      C * (|x| ^ 3 - min (|x| ^ 3) A) := by
  have hr : 0 ≤ C * (1 + A) := by positivity
  have hres : 0 ≤ C * (|x| ^ 3 - min (|x| ^ 3) A) :=
    mul_nonneg hC (sub_nonneg.mpr (min_le_left _ _))
  have hmin : C * min (|x| ^ 3) A ≤ C * A := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
  have hb := abs_le.mp (hfbound x)
  change |f x - clippedReal (C * (1 + A)) (f x)| ≤ _
  unfold clippedReal
  by_cases hlow : f x < -(C * (1 + A))
  · rw [min_eq_left (by linarith : f x ≤ C * (1 + A)), max_eq_left hlow.le,
      abs_of_nonpos (by linarith : f x - -(C * (1 + A)) ≤ 0)]
    nlinarith [hb.1]
  · by_cases hhigh : C * (1 + A) < f x
    · rw [min_eq_right hhigh.le, max_eq_right (by linarith : -(C * (1 + A)) ≤ C * (1 + A)),
        abs_of_nonneg (by linarith : 0 ≤ f x - C * (1 + A))]
      nlinarith [hb.2]
    · rw [min_eq_left (le_of_not_gt hhigh), max_eq_right (le_of_not_gt hlow), sub_self, abs_zero]
      exact hres

theorem cubic_growth_clipped_integral_error (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x| ^ 3) μ) (f : ℝ → ℝ) (hf : Continuous f)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hfbound : ∀ x, |f x| ≤ C * (1 + |x| ^ 3)) :
    |(∫ x, f x ∂μ) - ∫ x, cubicGrowthClippedBCF f hf C A hC hA x ∂μ| ≤
      C * ((∫ x, |x| ^ 3 ∂μ) - ∫ x, cappedAbsoluteThirdBCF A hA x ∂μ) := by
  have hif := cubic_growth_integrable μ hi f hf C hC hfbound
  have hig := (cubicGrowthClippedBCF f hf C A hC hA).integrable μ
  have hic := (cappedAbsoluteThirdBCF A hA).integrable μ
  rw [← integral_sub hif hig]
  have hn := norm_integral_le_integral_norm
    (f := fun x => f x - cubicGrowthClippedBCF f hf C A hC hA x) (μ := μ)
  simp only [Real.norm_eq_abs] at hn
  apply hn.trans
  rw [← integral_sub hi hic, ← integral_const_mul]
  apply integral_mono (hif.sub hig).abs ((hi.sub hic).const_mul C)
  intro x
  exact cubic_growth_clipped_error f hf C A hC hA hfbound x

theorem weak_cubic_moment_integral_tendsto
    (μj : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => |x| ^ 3) (μj j : Measure ℝ))
    (hiQ : Integrable (fun x : ℝ => |x| ^ 3) (μ : Measure ℝ))
    (hw : Tendsto μj atTop (𝓝 μ))
    (hm : Tendsto (fun j => ∫ x, |x| ^ 3 ∂(μj j : Measure ℝ))
      atTop (𝓝 (∫ x, |x| ^ 3 ∂(μ : Measure ℝ))))
    (f : ℝ → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hfbound : ∀ x, |f x| ≤ C * (1 + |x| ^ 3)) :
    Tendsto (fun j => ∫ x, f x ∂(μj j : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hresQ : Tendsto (fun N : ℕ => C * ((∫ x, |x| ^ 3 ∂(μ : Measure ℝ)) -
      ∫ x, cappedAbsoluteThirdBCF (N : ℝ) (by positivity) x ∂(μ : Measure ℝ)))
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := C)).mul
        ((tendsto_const_nhds (x := ∫ x, |x| ^ 3 ∂(μ : Measure ℝ))).sub
          (raw_cappedAbsoluteThird_integral_tendsto (μ : Measure ℝ) hiQ)) using 1 <;> norm_num
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hresQ).2 (ε / 4) (by positivity)).exists
  let A : ℝ := N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let g : ℝ →ᵇ ℝ := cubicGrowthClippedBCF f hf C A hC hA
  have hg := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw g
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw
    (cappedAbsoluteThirdBCF A hA)
  have hr := (tendsto_const_nhds (x := C)).mul (hm.sub hc)
  have hsmall : C * ((∫ x, |x| ^ 3 ∂(μ : Measure ℝ)) -
      ∫ x, cappedAbsoluteThirdBCF A hA x ∂(μ : Measure ℝ)) < ε / 3 := by
    exact hN.trans (by linarith)
  have he := (tendsto_order.1 hr).2 (ε / 3) hsmall
  have heg := (Metric.tendsto_nhds.1 hg) (ε / 3) (by positivity)
  filter_upwards [he, heg] with j hj hjg
  have hp := cubic_growth_clipped_integral_error (μj j : Measure ℝ) (hi j)
    f hf C A hC hA hfbound
  have hq := cubic_growth_clipped_integral_error (μ : Measure ℝ) hiQ
    f hf C A hC hA hfbound
  have hp' : |(∫ x, f x ∂(μj j : Measure ℝ)) - ∫ x, g x ∂(μj j : Measure ℝ)| < ε / 3 :=
    hp.trans_lt hj
  have hq' : |(∫ x, f x ∂(μ : Measure ℝ)) - ∫ x, g x ∂(μ : Measure ℝ)| < ε / 3 :=
    hq.trans_lt hsmall
  rw [Real.dist_eq] at hjg ⊢
  have ht := abs_add_three
    ((∫ x, f x ∂(μj j : Measure ℝ)) - ∫ x, g x ∂(μj j : Measure ℝ))
    ((∫ x, g x ∂(μj j : Measure ℝ)) - ∫ x, g x ∂(μ : Measure ℝ))
    ((∫ x, g x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ))
  have heq : ((∫ x, f x ∂(μj j : Measure ℝ)) - ∫ x, g x ∂(μj j : Measure ℝ)) +
      ((∫ x, g x ∂(μj j : Measure ℝ)) - ∫ x, g x ∂(μ : Measure ℝ)) +
      ((∫ x, g x ∂(μ : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ)) =
      ((∫ x, f x ∂(μj j : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ)) := by ring
  rw [heq, abs_sub_comm (∫ x, g x ∂(μ : Measure ℝ))] at ht
  linarith

end BerryEsseen
