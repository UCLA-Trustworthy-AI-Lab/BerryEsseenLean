import BerryEsseen.GeneralBernoulliLimits
import BerryEsseen.EffectiveClusterEnvelope
import BerryEsseen.RawAffineWeak

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem averageNoiseVariance_tendsto_zero (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j) :
    Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => averageNoiseVariance_nonneg _ _ _ ⟨(hp j).1.le, (hp j).2.le⟩)
    (fun j => averageNoiseVariance_le_square _ _ _ _ ⟨(hp j).1.le, (hp j).2.le⟩ (hε j) (hP j) (hQ j))
  simpa using hεlim.pow 2

theorem clusterVariance_tendsto_general (P Q : ℕ → CenteredFourthLaw) (p : ℕ → ℝ)
    (p₀ : ℝ) (hp : Tendsto p atTop (𝓝 p₀))
    (hs : Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0)) :
    Tendsto (fun j => clusterVariance (P j) (Q j) (p j)) atTop (𝓝 (p₀ * (1 - p₀))) := by
  have h := (hp.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).add hs
  simpa only [add_zero, clusterVariance, averageNoiseVariance, add_assoc] using h

theorem clusterThirdAbsoluteMoment_tendsto_general (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (hs : Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0)) :
    Tendsto (fun j => clusterThirdAbsoluteMoment (P j) (Q j) (p j)) atTop
      (𝓝 (p₀ * (1 - p₀) * (p₀ ^ 2 + (1 - p₀) ^ 2))) := by
  have hevent : ∀ᶠ j in atTop, ε j ≤ p j ∧ ε j ≤ 1 - p j := by
    filter_upwards [(hεlim.sub hplim).eventually (gt_mem_nhds (show 0 - p₀ < (0 : ℝ) by linarith [hp₀.1])),
      (hεlim.add hplim).eventually (gt_mem_nhds (show 0 + p₀ < (1 : ℝ) by linarith [hp₀.2]))] with j hj hk
    constructor <;> linarith
  have herror : Tendsto (fun j => clusterThirdAbsoluteMoment (P j) (Q j) (p j) -
      p j * (1 - p j) * ((p j) ^ 2 + (1 - p j) ^ 2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (by simpa using ((tendsto_const_nhds (x := (3 : ℝ))).add hεlim).mul hs)
    filter_upwards [hevent] with j hj
    simpa only [Real.norm_eq_abs, clusterThirdAbsoluteMoment, averageNoiseVariance] using
      twoCluster_abs_third_error (P j) (Q j) (p j) (ε j) ⟨(hp j).1.le, (hp j).2.le⟩
        hj.1 hj.2 (hP j) (hQ j)
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hplim
  have hb := (hplim.mul hq).mul ((hplim.pow 2).add (hq.pow 2))
  simpa only [sub_add_cancel, zero_add] using herror.add hb

theorem clusterSignedThirdMoment_tendsto_general (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (hs : Tendsto (fun j => averageNoiseVariance (P j) (Q j) (p j)) atTop (𝓝 0)) :
    Tendsto (fun j => clusterSignedThirdMoment (P j) (Q j) (p j)) atTop
      (𝓝 (p₀ * (1 - p₀) * (1 - 2 * p₀))) := by
  have herror : Tendsto (fun j => clusterSignedThirdMoment (P j) (Q j) (p j) -
      p j * (1 - p j) * (1 - 2 * p j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_)
      (by simpa using ((tendsto_const_nhds (x := (3 : ℝ))).add hεlim).mul hs)
    simpa only [Real.norm_eq_abs] using
      clusterSignedThirdMoment_error (P j) (Q j) (p j) (ε j) ⟨(hp j).1.le, (hp j).2.le⟩ (hP j) (hQ j)
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hplim
  have hb := (hplim.mul hq).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub (hplim.const_mul 2))
  simpa only [sub_add_cancel, zero_add] using herror.add hb

theorem shrinking_noise_integral_tendsto (P : ℕ → CenteredFourthLaw) (ε : ℕ → ℝ)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (f : BoundedContinuousFunction ℝ ℝ) (a : ℝ) :
    Tendsto (fun j => ∫ x, f (a + x) ∂(P j).measure) atTop (𝓝 (f a)) := by
  apply Metric.tendsto_nhds.2
  intro η hη
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.1 (f.continuous.continuousAt (x := a)) (η / 2) (by positivity)
  filter_upwards [hεlim.eventually (gt_mem_nhds hδ)] with j hj
  have hi : Integrable (fun x => f (a + x)) (P j).measure := by
    apply (integrable_const ‖f‖).mono' (by fun_prop)
    exact ae_of_all _ (fun x => f.norm_coe_le_norm (a + x))
  have he : |(∫ x, f (a + x) ∂(P j).measure) - f a| ≤ η / 2 := by
    have hc : (∫ _ : ℝ, f a ∂(P j).measure) = f a := by simp
    rw [← hc, ← integral_sub hi (integrable_const (f a))]
    apply (abs_integral_le_integral_abs).trans
    calc
      (∫ x, |f (a + x) - f a| ∂(P j).measure) ≤ ∫ _ : ℝ, η / 2 ∂(P j).measure := by
        apply integral_mono_ae (hi.sub (integrable_const _)).abs (integrable_const _)
        filter_upwards [hP j] with x hx
        have hxδ : dist (a + x) a < δ := by simpa only [Real.dist_eq, add_sub_cancel_left] using hx.trans_lt hj
        simpa only [Real.dist_eq] using (hd hxδ).le
      _ = η / 2 := by simp
  rw [Real.dist_eq]
  exact he.trans_lt (by linarith)

def twoClusterProbabilityMeasure (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) :
    ProbabilityMeasure ℝ :=
  ⟨twoClusterMeasure P Q p, twoClusterMeasure_probability P Q p ⟨hp.1.le, hp.2.le⟩⟩

theorem twoClusterProbabilityMeasure_tendsto (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j) :
    Tendsto (fun j => twoClusterProbabilityMeasure (P j) (Q j) (p j) (hp j)) atTop
      (𝓝 (twoClusterProbabilityMeasure CenteredFourthLaw.zero CenteredFourthLaw.zero p₀ hp₀)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun j => ∫ x, f x ∂twoClusterMeasure (P j) (Q j) (p j)) atTop
    (𝓝 (∫ x, f x ∂twoClusterMeasure CenteredFourthLaw.zero CenteredFourthLaw.zero p₀))
  have hiQ (j : ℕ) : Integrable (fun x => f (1 + x)) (Q j).measure := by
    apply (integrable_const ‖f‖).mono' (by fun_prop)
    exact ae_of_all _ (fun x => f.norm_coe_le_norm (1 + x))
  have he (j : ℕ) := integral_twoClusterMeasure (P j) (Q j) (p j)
    ⟨(hp j).1.le, (hp j).2.le⟩ f f.continuous.measurable (f.integrable _) (hiQ j)
  simp_rw [he]
  rw [twoCluster_zero_noise, bernoulliMeasure, integral_mixtureMeasure _ _ p₀ ⟨hp₀.1.le, hp₀.2.le⟩
    f (f.integrable _) (f.integrable _)]
  simp only [integral_dirac]
  have hleft := shrinking_noise_integral_tendsto P ε hεlim hP f 0
  simp only [zero_add] at hleft
  have hright := shrinking_noise_integral_tendsto Q ε hεlim hQ f 1
  exact (((tendsto_const_nhds (x := (1 : ℝ))).sub hplim).mul hleft).add (hplim.mul hright)

theorem standardizedTwoClusterLaw_tendsto (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j) :
    Tendsto (fun j => (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)).toProbabilityMeasure) atTop
      (𝓝 (standardizedBernoulliLaw p₀ hp₀).toProbabilityMeasure) := by
  have hs := averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ
  have hv := (clusterVariance_tendsto_general P Q p p₀ hplim hs).sqrt
  have hσ : Real.sqrt (p₀ * (1 - p₀)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))).ne'
  have hw := twoClusterProbabilityMeasure_tendsto P Q p ε hp p₀ hp₀ hplim hεlim hP hQ
  have h := probabilityMeasure_tendsto_map_affine _ _ _ _ _ _ hw (hv.inv₀ hσ) (hplim.neg.div hv hσ)
  have he (A B : CenteredFourthLaw) (q : ℝ) (hq : q ∈ Ioo 0 1) :
      (twoClusterProbabilityMeasure A B q hq).map
        (show Measurable (fun x : ℝ => (Real.sqrt (clusterVariance A B q))⁻¹ * x +
          -q / Real.sqrt (clusterVariance A B q)) by fun_prop).aemeasurable =
      (standardizedTwoClusterLaw A B q hq).toProbabilityMeasure := by
    apply Subtype.ext
    change (twoClusterMeasure A B q).map _ = standardizedMeasure (twoClusterMeasure A B q) q _
    unfold standardizedMeasure
    congr 1
    funext x
    ring
  simp_rw [he] at h
  have he0 := he CenteredFourthLaw.zero CenteredFourthLaw.zero p₀ hp₀
  simp only [zero_clusterVariance] at he0
  rw [he0] at h
  exact h

theorem standardizedTwoCluster_third_tendsto (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j) :
    Tendsto (fun j => thirdMoment (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j))) atTop
      (𝓝 (thirdMoment (standardizedBernoulliLaw p₀ hp₀))) := by
  have hs := averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ
  have hv := (clusterVariance_tendsto_general P Q p p₀ hplim hs).sqrt
  have hρ := clusterThirdAbsoluteMoment_tendsto_general P Q p ε hp p₀ hp₀ hplim hεlim hP hQ hs
  have hv0 := mul_pos hp₀.1 (sub_pos.mpr hp₀.2)
  have hσ := (Real.sqrt_pos.mpr hv0).ne'
  have h := hρ.div (hv.pow 3) (pow_ne_zero 3 hσ)
  simp_rw [standardizedTwoClusterLaw_third]
  convert h using 1
  rw [standardizedBernoulli_third]
  congr 1
  field_simp [hσ]
  rw [Real.sq_sqrt hv0.le]
  ring

theorem standardizedTwoCluster_signed_third_tendsto (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j) :
    Tendsto (fun j => signedThirdMoment (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j))) atTop
      (𝓝 (signedThirdMoment (standardizedBernoulliLaw p₀ hp₀))) := by
  have hs := averageNoiseVariance_tendsto_zero P Q p ε hp hε hεlim hP hQ
  have hv := (clusterVariance_tendsto_general P Q p p₀ hplim hs).sqrt
  have hρ := clusterSignedThirdMoment_tendsto_general P Q p ε hp p₀ hplim hεlim hP hQ hs
  have hv0 := mul_pos hp₀.1 (sub_pos.mpr hp₀.2)
  have hσ := (Real.sqrt_pos.mpr hv0).ne'
  have h := hρ.div (hv.pow 3) (pow_ne_zero 3 hσ)
  simp_rw [standardizedTwoCluster_signed_third]
  convert h using 1
  rw [standardizedBernoulli_signed_third]
  congr 1
  field_simp [hσ]
  rw [Real.sq_sqrt hv0.le]
  ring

end BerryEsseen
