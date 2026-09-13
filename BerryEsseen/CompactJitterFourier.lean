import BerryEsseen.RawFourierError
import BerryEsseen.GeneralLowFrequencyIntegral
import BerryEsseen.PublishedWassersteinThree

/-! The complete compact Fourier estimate for uniformly bounded standardized laws. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem integral_le_add_of_cover (f : ℝ → ℝ) (K A B : Set ℝ)
    (hK : MeasurableSet K) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hf : ∀ x, 0 ≤ f x) (hiA : IntegrableOn f A) (hiB : IntegrableOn f B)
    (hcover : K ⊆ A ∪ B) : (∫ x in K, f x) ≤ (∫ x in A, f x) + ∫ x in B, f x := by
  have hiK : IntegrableOn f K := (hiA.union hiB).mono_set hcover
  have hia := hiA.integrable_indicator hA
  have hib := hiB.integrable_indicator hB
  have hh : ∀ x, K.indicator f x ≤ A.indicator f x + B.indicator f x := by
    intro x
    have hna : 0 ≤ A.indicator f x := indicator_nonneg (fun u _ => hf u) x
    have hnb : 0 ≤ B.indicator f x := indicator_nonneg (fun u _ => hf u) x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      rcases hcover hx with hxa | hxb
      · rw [indicator_of_mem hxa]
        linarith
      · rw [indicator_of_mem hxb]
        linarith
    · rw [indicator_of_notMem hx]
      exact add_nonneg hna hnb
  have hb := integral_mono (hiK.integrable_indicator hK) (hia.add hib) hh
  change (∫ x, K.indicator f x) ≤ ∫ x, A.indicator f x + B.indicator f x at hb
  simpa only [integral_add hia hib, integral_indicator hK, integral_indicator hA, integral_indicator hB] using hb

theorem bounded_compact_rawJitterFourier_tendsto_zero (W : PublishedWassersteinThreeTopology) (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (T : ℝ) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ u in Icc (-T) T, rawJitterFourierError (P j) (n j) h u) atTop (𝓝 0) := by
  let A := Icc (-(1 / 200 : ℝ)) (1 / 200)
  let K := Icc (-T) T ∩ {u : ℝ | 1 / 200 ≤ |u|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hl : ∀ u ∈ K, (1 / 200 : ℝ) ≤ |u| := fun _ hu => hu.2
  have hu : ∀ u ∈ K, |u| ≤ T := fun _ hu => abs_le.2 hu.1
  have hcover : Icc (-T) T ⊆ A ∪ K := by
    intro u humem
    by_cases hlow : |u| ≤ 1 / 200
    · exact Or.inl (abs_le.1 hlow)
    · exact Or.inr ⟨humem, (lt_of_not_ge hlow).le⟩
  have hm := bounded_thirdMoment_tendsto P Q hw 10 (by norm_num) hb
  have hW3 := bounded_weak_wassersteinThree_tendsto W P Q hw 10 (by norm_num) hb
  have hlow := general_rawJitterFourierError_low_scaled_tendsto_zero P Q hw hm 2
    (by norm_num) hβ n hn hn2 h hh
  norm_num only [show (1 : ℝ) / (100 * 2) = 1 / 200 by norm_num] at hlow
  have haway := compact_rawJitterFourierError_away_tendsto_zero P Q hw hW3 2 hβ n hn h hh hzero
    K hK (1 / 200) T (by norm_num) hl hu
  have hsum := hlow.add haway
  simp only [add_zero] at hsum
  apply squeeze_zero _ _ hsum
  · intro j
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (rawJitterFourierError_nonneg (P j) (n j) h))
  · intro j
    have hn1 : 1 ≤ n j := by have := hn2 j; omega
    have hiA := general_rawJitterFourierError_low_integrable (P j) 2 (by norm_num)
      (hβ j) (n j) (hn2 j) h hh
    norm_num only [show (1 : ℝ) / (100 * 2) = 1 / 200 by norm_num] at hiA
    have hiK := rawJitterFourierError_away_integrable (P j) (n j) hn1 h 2 (1 / 200) T
      (hβ j) (by norm_num) K hK hl hu
    have hbnd := integral_le_add_of_cover (rawJitterFourierError (P j) (n j) h) (Icc (-T) T) A K
      measurableSet_Icc measurableSet_Icc hK.measurableSet
      (rawJitterFourierError_nonneg (P j) (n j) h) hiA hiK hcover
    change _ ≤ (∫ u in Icc (-(1 / 200 : ℝ)) (1 / 200), rawJitterFourierError (P j) (n j) h u) + _ at hbnd
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hbnd (Real.sqrt_nonneg (n j : ℝ))

theorem bounded_compact_jitterFourier_tendsto_zero (W : PublishedWassersteinThreeTopology) (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) *
      ∫ t in Icc (-T * Real.sqrt (n j : ℝ)) (T * Real.sqrt (n j : ℝ)),
        jitterFourierError (P j) (n j) h t) atTop (𝓝 0) := by
  have hraw := bounded_compact_rawJitterFourier_tendsto_zero W P Q hw hβ hb n hn hn2 h hh hzero T
  convert hraw using 1
  funext j
  rw [rawJitterFourierError_integral_scale (P j) (n j) (by have := hn2 j; omega) h (-T) T hh (by linarith)]
  simp only [mul_comm]

end BerryEsseen
