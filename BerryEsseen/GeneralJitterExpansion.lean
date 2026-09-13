import BerryEsseen.GeneralLowFrequencyIntegral
import BerryEsseen.GeneralJitterAssembly
import BerryEsseen.GeneralJitterWidth
import BerryEsseen.GeneralJitterEnvelopes

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The full triangular-array jitter expansion from weak convergence and
convergence of absolute third moments. No support bound is required. -/
theorem general_jitter_uniform_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop := by
  have hW3 := (standardized_wassersteinThree_tendsto_iff W P Q).2 ⟨hw, hm⟩
  obtain ⟨B, hB⟩ := hm.bddAbove_range
  have hβ : ∀ j, thirdMoment (P j) ≤ B := fun j => hB ⟨j, rfl⟩
  have hB1 : 1 ≤ B := (thirdMoment_ge_one (P 0)).trans (hβ 0)
  have hB0 : 0 < B := by linarith
  let m : ℕ → ℕ := fun j => max (n j) 2
  have hmn : ∀ᶠ j in atTop, m j = n j := by
    filter_upwards [hn.eventually (eventually_ge_atTop 2)] with j hj
    exact max_eq_left hj
  have hmtop : Tendsto m atTop atTop := hn.congr' (hmn.mono fun _ heq => heq.symm)
  have hm2 : ∀ j, 2 ≤ m j := fun j => le_max_right _ _
  have hδ : 0 < (1 : ℝ) / (100 * B) := by positivity
  have hU := general_jitter_uniform_expansion_of_raw_low S P Q hw hW3 B hβ m hmtop
    (fun j => by have := hm2 j; omega) h (1 / (100 * B)) hh hδ hzero
    (fun j => general_rawJitterFourierError_low_integrable (P j) B hB1 (hβ j) (m j) (hm2 j) h hh)
    (general_rawJitterFourierError_low_scaled_tendsto_zero P Q hw hm B hB1 hβ m hmtop hm2 h hh)
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 hU ε hε, hmn] with j hj heq
  simpa only [heq] using hj

theorem wassersteinThree_jitter_uniform_expansion
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  exact general_jitter_uniform_expansion W S P Q hw hm n hn h hh hzero

theorem maximal_span_resonance_multiplier (Q : StandardizedLaw) (h : ℝ)
    (hh : 0 ≤ h) (hspan : 0 < h → IsLatticeSpan Q.measure h)
    (hmax : ∀ d, IsLatticeSpan Q.measure d → d ≤ h) :
    ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0 := by
  obtain ⟨k, hk, hkspan, hkmax, hz⟩ := manuscript_exists_span_and_resonance_multiplier Q
  have heq : h = k := by
    apply le_antisymm
    · by_cases hp : 0 < h
      · exact hkmax h (hspan hp)
      · linarith
    · by_cases kp : 0 < k
      · exact hmax k (hkspan kp)
      · linarith
  intro r hr hres
  rw [heq]
  exact hz r hr ((mem_resonanceSubgroup_iff Q.measure r).1 hres)

/-- Manuscript Lemma jitter, including the nonlattice case h = 0. -/
theorem maximal_span_wassersteinThree_jitter_expansion
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h) (hspan : 0 < h → IsLatticeSpan Q.measure h)
    (hmax : ∀ d, IsLatticeSpan Q.measure d → d ≤ h) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop :=
  wassersteinThree_jitter_uniform_expansion W S P Q hW n hn h hh
    (maximal_span_resonance_multiplier Q h hh hspan hmax)

theorem exists_maximal_span_wassersteinThree_jitter_expansion
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    ∃ h : ℝ, 0 ≤ h ∧ (0 < h → IsLatticeSpan Q.measure h) ∧
      (∀ d, IsLatticeSpan Q.measure d → d ≤ h) ∧
      TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
        (fun _ => 0) atTop := by
  obtain ⟨h, hh, hspan, hmax, _⟩ := manuscript_exists_span_and_resonance_multiplier Q
  exact ⟨h, hh, hspan, hmax,
    maximal_span_wassersteinThree_jitter_expansion W S P Q hW n hn h hh hspan hmax⟩

/-- The standardized variable-width form with no expansion supplied as a hypothesis. -/
theorem general_variable_jitter_uniform_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j) (hwlim : Tendsto w atTop (𝓝 h)) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) (w j) x)
      (fun _ => 0) atTop := by
  obtain ⟨B, hB⟩ := hm.bddAbove_range
  have hβ : ∀ j, thirdMoment (P j) ≤ B := fun j => hB ⟨j, rfl⟩
  let m : ℕ → ℕ := fun j => max (n j) 1
  have hmn : ∀ᶠ j in atTop, m j = n j := by
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hj
    exact max_eq_left hj
  have hmtop : Tendsto m atTop atTop := hn.congr' (hmn.mono fun _ heq => heq.symm)
  have hfixed := general_jitter_uniform_expansion W S P Q hw hm m hmtop h hh hzero
  have hU := variable_jitter_uniform_expansion_of_fixed P m (fun j => le_max_right _ _)
    B hβ h hh w hw0 hwlim hfixed
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 hU ε hε, hmn] with j hj heq
  simpa only [heq] using hj

end BerryEsseen
