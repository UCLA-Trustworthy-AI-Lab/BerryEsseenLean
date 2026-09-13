import BerryEsseen.ManuscriptResonanceGeometry

/-! The actual moving resonance intervals in the uniform jitter argument. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem resonance_neighborhood (Q : StandardizedLaw) (r : ℝ) (hr : r ≠ 0)
    (hres : r ∈ resonanceSubgroup Q.measure) :
    ∃ d : ℝ, 0 < d ∧ d ≤ |r| / 2 ∧
      (∀ u ∈ Icc (r - d) (r + d), characteristicSquareCurvature Q u ≤ -3 / 2) ∧
      (∀ u ∈ Icc (r - d) (r + d), u ≠ r → characteristicSquare Q u < characteristicSquare Q r) := by
  obtain ⟨δ, hδ, hgap⟩ := manuscript_resonance_gap Q
  have hc := (characteristicSquareCurvature_hasDerivAt Q r).continuousAt
  obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  let d := min δ (min η |r|) / 2
  have hd : 0 < d := by dsimp [d]; exact div_pos (lt_min hδ (lt_min hη (abs_pos.2 hr))) (by norm_num)
  have hdδ : d ≤ δ / 2 := by
    dsimp [d]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hdη : d ≤ η / 2 := by
    dsimp [d]
    exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hdr : d ≤ |r| / 2 := by
    dsimp [d]
    exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hdist (u : ℝ) (hu : u ∈ Icc (r - d) (r + d)) : |u - r| ≤ d := by
    apply abs_le.2
    constructor <;> linarith [hu.1, hu.2]
  refine ⟨d, hd, hdr, ?_, ?_⟩
  · intro u hu
    have hdistη : dist u r < η := by rw [Real.dist_eq]; have := hdist u hu; linarith
    have h := hηc hdistη
    rw [Real.dist_eq, characteristicSquareCurvature_at_resonance Q r hres] at h
    have hh := (abs_lt.1 h).2
    linarith
  · intro u hu hur
    have hnot : u ∉ resonanceSubgroup Q.measure := by
      intro huRes
      have hg := hgap (u - r) ((resonanceSubgroup Q.measure).sub_mem huRes hres) (sub_ne_zero.2 hur)
      have hb := hdist u hu
      linarith
    have hnorm : ‖charFun Q.measure u‖ < 1 := by
      by_contra h
      apply hnot
      exact (mem_resonanceSubgroup_iff Q.measure u).2
        (le_antisymm (norm_charFun_le_one u) (le_of_not_gt h))
    have hnr : ‖charFun Q.measure r‖ = 1 := (mem_resonanceSubgroup_iff Q.measure r).1 hres
    unfold characteristicSquare
    rw [hnr]
    have hp := mul_pos (sub_pos.2 hnorm) (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg (charFun Q.measure u)))
    nlinarith

theorem actual_moving_resonance_envelopes_on (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (r d : ℝ) (hd : 0 < d)
    (hcurv : ∀ u ∈ Icc (r - d) (r + d), characteristicSquareCurvature Q u ≤ -3 / 2)
    (hstrict : ∀ u ∈ Icc (r - d) (r + d), u ≠ r →
      characteristicSquare Q u < characteristicSquare Q r) :
    ∃ m : ℕ → ℝ, Tendsto m atTop (𝓝 r) ∧
      ∀ᶠ j in atTop, m j ∈ Ioo (r - d) (r + d) ∧
        ∀ u ∈ Icc (r - d) (r + d), ∀ n : ℕ,
          ‖charFun (P j).measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * (u - m j) ^ 2 / 4) := by
  let K := Icc (r - d) (r + d)
  have hK : IsCompact K := isCompact_Icc
  have hrK : r ∈ K := ⟨by linarith, by linarith⟩
  have hq : Continuous (characteristicSquare Q) :=
    continuous_iff_continuousAt.2 (fun x => (characteristicSquare_hasDerivAt Q x).continuousAt)
  have hqs : ∀ j, ContinuousOn (characteristicSquare (P j)) K := fun j =>
    (continuous_iff_continuousAt.2 (fun x => (characteristicSquare_hasDerivAt (P j) x).continuousAt)).continuousOn
  obtain ⟨m, hm, hmlim⟩ := exists_convergent_compact_maximizers (fun j => characteristicSquare (P j))
    (characteristicSquare Q) K hK r hrK hqs hq hstrict
    (compact_characteristicSquare_convergence P Q hW3 K hK)
  have hcurvU := compact_characteristicSquareCurvature_convergence P Q hW3 K hK
  have hecurv : ∀ᶠ j in atTop, ∀ x ∈ K, characteristicSquareCurvature (P j) x ≤ -1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hcurvU) (1 / 2) (by norm_num)] with j hj
    intro x hx
    have hh := hj x hx
    rw [Real.dist_eq] at hh
    have hpoint := hcurv x hx
    have hab := abs_lt.1 hh
    linarith
  have hem : ∀ᶠ j in atTop, m j ∈ Ioo (r - d) (r + d) :=
    hmlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨m, hmlim, ?_⟩
  filter_upwards [hecurv, hem] with j hj hmem
  refine ⟨hmem, ?_⟩
  intro u hu n
  exact characteristic_peak_envelope (P j) (r - d) (r + d) (m j) hmem (hm j).2 hj u hu n

theorem actual_moving_resonance_envelopes (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, thirdMoment (P j) ≤ B)
    (r : ℝ) (hr : r ≠ 0) (hres : r ∈ resonanceSubgroup Q.measure) :
    ∃ (d : ℝ) (m : ℕ → ℝ), 0 < d ∧ d ≤ |r| / 2 ∧ Tendsto m atTop (𝓝 r) ∧
      ∀ᶠ j in atTop, m j ∈ Ioo (r - d) (r + d) ∧
        ∀ u ∈ Icc (r - d) (r + d), ∀ n : ℕ,
          ‖charFun (P j).measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * (u - m j) ^ 2 / 4) := by
  obtain ⟨d, hd, hdr, hcurv, hstrict⟩ := resonance_neighborhood Q r hr hres
  obtain ⟨m, hm, he⟩ := actual_moving_resonance_envelopes_on P Q hw hW3 B hB r d hd hcurv hstrict
  exact ⟨d, m, hd, hdr, hm, he⟩

end BerryEsseen
