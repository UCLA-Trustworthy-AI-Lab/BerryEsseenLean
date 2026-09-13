import BerryEsseen.IdentificationSign

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The original effective identification statement with the rounded law and
its maximal span retained in the conclusion. All global-jitter properties and
identification bounds below refer to this same `Q`, `F`, `h`, and `Z`. -/
theorem effective_identification_with_global_jitter (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality) (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) (z : ℝ)
    (hpos : cE * thirdMoment P < Real.sqrt (n : ℝ) * (normalizedSumCDF P n z - normalCDF z)) :
    ∃ (Q : Measure ℝ) (F : Finset ℝ) (h : ℝ) (Z : StandardizedLaw),
      IsProbabilityMeasure Q ∧ F.card < 2000 ∧ Q.support ⊆ (F : Set ℝ) ∧
      (∀ x ∈ F, |x| < 13) ∧ (∀ x ∈ F, appendixRetention ≤ Q.real {x}) ∧
      h ∈ Icc (Real.pi / 500) 5 ∧ IsLatticeSpan Q h ∧
      (∀ d : ℝ, IsLatticeSpan Q d → d ≤ h) ∧
      wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      |rawMean Q| ≤ (10 : ℝ) ^ 5 * appendixRetention ∧
      |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention ∧
      |rawThirdAbsoluteMoment Q - thirdMoment P| +
        |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 2 * (10 : ℝ) ^ 9 * appendixRetention ∧
      Z.measure = standardizedMeasure Q (rawMean Q) (rawStdDev Q) ∧
      Z.measure.support ⊆ Icc (-15) 15 ∧ thirdMoment Z < 2 ∧
      IsMaximalSpan Z (h / rawStdDev Q) ∧
      (∀ u : ℝ, |u| ≤ appendixGlobalCutoff →
        1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) →
        ‖charFun P.measure u‖ ≤ 1 - appendixGlobalGap) ∧
      (∀ ℓ : ℕ, (n : ℝ) / 2 ≤ (ℓ : ℝ) →
        Real.sqrt (ℓ : ℝ) * globalJitterDiscrepancy P ℓ h ≤ Real.exp (-19 * appendixA)) ∧
      wassersteinOne P.measure esseenLaw.measure ≤ Real.exp (-7 * appendixA) ∧
      |h - hE| ≤ Real.exp (-7 * appendixA) ∧
      |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA) ∧
      |signedThirdMoment P - kappaE| ≤ Real.exp (-6 * appendixA) ∧
      |signedSecondMoment P - signedSecondMoment esseenLaw| ≤ Real.exp (-6 * appendixA) ∧
      z ^ 2 ≤ Real.exp (-5 * appendixA) ∧
      ∀ ℓ : ℕ, (n : ℝ) / 2 ≤ (ℓ : ℝ) → ∀ x : ℝ,
        Real.sqrt (ℓ : ℝ) * |cdf (iidSumLaw P.measure ℓ ∗ uniformJitter h) x -
          edgeworthCDF ℓ (signedThirdMoment P) (x / Real.sqrt (ℓ : ℝ))| ≤ Real.exp (-19 * appendixA) := by
  have hnlarge := (appendix_sample_size_bounds n (appendix_conf_sample_size n hn).1).1
  have hn1 : 1 ≤ n := by omega
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hviol : ¬ BoundAt P n := by
    intro hB
    have hh := hB z
    have he : discrepancy P n z = |normalizedSumCDF P n z - normalCDF z| := by
      rw [discrepancy, normalizedSumCDF, cdf_eq_real]
      rfl
    rw [he] at hh
    have hh' := (le_div_iff₀ hr).mp hh
    have hpos' := mul_le_mul_of_nonneg_left (le_abs_self (normalizedSumCDF P n z - normalCDF z)) hr.le
    nlinarith only [hh', hpos', hpos]
  have hβ : thirdMoment P ≤ 1.84 := by
    have hvio := hviol
    rw [BoundAt_iff_normalized P n hn1] at hvio
    push_neg at hvio
    obtain ⟨x, hx⟩ := hvio
    exact ((normalized_violation_momentCutoff H P n hn1 x hx).trans momentCutoff_bounds.2).le
  obtain ⟨Q, F, h, Z, hprob, hcard, hsQ, hbF, haF, hh, hlat, hmax, hW, hm, hv,
    hthird, hmap, hsZ, hZβ, hZmax, hgap⟩ := effective_global_spectral_gap H S E K P n hn hsupp hviol
  letI : IsProbabilityMeasure Q := hprob
  have hP : ∀ᵐ x ∂P.measure, |x| ≤ 6 := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact abs_le.mpr (hsupp hx)
  have hQ : ∀ᵐ x ∂Q, |x| ≤ 13 := by
    filter_upwards [Q.support_mem_ae] with x hx
    exact (hbF x (hsQ hx)).le
  have hjitter (ℓ : ℕ) (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) (x : ℝ) :
      Real.sqrt (ℓ : ℝ) * |cdf (iidSumLaw P.measure ℓ ∗ uniformJitter h) x -
        edgeworthCDF ℓ (signedThirdMoment P) (x / Real.sqrt (ℓ : ℝ))| ≤ Real.exp (-19 * appendixA) :=
    effective_global_jitter_pointwise S K P Q hP hQ hβ hW hv h ⟨hlat.1, hh.2⟩ hlat hgap n ℓ hn hℓ x
  have hnn : (n : ℝ) / 2 ≤ (n : ℝ) := by have hh := Nat.cast_nonneg (α := ℝ) n; linarith
  have henv := effective_maximizer_envelope P n hn h ⟨hlat.1, hh.2⟩ (hβ.trans (by norm_num)) (hjitter n hnn) z hpos
  have hD := envelope_implies_small_lattice_deficit P h z (Real.exp (-18 * appendixA)) hlat.1.le (Real.exp_pos _).le henv
  have hσ := (effective_rounded_moment_bounds K P Q hP hQ hβ hW).2.1
  have hstdD := effective_standardized_lattice_deficit E P Q Z h ⟨hlat.1.le, hh.2⟩ hσ hmap hZmax hv hthird hD
  have hstdlat : IsLatticeSpan Z.measure (h / rawStdDev Q) := by
    rw [hmap]
    exact latticeSpan_standardized Q (rawMean Q) (rawStdDev Q) h (by linarith [hσ.1]) hlat
  obtain ⟨ε, hε, hWε, hspan⟩ := effective_lattice_identification_transfer K P Q Z h hQ hW hm hv hσ hmap hsZ hZβ.le hstdlat hstdD
  obtain ⟨hβE, hκE, hME⟩ := identification_moments_from_wasserstein K P hP ε hε hWε
  have hzfour := manuscript_effective_violation_threshold_four U P n hn1 z hpos
  obtain ⟨hεpos, hz⟩ := effective_identification_sign_and_threshold P h z ε hzfour hε hspan hβE hκE henv
  rw [hεpos] at hWε hκE hME
  simp only [one_mul, Measure.map_id'] at hWε hκE hME
  have hglobal (ℓ : ℕ) (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
      Real.sqrt (ℓ : ℝ) * globalJitterDiscrepancy P ℓ h ≤ Real.exp (-19 * appendixA) :=
    effective_global_jitter_from_lattice S K P Q hP hQ hβ hW hv h
      ⟨hlat.1, hh.2⟩ hlat hgap n ℓ hn hℓ
  exact ⟨Q, F, h, Z, hprob, hcard, hsQ, hbF, haF, hh, hlat, hmax, hW, hm, hv,
    hthird, hmap, hsZ, hZβ, hZmax, hgap, hglobal, hWε, hspan, hβE, hκE, hME, hz, hjitter⟩

/-- The existing numerical interface is a projection of the original statement
that retains the rounded law and its span. -/
theorem effective_identification (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality) (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) (z : ℝ)
    (hpos : cE * thirdMoment P < Real.sqrt (n : ℝ) * (normalizedSumCDF P n z - normalCDF z)) :
    ∃ h ∈ Icc (Real.pi / 500) 5,
      wassersteinOne P.measure esseenLaw.measure ≤ Real.exp (-7 * appendixA) ∧
      |h - hE| ≤ Real.exp (-7 * appendixA) ∧
      |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA) ∧
      |signedThirdMoment P - kappaE| ≤ Real.exp (-6 * appendixA) ∧
      |signedSecondMoment P - signedSecondMoment esseenLaw| ≤ Real.exp (-6 * appendixA) ∧
      z ^ 2 ≤ Real.exp (-5 * appendixA) ∧
      ∀ ℓ : ℕ, (n : ℝ) / 2 ≤ (ℓ : ℝ) → ∀ x : ℝ,
        Real.sqrt (ℓ : ℝ) * |cdf (iidSumLaw P.measure ℓ ∗ uniformJitter h) x -
          edgeworthCDF ℓ (signedThirdMoment P) (x / Real.sqrt (ℓ : ℝ))| ≤ Real.exp (-19 * appendixA) := by
  obtain ⟨Q, F, h, Z, hprob, hcard, hsQ, hbF, haF, hh, hlat, hmax, hW, hm, hv,
    hthird, hmap, hsZ, hZβ, hZmax, hgap, hglobal, hWε, hspan, hβE, hκE, hME, hz, hjitter⟩ :=
    effective_identification_with_global_jitter H S E K U P n hn hsupp z hpos
  exact ⟨h, hh, hWε, hspan, hβE, hκE, hME, hz, hjitter⟩

end BerryEsseen
