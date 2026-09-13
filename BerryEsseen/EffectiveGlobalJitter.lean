import BerryEsseen.GlobalSmoothingBudget
import BerryEsseen.EffectiveGlobalSpectralGap

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def globalJitterDiscrepancy (P : StandardizedLaw) (ℓ : ℕ) (h : ℝ) : ℝ :=
  sSup (Set.range (fun x : ℝ => |cdf (iidSumLaw P.measure ℓ ∗ uniformJitter h) x -
    edgeworthCDF ℓ (signedThirdMoment P) (x / Real.sqrt (ℓ : ℝ))|))

theorem effective_global_jitter_pointwise (S : PublishedSignedSmoothing) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hβ : thirdMoment P ≤ 1.84)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (h : ℝ) (hh : h ∈ Ioc 0 5) (hlat : IsLatticeSpan Q h)
    (hgap : ∀ u : ℝ, |u| ≤ appendixGlobalCutoff →
      1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) →
        ‖charFun P.measure u‖ ≤ 1 - appendixGlobalGap)
    (n ℓ : ℕ) (hn : appendixNConf ≤ n) (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) (x : ℝ) :
    Real.sqrt (ℓ : ℝ) * |cdf (iidSumLaw P.measure ℓ ∗ uniformJitter h) x -
      edgeworthCDF ℓ (signedThirdMoment P) (x / Real.sqrt (ℓ : ℝ))| ≤ Real.exp (-19 * appendixA) := by
  have hb := appendix_global_sample_bounds n ℓ hn hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓ2 : 2 ≤ ℓ := by omega
  have hr : 0 < Real.sqrt (ℓ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < ℓ by omega))
  have hpeaks (j : ℤ) (hj0 : j ≠ 0)
      (hj : |(j : ℝ) * (2 * Real.pi / h)| ≤ appendixGlobalCutoff + 1 / 1000) :
      ∃ m : ℝ, |m - (j : ℝ) * (2 * Real.pi / h)| ≤ appendixDerivativeError ∧
        ∀ u ∈ globalResonanceCell h j, ∀ m₀ : ℕ, ‖charFun P.measure u‖ ^ m₀ ≤ globalPeakGaussian m₀ m u := by
    obtain ⟨m, hm, hc, hd, hmax, huniq, henv⟩ := effective_global_peak K P Q hP hQ
      (hβ.trans (by norm_num)) hW hv h hlat j hj
    exact ⟨m, hd, henv⟩
  have hF := global_fourier_integral P h appendixGlobalCutoff appendixDerivativeError appendixGlobalGap hh
    appendix_global_cutoff_ge_ten appendix_derivative_error_small.1.le hβ hP hgap hpeaks ℓ hℓ2
  let L := Real.sqrt (ℓ : ℝ) * appendixGlobalCutoff
  have hL : 0 < L := mul_pos hr (Real.exp_pos _)
  have hsm := effective_jitter_signed_smoothing S P ℓ hℓ1 hβ h L hL hF.1 (x / Real.sqrt (ℓ : ℝ))
  have hsm' := mul_le_mul_of_nonneg_left (hsm.trans (add_le_add
    (mul_le_mul_of_nonneg_left hF.2 (by positivity : (0 : ℝ) ≤ 1 / 4)) le_rfl)) hr.le
  have hfinal := hsm'.trans ((appendix_global_smoothing_budget n ℓ hn hℓ).trans (appendix_global_final_budget n ℓ hn hℓ))
  rw [normalizedJitteredSumLaw_cdf P ℓ hℓ1 h, mul_div_cancel₀ _ hr.ne', spanJitter, if_pos hh.1] at hfinal
  exact hfinal

theorem effective_global_jitter_from_lattice (S : PublishedSignedSmoothing) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hβ : thirdMoment P ≤ 1.84)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (h : ℝ) (hh : h ∈ Ioc 0 5) (hlat : IsLatticeSpan Q h)
    (hgap : ∀ u : ℝ, |u| ≤ appendixGlobalCutoff →
      1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) →
        ‖charFun P.measure u‖ ≤ 1 - appendixGlobalGap)
    (n ℓ : ℕ) (hn : appendixNConf ≤ n) (hℓ : (n : ℝ) / 2 ≤ (ℓ : ℝ)) :
    Real.sqrt (ℓ : ℝ) * globalJitterDiscrepancy P ℓ h ≤ Real.exp (-19 * appendixA) := by
  have hb := appendix_global_sample_bounds n ℓ hn hℓ
  have hr : 0 < Real.sqrt (ℓ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < ℓ by omega))
  have hsup : globalJitterDiscrepancy P ℓ h ≤ Real.exp (-19 * appendixA) / Real.sqrt (ℓ : ℝ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    apply (le_div_iff₀ hr).mpr
    simpa only [mul_comm] using effective_global_jitter_pointwise S K P Q hP hQ hβ hW hv h hh hlat hgap n ℓ hn hℓ x
  have hmul := mul_le_mul_of_nonneg_left hsup hr.le
  simpa only [mul_div_cancel₀ _ hr.ne'] using hmul

theorem effective_global_jitter (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) (hviol : ¬ BoundAt P n) :
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
      ∀ ℓ : ℕ, (n : ℝ) / 2 ≤ (ℓ : ℝ) →
        Real.sqrt (ℓ : ℝ) * globalJitterDiscrepancy P ℓ h ≤ Real.exp (-19 * appendixA) := by
  obtain ⟨Q, F, h, Z, hprob, hcard, hsQ, hbF, haF, hh, hlat, hmax, hW, hm, hv,
    hthird, hmap, hsZ, hZβ, hZmax, hgap⟩ := effective_global_spectral_gap H S E K P n hn hsupp hviol
  letI : IsProbabilityMeasure Q := hprob
  have hP : ∀ᵐ x ∂P.measure, |x| ≤ 6 := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact abs_le.mpr (hsupp hx)
  have hQ : ∀ᵐ x ∂Q, |x| ≤ 13 := by
    filter_upwards [Q.support_mem_ae] with x hx
    exact (hbF x (hsQ hx)).le
  have hnlarge := (appendix_sample_size_bounds n (appendix_conf_sample_size n hn).1).1
  have hn1 : 1 ≤ n := by omega
  have hβ : thirdMoment P ≤ 1.84 := by
    have hvio := hviol
    rw [BoundAt_iff_normalized P n hn1] at hvio
    push_neg at hvio
    obtain ⟨x, hx⟩ := hvio
    exact ((normalized_violation_momentCutoff H P n hn1 x hx).trans momentCutoff_bounds.2).le
  refine ⟨Q, F, h, Z, hprob, hcard, hsQ, hbF, haF, hh, hlat, hmax, hW, hm, hv,
    hthird, hmap, hsZ, hZβ, hZmax, hgap, ?_⟩
  intro ℓ hℓ
  exact effective_global_jitter_from_lattice S K P Q hP hQ hβ hW hv h ⟨hlat.1, hh.2⟩ hlat hgap n ℓ hn hℓ

end BerryEsseen
