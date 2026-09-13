import BerryEsseen.PublishedEsseenMoment

/-! Esseen's fixed-law Kolmogorov asymptotic, cited as eq:esseen-limit in
the manuscript. The exact published statement is Mattner--Shevtsova,
ALEA 16 (2019), printed p. 491, equation (1.5), with the span convention
in the preceding paragraph: https://alea.impa.br/articles/v16/16-19.pdf .

This is an explicit external theorem parameter, not a Lean proof of Esseen's
classical theorem. The law is fixed, the span is maximal (zero for a
nonlattice law), and the error is the actual Kolmogorov supremum. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- Esseen (1945, 1956), as explicitly restated in the cited published
equation (1.5). No uniformity in the summand distribution is asserted. -/
structure PublishedEsseenFixedLawAsymptotic : Prop where
  limit : ∀ (P : StandardizedLaw) (h : ℝ), IsMaximalSpan P h →
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * sSup (range (discrepancy P n)))
      atTop (𝓝 (phi0 / 6 * (|signedThirdMoment P| + 3 * h)))

/-- The actual Esseen two-point measure has maximal span equal to the
distance between its two positive-mass atoms. -/
theorem manuscript_esseen_maximal_span : IsMaximalSpan esseenLaw hE := by
  refine ⟨hE_pos.le, fun _ => esseen_lattice_span, ?_⟩
  intro d hd
  obtain ⟨hd, a, ha⟩ := hd
  have hleft : -aE ∈ esseenLaw.measure.support := by
    change -aE ∈ esseenMeasure.support
    rw [esseen_support]
    simp
  have hright : bE ∈ esseenLaw.measure.support := by
    change bE ∈ esseenMeasure.support
    rw [esseen_support]
    simp
  obtain ⟨k, hk⟩ := ha (-aE) hleft
  obtain ⟨l, hl⟩ := ha bE hright
  have hdiff : hE = ((l - k : ℤ) : ℝ) * d := by
    push_cast
    linarith [span_identity]
  have hpos : (0 : ℝ) < ((l - k : ℤ) : ℝ) := by
    apply (mul_pos_iff_of_pos_right hd).mp
    rw [← hdiff]
    exact hE_pos
  have hint : (0 : ℤ) < l - k := by exact_mod_cast hpos
  have hone : (1 : ℝ) ≤ ((l - k : ℤ) : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ l - k by omega)
  have hm := mul_le_mul_of_nonneg_right hone hd.le
  simpa only [one_mul, ← hdiff] using hm

theorem manuscript_normalized_sup_eq_scaled_sup
    (P : StandardizedLaw) (n : ℕ) :
    sSup (range (normalizedDiscrepancy P n)) =
      (Real.sqrt (n : ℝ) * sSup (range (discrepancy P n))) / thirdMoment P := by
  have he : normalizedDiscrepancy P n =
      (fun x => (Real.sqrt (n : ℝ) / thirdMoment P) • discrepancy P n x) := by
    funext x
    unfold normalizedDiscrepancy
    simp only [smul_eq_mul]
    ring
  rw [he]
  change (⨆ x : ℝ, (Real.sqrt (n : ℝ) / thirdMoment P) • discrepancy P n x) = _
  rw [← Real.smul_iSup_of_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (thirdMoment_pos P).le) (discrepancy P n)]
  simp only [smul_eq_mul]
  change (Real.sqrt (n : ℝ) / thirdMoment P) * sSup (range (discrepancy P n)) = _
  ring

/-- The manuscript's original fixed-law route: specialize the classical
formula to the actual Esseen law and use its proved moment identities. -/
theorem original_manuscript_esseen_constant_tendsto
    (E : PublishedEsseenFixedLawAsymptotic) :
    Tendsto (fun n : ℕ => sSup (range (normalizedDiscrepancy esseenLaw n)))
      atTop (𝓝 cE) := by
  have hlim := (E.limit esseenLaw hE manuscript_esseen_maximal_span).div_const
    (thirdMoment esseenLaw)
  have hvalue : (phi0 / 6 * (|signedThirdMoment esseenLaw| + 3 * hE)) /
      thirdMoment esseenLaw = cE := by
    rw [signedThirdMoment_esseen, abs_of_pos kappaE_pos, thirdMoment_esseen]
    have hbeta : 0 < betaE := by simpa only [thirdMoment_esseen] using thirdMoment_pos esseenLaw
    apply (div_eq_iff hbeta.ne').mpr
    nlinarith only [esseen_peak_identity]
  simpa only [← manuscript_normalized_sup_eq_scaled_sup, hvalue] using hlim

end BerryEsseen
