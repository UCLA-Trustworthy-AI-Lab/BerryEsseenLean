import BerryEsseen.MovingPeaks
import Mathlib.Topology.DiscreteSubset

/-! The manuscript's isolation argument: q''(0) = -2, continuity and Taylor.
This is deliberately a late module: characteristic derivatives already depend
on the elementary phase subgroup in `Resonances`. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_characteristicSquare_zero (P : StandardizedLaw) :
    characteristicSquare P 0 = 1 := by
  have h := (mem_resonanceSubgroup_iff P.measure 0).1
    (resonanceSubgroup P.measure).zero_mem
  simp only [characteristicSquare, h, one_pow]

theorem manuscript_characteristicSquareSlope_zero (P : StandardizedLaw) :
    characteristicSquareSlope P 0 = 0 := by
  have h1 : weightedCharFun P.measure 1 0 = 0 := by
    rw [weightedCharFun_at_resonance P.measure 0 (resonanceSubgroup P.measure).zero_mem]
    simp only [pow_one, P.mean_zero, Complex.ofReal_zero, zero_mul]
  simp [characteristicSquareSlope, charFunDerivative, h1]

theorem manuscript_characteristicSquareCurvature_zero (P : StandardizedLaw) :
    characteristicSquareCurvature P 0 = -2 :=
  characteristicSquareCurvature_at_resonance P 0 (resonanceSubgroup P.measure).zero_mem

/-- Taylor at zero gives a strict quadratic drop, without choosing support points. -/
theorem manuscript_zero_quadratic_drop (P : StandardizedLaw) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u, |u| ≤ δ →
      characteristicSquare P u ≤ 1 - u ^ 2 / 2 := by
  have hc := (characteristicSquareCurvature_hasDerivAt P 0).continuousAt
  obtain ⟨η, hη, he⟩ := Metric.continuousAt_iff.1 hc 1 zero_lt_one
  let δ := η / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcurv : ∀ u ∈ Icc (-δ) δ, characteristicSquareCurvature P u ≤ -1 := by
    intro u hu
    have huη : dist u 0 < η := by
      rw [Real.dist_eq, sub_zero]
      have huδ : |u| ≤ δ := abs_le.2 hu
      dsimp [δ] at huδ
      linarith
    have hh := he huη
    rw [Real.dist_eq, manuscript_characteristicSquareCurvature_zero] at hh
    have := (abs_lt.1 hh).2
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro u hu
  have h := quadratic_upper_at_critical_point (characteristicSquare P)
    (characteristicSquareSlope P) (characteristicSquareCurvature P)
    (-δ) δ 0 u ⟨by linarith, hδ.le⟩ (abs_le.1 hu)
    (fun x _ => characteristicSquare_hasDerivAt P x)
    (fun x _ => characteristicSquareSlope_hasDerivAt P x)
    hcurv (manuscript_characteristicSquareSlope_zero P)
  simpa only [manuscript_characteristicSquare_zero, sub_zero] using h

theorem manuscript_resonance_gap (P : StandardizedLaw) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ resonanceSubgroup P.measure, u ≠ 0 → δ ≤ |u| := by
  obtain ⟨δ, hδ, hdrop⟩ := manuscript_zero_quadratic_drop P
  refine ⟨δ, hδ, ?_⟩
  intro u hu hu0
  by_contra h
  have hq := hdrop u (le_of_lt (lt_of_not_ge h))
  have hr := (mem_resonanceSubgroup_iff P.measure u).1 hu
  simp only [characteristicSquare, hr, one_pow] at hq
  nlinarith [sq_pos_of_ne_zero hu0]

theorem manuscript_resonanceSubgroup_cyclic (P : StandardizedLaw) :
    ∃ a : ℝ, resonanceSubgroup P.measure = AddSubgroup.zmultiples a := by
  obtain ⟨δ, hδ, hgap⟩ := manuscript_resonance_gap P
  have hdis : Disjoint (resonanceSubgroup P.measure : Set ℝ) (Ioo 0 δ) := by
    apply Set.disjoint_left.2
    intro u hu hut
    have h := hgap u hu hut.1.ne'
    rw [abs_of_pos hut.1] at h
    exact (not_lt_of_ge h) hut.2
  obtain ⟨a, ha⟩ := AddSubgroup.cyclic_of_isolated_zero hδ hdis
  exact ⟨a, by simpa only [← AddSubgroup.zmultiples_eq_closure] using ha⟩

theorem manuscript_resonanceSubgroup_nonnegative_generator (P : StandardizedLaw) :
    ∃ a : ℝ, 0 ≤ a ∧ resonanceSubgroup P.measure = AddSubgroup.zmultiples a := by
  obtain ⟨a, ha⟩ := manuscript_resonanceSubgroup_cyclic P
  refine ⟨|a|, abs_nonneg a, ?_⟩
  by_cases ha0 : 0 ≤ a
  · rwa [abs_of_nonneg ha0]
  · rw [abs_of_neg (lt_of_not_ge ha0), AddSubgroup.zmultiples_neg]
    exact ha

theorem manuscript_lattice_span_dichotomy (P : StandardizedLaw) :
    (resonanceSubgroup P.measure = ⊥ ∧ ∀ d : ℝ, ¬ IsLatticeSpan P.measure d) ∨
    ∃ h : ℝ, IsLatticeSpan P.measure h ∧
      (∀ d : ℝ, IsLatticeSpan P.measure d → d ≤ h) ∧
      resonanceSubgroup P.measure = AddSubgroup.zmultiples (2 * Real.pi / h) := by
  obtain ⟨a, ha0, hgen⟩ := manuscript_resonanceSubgroup_nonnegative_generator P
  rcases eq_or_lt_of_le ha0 with haz | ha
  · left
    have hbot : resonanceSubgroup P.measure = ⊥ := by simpa [← haz] using hgen
    refine ⟨hbot, ?_⟩
    intro d hd
    have hr := latticeSpan_gives_resonance P.measure d hd
    rw [hbot, AddSubgroup.mem_bot] at hr
    exact (div_pos Real.two_pi_pos hd.1).ne' hr
  · right
    obtain ⟨hspan, hmax⟩ := maximal_span_of_positive_generator P a ha hgen
    refine ⟨2 * Real.pi / a, hspan, hmax, ?_⟩
    have he : 2 * Real.pi / (2 * Real.pi / a) = a := by field_simp
    rwa [he]

theorem manuscript_exists_span_and_resonance_multiplier (P : StandardizedLaw) :
    ∃ h : ℝ, 0 ≤ h ∧ (0 < h → IsLatticeSpan P.measure h) ∧
      (∀ d : ℝ, IsLatticeSpan P.measure d → d ≤ h) ∧
      ∀ u : ℝ, u ≠ 0 → ‖charFun P.measure u‖ = 1 → Real.sinc (h * u / 2) = 0 := by
  rcases manuscript_lattice_span_dichotomy P with ⟨hbot, hnonlat⟩ | ⟨h, hspan, hmax, hgen⟩
  · refine ⟨0, le_rfl, fun h => False.elim (lt_irrefl _ h), ?_, ?_⟩
    · intro d hd
      exact False.elim (hnonlat d hd)
    · intro u hu hnorm
      have hmem := (mem_resonanceSubgroup_iff P.measure u).2 hnorm
      rw [hbot, AddSubgroup.mem_bot] at hmem
      exact False.elim (hu hmem)
  · refine ⟨h, hspan.1.le, fun _ => hspan, hmax, ?_⟩
    intro u hu hnorm
    have hmem := (mem_resonanceSubgroup_iff P.measure u).2 hnorm
    rw [hgen, AddSubgroup.mem_zmultiples_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [zsmul_eq_mul] at hk
    have hk0 : k ≠ 0 := by intro hk0; simp [hk0] at hk; exact hu hk.symm
    have he : u = 2 * Real.pi * (k : ℝ) / h := by rw [← hk]; ring
    rw [he]
    exact spanJitter_multiplier_resonance_zero h hspan.1 k hk0

/-- A fixed cutoff can be chosen beyond any prescribed bound with both endpoints
outside the limiting resonance subgroup. -/
theorem manuscript_nonresonant_cutoff (P : StandardizedLaw) (R : ℝ) :
    ∃ T : ℝ, 0 < T ∧ R < T ∧ T ∉ resonanceSubgroup P.measure ∧
      -T ∉ resonanceSubgroup P.measure := by
  obtain ⟨δ, hδ, hgap⟩ := manuscript_resonance_gap P
  let t := max R 0 + 1
  have ht : 0 < t := by dsimp [t]; linarith [le_max_right R 0]
  have hRt : R < t := by dsimp [t]; linarith [le_max_left R 0]
  have hex : ∃ T : ℝ, 0 < T ∧ R < T ∧ T ∉ resonanceSubgroup P.measure := by
    by_cases htres : t ∈ resonanceSubgroup P.measure
    · refine ⟨t + δ / 2, by linarith, by linarith, ?_⟩
      intro hres
      have hm := (resonanceSubgroup P.measure).sub_mem hres htres
      have hd : t + δ / 2 - t ≠ 0 := by linarith
      have h := hgap _ hm hd
      rw [abs_of_pos (by linarith : 0 < t + δ / 2 - t)] at h
      linarith
    · exact ⟨t, ht, hRt, htres⟩
  obtain ⟨T, hT, hRT, hnr⟩ := hex
  refine ⟨T, hT, hRT, hnr, ?_⟩
  intro hneg
  exact hnr (by simpa using (resonanceSubgroup P.measure).neg_mem hneg)

theorem manuscript_resonances_closed (P : StandardizedLaw) :
    IsClosed (resonanceSubgroup P.measure : Set ℝ) := by
  have hc : Continuous (fun u => ‖charFun P.measure u‖) :=
    continuous_iff_continuousAt.2 (fun u => (charFun_hasDerivAt P u).continuousAt.norm)
  have he : (resonanceSubgroup P.measure : Set ℝ) = {u | ‖charFun P.measure u‖ = 1} := by
    ext u
    exact mem_resonanceSubgroup_iff P.measure u
  rw [he]
  exact isClosed_eq hc continuous_const

/-- Compactness is used only to enumerate the discrete resonance set, not to
cover every nonzero frequency by possibly overlapping neighborhoods. -/
theorem manuscript_finite_resonances (P : StandardizedLaw) (K : Set ℝ) (hK : IsCompact K) :
    (K ∩ (resonanceSubgroup P.measure : Set ℝ)).Finite := by
  obtain ⟨δ, hδ, hgap⟩ := manuscript_resonance_gap P
  apply (hK.inter_right (manuscript_resonances_closed P)).finite
  apply isDiscrete_iff_forall_exists_isOpen.2
  intro r hr
  refine ⟨Ioo (r - δ) (r + δ), isOpen_Ioo, ?_⟩
  ext u
  constructor
  · rintro ⟨hu, huK, huRes⟩
    apply mem_singleton_iff.2
    by_contra hur
    have hg := hgap (u - r) ((resonanceSubgroup P.measure).sub_mem huRes hr.2)
      (sub_ne_zero.2 hur)
    have hlt : |u - r| < δ := abs_lt.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    linarith
  · intro hu
    rw [mem_singleton_iff] at hu
    subst u
    exact ⟨⟨by linarith, by linarith⟩, hr⟩

end BerryEsseen
