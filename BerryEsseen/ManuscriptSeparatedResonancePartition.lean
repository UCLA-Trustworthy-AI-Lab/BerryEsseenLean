import BerryEsseen.ManuscriptResonancePartition

/-! The manuscript's final separation choice: shrink the low-frequency radius
so that even twice that radius contains no nonzero resonance. Consequently the
entire resonance intervals, not just their intersections, lie in the annulus. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The original low-frequency estimate may be restricted to this radius.
The stronger isolation on twice the radius will separate every closed cell. -/
theorem manuscript_low_resonance_isolation (Q : StandardizedLaw) (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧
      ∀ u, |u| ≤ 2 * d → u ∈ resonanceSubgroup Q.measure → u = 0 := by
  obtain ⟨g, hg, hgap⟩ := manuscript_resonance_gap Q
  let d := min δ (g / 4)
  have hd : 0 < d := lt_min hδ (div_pos hg (by norm_num))
  refine ⟨d, hd, min_le_left _ _, ?_⟩
  intro u hu hres
  by_contra hu0
  have h := hgap u hres hu0
  have hdg : d ≤ g / 4 := min_le_right _ _
  linarith

def manuscriptFrequencyAnnulus (d T : ℝ) : Set ℝ :=
  Icc (-T) T ∩ {u : ℝ | d ≤ |u|}

structure ManuscriptSeparatedResonancePartition (Q : StandardizedLaw) (d T : ℝ)
    extends ManuscriptResonancePartition Q (manuscriptFrequencyAnnulus d T) T where
  cells_disjoint_low : ∀ r ∈ centers,
    Disjoint (Icc (r - radius r) (r + radius r)) (Icc (-d) d)

namespace ManuscriptSeparatedResonancePartition

/-- The actual closed cells lie wholly in the annulus. This proof consumes
the disjointness from the closed low-frequency interval. -/
theorem cells_subset_annulus {Q : StandardizedLaw} {d T : ℝ}
    (D : ManuscriptSeparatedResonancePartition Q d T) :
    ∀ r ∈ D.centers, Icc (r - D.radius r) (r + D.radius r) ⊆
      manuscriptFrequencyAnnulus d T := by
  intro r hr u hu
  have hT := D.cells_inside r hr hu
  refine ⟨⟨hT.1.le, hT.2.le⟩, ?_⟩
  have hnot : u ∉ Icc (-d) d := fun hv => Set.disjoint_left.1 (D.cells_disjoint_low r hr) hu hv
  exact (lt_of_not_ge (fun h => hnot (abs_le.1 h))).le

/-- Exact full-cell decomposition: the intersections with the annulus
disappear because the entire closed cells are already in it. -/
theorem integral_decomposition {Q : StandardizedLaw} {d T : ℝ}
    (D : ManuscriptSeparatedResonancePartition Q d T) (f : ℝ → ℝ)
    (hf : IntegrableOn f (manuscriptFrequencyAnnulus d T)) :
    (∫ u in manuscriptFrequencyAnnulus d T, f u) =
      (∫ u in D.toManuscriptResonancePartition.remainder, f u) +
        ∑ r ∈ D.centers, ∫ u in Icc (r - D.radius r) (r + D.radius r), f u := by
  classical
  have hK : MeasurableSet (manuscriptFrequencyAnnulus d T) :=
    measurableSet_Icc.inter (isClosed_le continuous_const continuous_abs).measurableSet
  rw [D.toManuscriptResonancePartition.integral_decomposition hK f hf]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hsub : Ioo (r - D.radius r) (r + D.radius r) ⊆ manuscriptFrequencyAnnulus d T :=
    Ioo_subset_Icc_self.trans (D.cells_subset_annulus r hr)
  rw [inter_eq_right.2 hsub, integral_Icc_eq_integral_Ioo]

end ManuscriptSeparatedResonancePartition

/-- Strengthen the existing generic partition only for the manuscript annulus.
The generic arbitrary-compact API is not restricted. -/
theorem manuscript_separated_resonance_partition_exists (Q : StandardizedLaw) (d T : ℝ)
    (hd : 0 < d)
    (hisolated : ∀ u, |u| ≤ 2 * d → u ∈ resonanceSubgroup Q.measure → u = 0)
    (hT : T ∉ resonanceSubgroup Q.measure) (hnegT : -T ∉ resonanceSubgroup Q.measure)
    (d₀ : ℝ → ℝ)
    (hd₀ : ∀ r ∈ manuscriptFrequencyAnnulus d T, r ∈ resonanceSubgroup Q.measure → 0 < d₀ r)
    (hdaway : ∀ r ∈ manuscriptFrequencyAnnulus d T, r ∈ resonanceSubgroup Q.measure → d₀ r ≤ |r| / 2) :
    ∃ D : ManuscriptSeparatedResonancePartition Q d T,
      ∀ r ∈ D.centers, D.radius r ≤ d₀ r := by
  have hK : IsCompact (manuscriptFrequencyAnnulus d T) :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  obtain ⟨D, hD⟩ := manuscript_resonance_partition_exists Q (manuscriptFrequencyAnnulus d T)
    hK T hT hnegT (fun _ hu => abs_le.2 hu.1) d₀ hd₀ hdaway
  have hsep : ∀ r ∈ D.centers,
      Disjoint (Icc (r - D.radius r) (r + D.radius r)) (Icc (-d) d) := by
    intro r hr
    have hmem := (D.centers_spec r).1 hr
    have hr0 : r ≠ 0 := by
      intro he
      have hh := hmem.1.2
      change d ≤ |r| at hh
      rw [he, abs_zero] at hh
      linarith
    have hrfar : 2 * d < |r| := lt_of_not_ge (fun h => hr0 (hisolated r h hmem.2))
    apply Set.disjoint_left.2
    intro u hu hulow
    have hur : |r - u| ≤ D.radius r := abs_le.2 ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have htriangle := abs_sub_le r u 0
    simp only [sub_zero] at htriangle
    have hlu : |u| ≤ d := abs_le.2 hulow
    linarith [D.radius_away r hr]
  exact ⟨⟨D, hsep⟩, hD⟩

/-- T > d makes the low interval a genuine part of the chosen cutoff.
The only shared endpoints have zero Lebesgue measure, so the decomposition
is exact with the closed low interval and the closed annulus. -/
theorem manuscript_low_annulus_integral_decomposition (d T : ℝ) (hdT : d < T)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc (-T) T)) :
    (∫ u in Icc (-T) T, f u) = (∫ u in Icc (-d) d, f u) +
      ∫ u in manuscriptFrequencyAnnulus d T, f u := by
  have hsub : Ioo (-d) d ⊆ Icc (-T) T := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have he := integral_inter_add_diff (s := Icc (-T) T) measurableSet_Ioo hf
    (t := Ioo (-d) d)
  rw [inter_eq_right.2 hsub, ← integral_Icc_eq_integral_Ioo] at he
  have hsets : Icc (-T) T \ Ioo (-d) d = manuscriptFrequencyAnnulus d T := by
    ext u
    simp only [mem_diff, mem_Ioo, manuscriptFrequencyAnnulus, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hu, hnot⟩
      refine ⟨hu, le_of_not_gt ?_⟩
      intro hlt
      exact hnot (abs_lt.1 hlt)
    · rintro ⟨hu, ha⟩
      exact ⟨hu, fun hlt => (not_lt_of_ge ha) (abs_lt.2 hlt)⟩
  rw [hsets] at he
  exact he.symm

end BerryEsseen
