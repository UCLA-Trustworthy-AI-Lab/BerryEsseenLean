import BerryEsseen.ManuscriptResonanceGeometry

/-! A finite family of disjoint resonance intervals and its compact,
nonresonant remainder. The cutoff endpoints are chosen off the subgroup. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

structure ManuscriptResonancePartition (Q : StandardizedLaw) (K : Set ℝ) (T : ℝ) where
  centers : Finset ℝ
  radius : ℝ → ℝ
  centers_spec : ∀ r, r ∈ centers ↔ r ∈ K ∧ r ∈ resonanceSubgroup Q.measure
  radius_pos : ∀ r ∈ centers, 0 < radius r
  radius_away : ∀ r ∈ centers, radius r ≤ |r| / 2
  cells_inside : ∀ r ∈ centers, Icc (r - radius r) (r + radius r) ⊆ Ioo (-T) T
  cells_disjoint : Set.Pairwise (centers : Set ℝ)
    (fun r v => Disjoint (Icc (r - radius r) (r + radius r))
      (Icc (v - radius v) (v + radius v)))

namespace ManuscriptResonancePartition

def remainder {Q : StandardizedLaw} {K : Set ℝ} {T : ℝ}
    (D : ManuscriptResonancePartition Q K T) : Set ℝ :=
  K \ ⋃ r ∈ D.centers, Ioo (r - D.radius r) (r + D.radius r)

theorem remainder_compact {Q : StandardizedLaw} {K : Set ℝ} {T : ℝ}
    (D : ManuscriptResonancePartition Q K T) (hK : IsCompact K) :
    IsCompact D.remainder :=
  hK.diff (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo)

theorem remainder_nonresonant {Q : StandardizedLaw} {K : Set ℝ} {T : ℝ}
    (D : ManuscriptResonancePartition Q K T) :
    ∀ r ∈ D.remainder, r ∉ resonanceSubgroup Q.measure := by
  intro r hr hres
  have hs := (D.centers_spec r).2 ⟨hr.1, hres⟩
  apply hr.2
  exact mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨hs,
    ⟨by linarith [D.radius_pos r hs], by linarith [D.radius_pos r hs]⟩⟩⟩

/-- The exact integral decomposition consumes pairwise disjointness. The
intervals are intersected with K; their endpoints belong to the remainder. -/
theorem integral_decomposition {Q : StandardizedLaw} {K : Set ℝ} {T : ℝ}
    (D : ManuscriptResonancePartition Q K T) (hK : MeasurableSet K)
    (f : ℝ → ℝ) (hf : IntegrableOn f K) :
    (∫ u in K, f u) = (∫ u in D.remainder, f u) +
      ∑ r ∈ D.centers, ∫ u in K ∩ Ioo (r - D.radius r) (r + D.radius r), f u := by
  classical
  let U : Set ℝ := ⋃ r ∈ D.centers, Ioo (r - D.radius r) (r + D.radius r)
  have hU : MeasurableSet U := (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo).measurableSet
  have he := integral_inter_add_diff hU hf
  have hsets : K ∩ U = ⋃ r ∈ D.centers, K ∩ Ioo (r - D.radius r) (r + D.radius r) := by
    simp only [U, inter_iUnion]
  have hp : Set.Pairwise (D.centers : Set ℝ)
      (fun r v => Disjoint (K ∩ Ioo (r - D.radius r) (r + D.radius r))
        (K ∩ Ioo (v - D.radius v) (v + D.radius v))) := by
    intro r hr v hv hrv
    exact (D.cells_disjoint hr hv hrv).mono
      (inter_subset_right.trans Ioo_subset_Icc_self) (inter_subset_right.trans Ioo_subset_Icc_self)
  rw [hsets, integral_biUnion_finset D.centers
    (fun _ _ => hK.inter measurableSet_Ioo) hp
    (fun _ _ => hf.mono_set inter_subset_left)] at he
  change _ + (∫ u in D.remainder, f u) = _ at he
  linarith

end ManuscriptResonancePartition

/-- Shrink the already proved local resonance intervals using the separation
from q''(0), and the distance to the nonresonant cutoff endpoints. -/
theorem manuscript_resonance_partition_exists (Q : StandardizedLaw)
    (K : Set ℝ) (hK : IsCompact K) (T : ℝ)
    (hT : T ∉ resonanceSubgroup Q.measure) (hnegT : -T ∉ resonanceSubgroup Q.measure)
    (hbound : ∀ r ∈ K, |r| ≤ T) (d₀ : ℝ → ℝ)
    (hd₀ : ∀ r ∈ K, r ∈ resonanceSubgroup Q.measure → 0 < d₀ r)
    (hdaway : ∀ r ∈ K, r ∈ resonanceSubgroup Q.measure → d₀ r ≤ |r| / 2) :
    ∃ D : ManuscriptResonancePartition Q K T,
      ∀ r ∈ D.centers, D.radius r ≤ d₀ r := by
  classical
  let s := (manuscript_finite_resonances Q K hK).toFinset
  have hs : ∀ r, r ∈ s ↔ r ∈ K ∧ r ∈ resonanceSubgroup Q.measure := by
    intro r
    simp only [s, Set.Finite.mem_toFinset, mem_inter_iff, SetLike.mem_coe]
  obtain ⟨δ, hδ, hgap⟩ := manuscript_resonance_gap Q
  have hrT : ∀ r ∈ s, |r| < T := by
    intro r hr
    have hmem := (hs r).1 hr
    apply lt_of_le_of_ne (hbound r hmem.1)
    intro he
    rcases le_total 0 r with hr0 | hr0
    · rw [abs_of_nonneg hr0] at he
      exact hT (he ▸ hmem.2)
    · rw [abs_of_nonpos hr0] at he
      have her : r = -T := by linarith
      exact hnegT (her ▸ hmem.2)
  let d : ℝ → ℝ := fun r => min (d₀ r) (min (δ / 4) ((T - |r|) / 2))
  have hdpos : ∀ r ∈ s, 0 < d r := by
    intro r hr
    have hmem := (hs r).1 hr
    exact lt_min (hd₀ r hmem.1 hmem.2)
      (lt_min (div_pos hδ (by norm_num)) (div_pos (sub_pos.2 (hrT r hr)) (by norm_num)))
  have hds (r : ℝ) : d r ≤ d₀ r := min_le_left _ _
  have hdδ (r : ℝ) : d r ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdT (r : ℝ) : d r ≤ (T - |r|) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hdaway' : ∀ r ∈ s, d r ≤ |r| / 2 := by
    intro r hr
    have hmem := (hs r).1 hr
    exact (hds r).trans (hdaway r hmem.1 hmem.2)
  have hinside : ∀ r ∈ s, Icc (r - d r) (r + d r) ⊆ Ioo (-T) T := by
    intro r hr u hu
    have hrb := hrT r hr
    have hdt := hdT r
    have har := neg_abs_le r
    have hbr := le_abs_self r
    constructor <;> linarith [hu.1, hu.2]
  have hdis : Set.Pairwise (s : Set ℝ)
      (fun r v => Disjoint (Icc (r - d r) (r + d r)) (Icc (v - d v) (v + d v))) := by
    intro r hr v hv hrv
    apply Set.disjoint_left.2
    intro u hur huv
    have hgr := hgap (r - v)
      ((resonanceSubgroup Q.measure).sub_mem ((hs r).1 hr).2 ((hs v).1 hv).2)
      (sub_ne_zero.2 hrv)
    have hdist : |r - v| ≤ d r + d v := by
      apply abs_le.2
      constructor <;> linarith [hur.1, hur.2, huv.1, huv.2]
    linarith [hdδ r, hdδ v]
  exact ⟨⟨s, d, hs, hdpos, hdaway', hinside, hdis⟩, fun r _ => hds r⟩

end BerryEsseen
