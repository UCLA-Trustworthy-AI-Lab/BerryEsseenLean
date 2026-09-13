import BerryEsseen.ManuscriptLatticeOutside

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_atom_mem_support (μ : Measure ℝ) (x : ℝ) (hx : μ {x} ≠ 0) :
    x ∈ μ.support := by
  rw [Measure.mem_support_iff_forall]
  intro s hs
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hx)
    (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hs)))

theorem manuscript_lattice_bracket_atoms_positive (P : StandardizedLaw) (a b h δ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = h) (hh : 17 / 10 < h)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ≤ δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6)
    (hgeom : ∀ x ∈ P.measure.support,
      x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) :
    P.measure {-a} ≠ 0 ∧ P.measure {b} ≠ 0 := by
  have hh0 : 0 < h := by linarith
  constructor
  · intro hzero
    have hn : ∀ᵐ x ∂P.measure, x ∈ ({-a}ᶜ : Set ℝ) := by
      rw [ae_iff]
      simpa using hzero
    have hn' := manuscriptNegativeSizeBias_source P _ (measurableSet_singleton (-a)).compl hn
    have hpair : ∀ᵐ z ∂manuscriptSizeBiasedProduct P, 2 * h ≤ z.1 + z.2 := by
      have ht : ∀ᵐ z ∂manuscriptSizeBiasedProduct P, -z.1 ∈ ({-a}ᶜ : Set ℝ) :=
        measurePreserving_fst.quasiMeasurePreserving.ae hn'
      filter_upwards [manuscriptSizeBiasedProduct_support P, ht] with z hz hne
      have hg := manuscript_bracketing_pair_geometry a b h ha hb hab z hz.1 hz.2.1
        (hgeom _ hz.2.2.1) (hgeom _ hz.2.2.2)
      apply hg.2
      left
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · exact hne
      · linarith [hz.1]
    have hd := manuscript_lattice_large_pairs_deficit P h hh0 hκ hpair
    linarith
  · intro hzero
    have hn : ∀ᵐ x ∂P.measure, x ∈ ({b}ᶜ : Set ℝ) := by
      rw [ae_iff]
      simpa using hzero
    have hn' := manuscriptPositiveSizeBias_ae P _ hn
    have hpair : ∀ᵐ z ∂manuscriptSizeBiasedProduct P, 2 * h ≤ z.1 + z.2 := by
      have ht : ∀ᵐ z ∂manuscriptSizeBiasedProduct P, z.2 ∈ ({b}ᶜ : Set ℝ) :=
        measurePreserving_snd.quasiMeasurePreserving.ae hn'
      filter_upwards [manuscriptSizeBiasedProduct_support P, ht] with z hz hne
      have hg := manuscript_bracketing_pair_geometry a b h ha hb hab z hz.1 hz.2.1
        (hgeom _ hz.2.2.1) (hgeom _ hz.2.2.2)
      apply hg.2
      right
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · linarith [hz.2.1]
      · exact hne
    have hd := manuscript_lattice_large_pairs_deficit P h hh0 hκ hpair
    linarith

theorem manuscript_bracket_atoms_force_maximal_span (P : StandardizedLaw) (a b h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = h)
    (hlat : IsLatticeSpan P.measure h)
    (hna : P.measure {-a} ≠ 0) (hnb : P.measure {b} ≠ 0) : IsMaximalSpan P h := by
  refine ⟨hlat.1.le, fun _ => hlat, ?_⟩
  intro d hd
  obtain ⟨hd0, a₀, hdlat⟩ := hd
  have hg := manuscript_positive_lattice_pair_gap a b a₀ d ha hb hd0
    (hdlat (-a) (manuscript_atom_mem_support P.measure (-a) hna))
    (hdlat b (manuscript_atom_mem_support P.measure b hnb))
  simpa only [hab] using hg

theorem manuscript_effective_lattice_bracket (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧
      (∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) ∧
      P.measure {-a} ≠ 0 ∧ P.measure {b} ≠ 0 ∧ IsMaximalSpan P h ∧
      (∫ x, ({-a, b}ᶜ : Set ℝ).indicator (fun y => y ^ 2) x ∂P.measure) ≤ δ := by
  obtain ⟨hh, a₀, ha₀⟩ := hlat
  have hlat : IsLatticeSpan P.measure h := ⟨hh, a₀, ha₀⟩
  have hz := manuscript_effective_lattice_translate_avoids_zero P h δ a₀ hh hβ hκ hD hδ ha₀
  obtain ⟨a, b, ha, hb, hab, hg⟩ := translated_lattice_bracketing a₀ h hh hz
  have hgeom : ∀ x ∈ P.measure.support,
      x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x := fun x hx => hg x (ha₀ x hx)
  have hspan := effective_lattice_span_bounds P h δ hβ hD hδ
  have hatoms := manuscript_lattice_bracket_atoms_positive P a b h δ ha hb hab hspan.1
    hκ hD.2 hδ hgeom
  refine ⟨a, b, ha, hb, hab, ?_, hatoms.1, hatoms.2,
    manuscript_bracket_atoms_force_maximal_span P a b h ha hb hab hlat hatoms.1 hatoms.2, ?_⟩
  · filter_upwards [P.measure.support_mem_ae] with x hx
    exact hgeom x hx
  · have hbnd := manuscript_lattice_outside_second_bound P a b h ha hb hab hκ hgeom
    apply hbnd.trans
    apply (div_le_iff₀ (by positivity : 0 < 3 * h)).mpr
    have hh1 : 1 ≤ 3 * h := by linarith [hspan.1]
    exact hD.2.trans (by nlinarith [mul_nonneg (hD.1.trans hD.2) (sub_nonneg.mpr hh1)])

end BerryEsseen
