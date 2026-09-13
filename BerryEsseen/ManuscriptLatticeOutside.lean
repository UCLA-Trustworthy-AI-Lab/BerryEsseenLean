import BerryEsseen.ManuscriptLatticeGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def manuscriptOutsidePairContribution (s : Set ℝ) (z : ℝ × ℝ) : ℝ :=
  s.indicator abs (-z.1) + s.indicator abs z.2

theorem manuscriptSizeBias_outside_first_integrable (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) :
    Integrable (s.indicator abs) (manuscriptPositiveSizeBias P) :=
  (manuscriptPositiveSizeBias_first_integrable P).abs.indicator hs

theorem manuscriptSizeBias_outside_negative_first_integrable (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) :
    Integrable (fun a => s.indicator abs (-a)) (manuscriptNegativeSizeBias P) := by
  apply (manuscriptNegativeSizeBias_first_integrable P).abs.mono'
    ((measurable_abs.indicator hs).comp measurable_neg).aestronglyMeasurable
  filter_upwards [] with a
  by_cases ha : -a ∈ s
  · simp [Set.indicator_of_mem ha]
  · simp [Set.indicator_of_notMem ha, abs_nonneg]

theorem manuscriptOutsidePairContribution_integrable (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) :
    Integrable (manuscriptOutsidePairContribution s) (manuscriptSizeBiasedProduct P) :=
  ((manuscriptSizeBias_outside_negative_first_integrable P s hs).comp_fst _).add
    ((manuscriptSizeBias_outside_first_integrable P s hs).comp_snd _)

theorem manuscript_weighted_outside_integrable (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) :
    Integrable (fun x => max x 0 * s.indicator abs x) P.measure ∧
      Integrable (fun x => max (-x) 0 * s.indicator abs x) P.measure := by
  constructor
  · convert (manuscriptSizeBias_weighted_first_integrable P).indicator hs using 1
    funext x
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · simp [max_eq_right hx]
    · simp [Set.indicator_of_notMem hxs]
  · convert (manuscriptSizeBias_negative_weighted_first_integrable P).indicator hs using 1
    funext x
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      rcases le_total 0 x with hx | hx
      · simp [max_eq_right (neg_nonpos.mpr hx)]
      · rw [abs_of_nonpos hx]
    · simp [Set.indicator_of_notMem hxs]

theorem manuscriptOutsidePairContribution_identity (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) :
    manuscriptHalfFirstMoment P *
      (∫ z, manuscriptOutsidePairContribution s z ∂manuscriptSizeBiasedProduct P) =
      ∫ x, s.indicator (fun x : ℝ => x ^ 2) x ∂P.measure := by
  unfold manuscriptOutsidePairContribution manuscriptSizeBiasedProduct
  rw [integral_add ((manuscriptSizeBias_outside_negative_first_integrable P s hs).comp_fst _)
    ((manuscriptSizeBias_outside_first_integrable P s hs).comp_snd _),
    integral_fun_fst (fun a => s.indicator abs (-a)),
    integral_fun_snd (s.indicator abs)]
  simp only [probReal_univ, one_smul]
  rw [manuscriptNegativeSizeBias_integral P (fun x => s.indicator abs (-x))
    ((measurable_abs.indicator hs).comp measurable_neg), manuscriptPositiveSizeBias_integral]
  simp only [neg_neg]
  rw [← add_div, mul_div_cancel₀ _ (manuscriptHalfFirstMoment_pos P).ne',
    ← integral_add (manuscript_weighted_outside_integrable P s hs).2
      (manuscript_weighted_outside_integrable P s hs).1]
  congr 1
  funext x
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]; ring
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), abs_of_nonpos hx]; ring
  · simp [Set.indicator_of_notMem hxs]

theorem manuscript_outside_pair_comparison (s : Set ℝ) (h : ℝ) (z : ℝ × ℝ)
    (ha : 0 < z.1) (hb : 0 < z.2)
    (hout : -z.1 ∈ s ∨ z.2 ∈ s → 2 * h ≤ z.1 + z.2) :
    manuscriptOutsidePairContribution s z ≤
      (Ici (2 * h)).indicator (fun x : ℝ => x) (z.1 + z.2) := by
  unfold manuscriptOutsidePairContribution
  by_cases hlarge : 2 * h ≤ z.1 + z.2
  · rw [Set.indicator_of_mem (show z.1 + z.2 ∈ Ici (2 * h) from hlarge)]
    have hleft : s.indicator abs (-z.1) ≤ z.1 := by
      by_cases hs : -z.1 ∈ s
      · simp [Set.indicator_of_mem hs, abs_of_pos ha]
      · simp [Set.indicator_of_notMem hs, ha.le]
    have hright : s.indicator abs z.2 ≤ z.2 := by
      by_cases hs : z.2 ∈ s
      · simp [Set.indicator_of_mem hs, abs_of_pos hb]
      · simp [Set.indicator_of_notMem hs, hb.le]
    exact add_le_add hleft hright
  · have hna : -z.1 ∉ s := fun hs => hlarge (hout (Or.inl hs))
    have hnb : z.2 ∉ s := fun hs => hlarge (hout (Or.inr hs))
    simp [Set.indicator_of_notMem hna, Set.indicator_of_notMem hnb,
      Set.indicator_of_notMem (show z.1 + z.2 ∉ Ici (2 * h) from hlarge)]

theorem manuscript_deficit_controls_outside_pair (s : Set ℝ) (h : ℝ) (z : ℝ × ℝ)
    (hh : 0 < h) (ha : 0 < z.1) (hb : 0 < z.2) (hgap : h ≤ z.1 + z.2)
    (hout : -z.1 ∈ s ∨ z.2 ∈ s → 2 * h ≤ z.1 + z.2) :
    3 * h * manuscriptOutsidePairContribution s z ≤ manuscriptLatticeDeficitKernel h z := by
  have hi := mul_le_mul_of_nonneg_left (manuscript_outside_pair_comparison s h z ha hb hout)
    (show 0 ≤ 3 * h by positivity)
  apply hi.trans
  by_cases hz : 2 * h ≤ z.1 + z.2
  · rw [Set.indicator_of_mem (show z.1 + z.2 ∈ Ici (2 * h) from hz)]
    have hp := mul_nonneg (show 0 ≤ 3 * (z.1 + z.2) by linarith)
      (show 0 ≤ z.1 + z.2 - 2 * h by linarith)
    unfold manuscriptLatticeDeficitKernel
    nlinarith only [hp, sq_nonneg
      (Real.sqrt (cStar - 2) * z.1 - Real.sqrt (cStar - 4) * z.2)]
  · rw [Set.indicator_of_notMem (show z.1 + z.2 ∉ Ici (2 * h) from hz), mul_zero]
    exact manuscriptLatticeDeficitKernel_nonneg h z hh.le hgap

theorem manuscript_bracketing_pair_geometry (a b h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = h) (z : ℝ × ℝ)
    (ha' : 0 < z.1) (hb' : 0 < z.2)
    (hx : -z.1 = -a ∨ -z.1 = b ∨ -z.1 ≤ -a - h ∨ b + h ≤ -z.1)
    (hy : z.2 = -a ∨ z.2 = b ∨ z.2 ≤ -a - h ∨ b + h ≤ z.2) :
    h ≤ z.1 + z.2 ∧
      (-z.1 ∈ ({-a, b}ᶜ : Set ℝ) ∨ z.2 ∈ ({-a, b}ᶜ : Set ℝ) →
        2 * h ≤ z.1 + z.2) := by
  have hx' : z.1 = a ∨ a + h ≤ z.1 := by
    rcases hx with hx | hx | hx | hx
    · left; linarith
    · exfalso; linarith
    · right; linarith
    · exfalso; linarith
  have hy' : z.2 = b ∨ b + h ≤ z.2 := by
    rcases hy with hy | hy | hy | hy
    · exfalso; linarith
    · left; exact hy
    · exfalso; linarith
    · right; exact hy
  constructor
  · rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;> linarith
  · intro hs
    rcases hs with hs | hs
    · have hne : z.1 ≠ a := by intro he; apply hs; simp [he]
      rcases hx' with hx' | hx'
      · exact False.elim (hne hx')
      · rcases hy' with hy' | hy' <;> linarith
    · have hne : z.2 ≠ b := by intro he; apply hs; simp [he]
      rcases hy' with hy' | hy'
      · exact False.elim (hne hy')
      · rcases hx' with hx' | hx' <;> linarith

theorem manuscript_lattice_outside_second_bound (P : StandardizedLaw) (a b h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = h) (hκ : 0 ≤ signedThirdMoment P)
    (hgeom : ∀ x ∈ P.measure.support,
      x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) :
    (∫ x, ({-a, b}ᶜ : Set ℝ).indicator (fun x : ℝ => x ^ 2) x ∂P.measure) ≤
      latticeMomentDeficit P h / (3 * h) := by
  have hh : 0 < h := by linarith
  let s : Set ℝ := {-a, b}ᶜ
  have hs : MeasurableSet s := ((measurableSet_singleton b).insert (-a)).compl
  have hi : Integrable (fun z => 3 * h * manuscriptOutsidePairContribution s z)
      (manuscriptSizeBiasedProduct P) :=
    (manuscriptOutsidePairContribution_integrable P s hs).const_mul _
  have hpoint : ∀ᵐ z ∂manuscriptSizeBiasedProduct P,
      3 * h * manuscriptOutsidePairContribution s z ≤ manuscriptLatticeDeficitKernel h z := by
    filter_upwards [manuscriptSizeBiasedProduct_support P] with z hz
    have hg := manuscript_bracketing_pair_geometry a b h ha hb hab z hz.1 hz.2.1
      (hgeom _ hz.2.2.1) (hgeom _ hz.2.2.2)
    exact manuscript_deficit_controls_outside_pair s h z hh hz.1 hz.2.1 hg.1 hg.2
  have hbnd := integral_mono_ae hi (manuscriptLatticeDeficitKernel_integrable P h) hpoint
  rw [integral_const_mul] at hbnd
  have hm := mul_le_mul_of_nonneg_left hbnd (manuscriptHalfFirstMoment_pos P).le
  have hid := manuscriptOutsidePairContribution_identity P s hs
  apply (le_div_iff₀ (by positivity : 0 < 3 * h)).mpr
  rw [manuscript_lattice_deficit_decomposition P h hκ]
  change (∫ x, s.indicator (fun x : ℝ => x ^ 2) x ∂P.measure) * (3 * h) ≤ _
  linear_combination hm - 3 * h * hid

theorem manuscript_effective_lattice_outside_second (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧
      (∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) ∧
      (∫ x, ({-a, b}ᶜ : Set ℝ).indicator (fun y => y ^ 2) x ∂P.measure) ≤ δ := by
  obtain ⟨hh, a₀, ha₀⟩ := hlat
  have hz := manuscript_effective_lattice_translate_avoids_zero P h δ a₀ hh hβ hκ hD hδ ha₀
  obtain ⟨a, b, ha, hb, hab, hg⟩ := translated_lattice_bracketing a₀ h hh hz
  have hgeom : ∀ x ∈ P.measure.support,
      x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x := fun x hx => hg x (ha₀ x hx)
  refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
  · filter_upwards [P.measure.support_mem_ae] with x hx
    exact hgeom x hx
  have hbnd := manuscript_lattice_outside_second_bound P a b h ha hb hab hκ hgeom
  apply hbnd.trans
  apply (div_le_iff₀ (by positivity : 0 < 3 * h)).mpr
  have hh1 : 1 ≤ 3 * h := by linarith [(effective_lattice_span_bounds P h δ hβ hD hδ).1]
  exact hD.2.trans (by nlinarith [mul_nonneg (hD.1.trans hD.2) (sub_nonneg.mpr hh1)])

end BerryEsseen
