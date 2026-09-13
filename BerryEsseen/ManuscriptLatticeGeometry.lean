import BerryEsseen.ManuscriptLatticeSizeBias

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscriptNegativeSizeBias_source (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) (h : ∀ᵐ x ∂P.measure, x ∈ s) :
    ∀ᵐ a ∂manuscriptNegativeSizeBias P, -a ∈ s := by
  apply manuscriptPositiveSizeBias_ae (reflectedLaw P)
  change ∀ᵐ a ∂P.measure.map (fun x => -x), -a ∈ s
  apply (ae_map_iff (by fun_prop) (hs.preimage (by fun_prop))).mpr
  simpa only [neg_neg] using h

theorem manuscriptSizeBiasedProduct_support (P : StandardizedLaw) :
    ∀ᵐ z ∂manuscriptSizeBiasedProduct P,
      0 < z.1 ∧ 0 < z.2 ∧ -z.1 ∈ P.measure.support ∧ z.2 ∈ P.measure.support := by
  have ha : ∀ᵐ a ∂manuscriptNegativeSizeBias P, 0 < a :=
    manuscriptPositiveSizeBias_positive (reflectedLaw P)
  have hb := manuscriptPositiveSizeBias_positive P
  have has := manuscriptNegativeSizeBias_source P _ P.measure.isClosed_support.measurableSet
    P.measure.support_mem_ae
  have hbs := manuscriptPositiveSizeBias_ae P _ P.measure.support_mem_ae
  change ∀ᵐ z ∂(manuscriptNegativeSizeBias P).prod (manuscriptPositiveSizeBias P), _
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae ha,
    measurePreserving_snd.quasiMeasurePreserving.ae hb,
    measurePreserving_fst.quasiMeasurePreserving.ae has,
    measurePreserving_snd.quasiMeasurePreserving.ae hbs] with z ha hb has hbs
  exact ⟨ha, hb, has, hbs⟩

theorem manuscript_positive_lattice_pair_gap (a b a₀ h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (has : ∃ i : ℤ, -a = a₀ + (i : ℝ) * h)
    (hbs : ∃ j : ℤ, b = a₀ + (j : ℝ) * h) : h ≤ a + b := by
  obtain ⟨i, hi⟩ := has
  obtain ⟨j, hj⟩ := hbs
  have hij : (i : ℝ) < j := by nlinarith
  have hij' : i < j := by exact_mod_cast hij
  have hn : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
  nlinarith

theorem manuscriptSizeBiasedProduct_gap (P : StandardizedLaw) (h : ℝ)
    (hlat : IsLatticeSpan P.measure h) :
    ∀ᵐ z ∂manuscriptSizeBiasedProduct P, h ≤ z.1 + z.2 := by
  obtain ⟨hh, a₀, hlat⟩ := hlat
  filter_upwards [manuscriptSizeBiasedProduct_support P] with z hz
  exact manuscript_positive_lattice_pair_gap z.1 z.2 a₀ h hz.1 hz.2.1 hh
    (hlat _ hz.2.2.1) (hlat _ hz.2.2.2)

theorem manuscriptLatticeDeficitKernel_nonneg (h : ℝ) (z : ℝ × ℝ)
    (hh : 0 ≤ h) (hz : h ≤ z.1 + z.2) : 0 ≤ manuscriptLatticeDeficitKernel h z := by
  unfold manuscriptLatticeDeficitKernel
  exact add_nonneg (sq_nonneg _) (mul_nonneg
    (mul_nonneg (by norm_num) (hh.trans hz)) (sub_nonneg.mpr hz))

theorem manuscript_lattice_large_pairs_deficit (P : StandardizedLaw) (h : ℝ)
    (hh : 0 < h) (hκ : 0 ≤ signedThirdMoment P)
    (hpair : ∀ᵐ z ∂manuscriptSizeBiasedProduct P, 2 * h ≤ z.1 + z.2) :
    3 * h ≤ latticeMomentDeficit P h := by
  have hi : Integrable (fun z : ℝ × ℝ => 3 * h * (z.1 + z.2))
      (manuscriptSizeBiasedProduct P) :=
    (((manuscriptNegativeSizeBias_first_integrable P).comp_fst _).add
      ((manuscriptPositiveSizeBias_first_integrable P).comp_snd _)).const_mul _
  have hb := integral_mono_ae hi (manuscriptLatticeDeficitKernel_integrable P h) (by
    filter_upwards [hpair] with z hz
    have hp := mul_nonneg (show 0 ≤ 3 * (z.1 + z.2) by linarith)
      (show 0 ≤ z.1 + z.2 - 2 * h by linarith)
    unfold manuscriptLatticeDeficitKernel
    nlinarith only [hp, sq_nonneg
      (Real.sqrt (cStar - 2) * z.1 - Real.sqrt (cStar - 4) * z.2)])
  rw [integral_const_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb (manuscriptHalfFirstMoment_pos P).le
  rw [manuscript_lattice_deficit_decomposition P h hκ]
  have h1 := manuscriptSizeBiasedProduct_first_identity P
  linear_combination hm - 3 * h * h1

theorem manuscript_effective_lattice_translate_avoids_zero (P : StandardizedLaw) (h δ a₀ : ℝ)
    (hh : 0 < h) (hβ : thirdMoment P ≤ 2) (hκ : 0 ≤ signedThirdMoment P)
    (hD : latticeMomentDeficit P h ∈ Icc 0 δ) (hδ : δ ≤ 1 / (10 : ℝ) ^ 6)
    (hlat : ∀ x ∈ P.measure.support, ∃ k : ℤ, x = a₀ + (k : ℝ) * h) :
    ¬ ∃ j : ℤ, a₀ + (j : ℝ) * h = 0 := by
  intro hz
  have hpair : ∀ᵐ z ∂manuscriptSizeBiasedProduct P, 2 * h ≤ z.1 + z.2 := by
    filter_upwards [manuscriptSizeBiasedProduct_support P] with z hz'
    have ha := translated_lattice_nonzero_gap a₀ h hh hz (-z.1)
      (hlat _ hz'.2.2.1) (neg_ne_zero.mpr hz'.1.ne')
    have hb := translated_lattice_nonzero_gap a₀ h hh hz z.2
      (hlat _ hz'.2.2.2) hz'.2.1.ne'
    rw [abs_neg, abs_of_pos hz'.1] at ha
    rw [abs_of_pos hz'.2.1] at hb
    linarith
  have hd := manuscript_lattice_large_pairs_deficit P h hh hκ hpair
  have hs := effective_lattice_span_bounds P h δ hβ hD hδ
  linarith [hD.2]

end BerryEsseen
