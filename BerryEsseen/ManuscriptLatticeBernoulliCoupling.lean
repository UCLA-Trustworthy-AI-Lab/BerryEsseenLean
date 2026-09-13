import BerryEsseen.ManuscriptLatticeCouplings
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The one shared uniform random variable in the printed Bernoulli coupling. -/
def manuscriptUnitUniform : Measure ℝ := volume.restrict (Ioc 0 1)

instance manuscriptUnitUniform_probability : IsProbabilityMeasure manuscriptUnitUniform := by
  constructor
  simp [manuscriptUnitUniform]

theorem manuscriptUnitUniform_threshold (p : ℝ) (hp : p ∈ Icc 0 1) :
    manuscriptUnitUniform (Iic p) = ENNReal.ofReal p ∧
    manuscriptUnitUniform (Iic p)ᶜ = ENNReal.ofReal (1 - p) := by
  constructor
  · rw [manuscriptUnitUniform, Measure.restrict_apply measurableSet_Iic]
    have he : Iic p ∩ Ioc (0 : ℝ) 1 = Ioc 0 p := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨hxp, h0, h1⟩; exact ⟨h0, hxp⟩
      · rintro ⟨h0, hxp⟩; exact ⟨hxp, h0, hxp.trans hp.2⟩
    rw [he, Real.volume_Ioc, sub_zero]
  · rw [manuscriptUnitUniform, Measure.restrict_apply measurableSet_Iic.compl]
    have he : (Iic p)ᶜ ∩ Ioc (0 : ℝ) 1 = Ioc p 1 := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_Iic, mem_Ioc, not_le]
      constructor
      · rintro ⟨hxp, h0, h1⟩; exact ⟨hxp, h1⟩
      · rintro ⟨hxp, h1⟩; exact ⟨hxp, hp.1.trans_lt hxp, h1⟩
    rw [he, Real.volume_Ioc]

/-- The threshold map, with the upper atom occurring with probability p. -/
def manuscriptBernoulliUniformMap (p t : ℝ) : ℝ :=
  if t ≤ p then (1 - p) / Real.sqrt (p * (1 - p)) else -p / Real.sqrt (p * (1 - p))

theorem manuscriptBernoulliUniformMap_measurable (p : ℝ) :
    Measurable (manuscriptBernoulliUniformMap p) := by
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem manuscript_map_two_values (μ : Measure ℝ) (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (a b : ℝ) : μ.map (s.piecewise (fun _ => a) (fun _ => b)) =
      μ s • Measure.dirac a + μ sᶜ • Measure.dirac b := by
  classical
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply (Measurable.piecewise hs measurable_const measurable_const) ht]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases ha : a ∈ t <;> by_cases hb : b ∈ t
  · have he : s.piecewise (fun _ => a) (fun _ => b) ⁻¹' t = univ := by
      ext x; by_cases hx : x ∈ s <;> simp [hx, ha, hb]
    rw [he]
    simp only [Measure.dirac_apply' _ ht, indicator_of_mem ha, indicator_of_mem hb,
      Pi.one_apply, mul_one]
    exact (measure_add_measure_compl hs).symm
  · have he : s.piecewise (fun _ => a) (fun _ => b) ⁻¹' t = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx, ha, hb]
    rw [he]
    simp [Measure.dirac_apply' _ ht, ha, hb]
  · have he : s.piecewise (fun _ => a) (fun _ => b) ⁻¹' t = sᶜ := by
      ext x; by_cases hx : x ∈ s <;> simp [hx, ha, hb]
    rw [he]
    simp [Measure.dirac_apply' _ ht, ha, hb]
  · have he : s.piecewise (fun _ => a) (fun _ => b) ⁻¹' t = ∅ := by
      ext x; by_cases hx : x ∈ s <;> simp [hx, ha, hb]
    rw [he]
    simp [Measure.dirac_apply' _ ht, ha, hb]

theorem manuscriptBernoulliUniformMap_law (p : ℝ) (hp : p ∈ Ioo 0 1) :
    manuscriptUnitUniform.map (manuscriptBernoulliUniformMap p) =
      (standardizedBernoulliLaw p hp).measure := by
  classical
  have he : manuscriptBernoulliUniformMap p =
      (Iic p).piecewise (fun _ => (1 - p) / Real.sqrt (p * (1 - p)))
        (fun _ => -p / Real.sqrt (p * (1 - p))) := rfl
  rw [he, manuscript_map_two_values _ _ measurableSet_Iic,
    (manuscriptUnitUniform_threshold p ⟨hp.1.le, hp.2.le⟩).1,
    (manuscriptUnitUniform_threshold p ⟨hp.1.le, hp.2.le⟩).2,
    standardizedBernoulliLaw_measure, add_comm]

/-- The disagreement event of the shared indicators has exactly length |p-q|. -/
theorem manuscriptUnitUniform_disagreement (p q : ℝ) (hp : p ∈ Icc 0 1)
    (hq : q ∈ Icc 0 1) :
    manuscriptUnitUniform.real (Ioc (min p q) (max p q)) = |p - q| := by
  rw [Measure.real, manuscriptUnitUniform, Measure.restrict_apply measurableSet_Ioc]
  have hsub : Ioc (min p q) (max p q) ⊆ Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_le_of_lt (le_min hp.1 hq.1) hx.1,
      hx.2.trans (max_le hp.2 hq.2)⟩
  rw [inter_eq_left.mpr hsub, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max))]
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]

/-- The printed derivative bounds for the two atom locations. -/
theorem manuscript_bernoulli_atoms_derivative (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    (∃ d, HasDerivAt (fun t => -t / Real.sqrt (t * (1 - t))) d p ∧ |d| < 5) ∧
    (∃ d, HasDerivAt (fun t => (1 - t) / Real.sqrt (t * (1 - t))) d p ∧ |d| < 5) := by
  let d := -(1 - 2 * p) / (2 * (Real.sqrt (p * (1 - p))) ^ 3)
  let A := (Real.sqrt (p * (1 - p)))⁻¹
  have hd := manuscript_bernoulli_span_hasDerivAt p hp
  have hdlt : |d| < 1 := manuscript_bernoulli_span_derivative_bound p hp
  have hA : |A| < 3 := by
    rw [abs_of_nonneg (by dsimp [A]; positivity)]
    exact manuscript_bernoulli_span_lt_three p hp
  have hpabs : |p| ≤ 1 := by rw [abs_of_nonneg (by linarith [hp.1])]; linarith [hp.2]
  have hqabs : |1 - p| ≤ 1 := by rw [abs_of_nonneg (by linarith [hp.2])]; linarith [hp.1]
  constructor
  · refine ⟨-(A + p * d), ?_, ?_⟩
    · convert ((hasDerivAt_id p).mul hd).neg using 1
      · funext t; simp [div_eq_mul_inv]
      · dsimp [A, d]; ring
    · rw [abs_neg]
      have hmul := mul_le_mul hpabs hdlt.le (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hb := abs_add_le A (p * d)
      rw [abs_mul] at hb
      linarith
  · refine ⟨-A + (1 - p) * d, ?_, ?_⟩
    · convert (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul hd) using 1
      dsimp [A, d]; ring
    · have hmul := mul_le_mul hqabs hdlt.le (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      have hb := abs_add_le (-A) ((1 - p) * d)
      rw [abs_neg, abs_mul] at hb
      linarith

theorem manuscript_bernoulli_atoms_MVT (p q : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hq : q ∈ Icc (2 / 5) (9 / 20)) :
    |(-p / Real.sqrt (p * (1 - p))) - (-q / Real.sqrt (q * (1 - q)))| ≤ 5 * |p - q| ∧
    |((1-p) / Real.sqrt (p * (1 - p))) - ((1-q) / Real.sqrt (q * (1 - q)))| ≤ 5 * |p - q| := by
  have hleft : ∀ t ∈ Icc (2 / 5 : ℝ) (9 / 20),
      HasDerivWithinAt (fun t => -t / Real.sqrt (t * (1 - t)))
        (deriv (fun t => -t / Real.sqrt (t * (1 - t))) t) (Icc (2 / 5 : ℝ) (9 / 20)) t ∧
      ‖deriv (fun t => -t / Real.sqrt (t * (1 - t))) t‖ ≤ 5 := by
    intro t ht
    obtain ⟨d, hd, hb⟩ := (manuscript_bernoulli_atoms_derivative t ht).1
    rw [hd.deriv]
    exact ⟨hd.hasDerivWithinAt, hb.le⟩
  have hright : ∀ t ∈ Icc (2 / 5 : ℝ) (9 / 20),
      HasDerivWithinAt (fun t => (1-t) / Real.sqrt (t * (1 - t)))
        (deriv (fun t => (1-t) / Real.sqrt (t * (1 - t))) t) (Icc (2 / 5 : ℝ) (9 / 20)) t ∧
      ‖deriv (fun t => (1-t) / Real.sqrt (t * (1 - t))) t‖ ≤ 5 := by
    intro t ht
    obtain ⟨d, hd, hb⟩ := (manuscript_bernoulli_atoms_derivative t ht).2
    rw [hd.deriv]
    exact ⟨hd.hasDerivWithinAt, hb.le⟩
  exact ⟨Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t ht => (hleft t ht).1)
      (fun t ht => (hleft t ht).2) (convex_Icc _ _) hq hp,
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t ht => (hright t ht).1)
      (fun t ht => (hright t ht).2) (convex_Icc _ _) hq hp⟩

/-- Cross-atom distances have the printed strict bound 5/2. -/
theorem manuscript_bernoulli_cross_atom_bound (p q : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hq : q ∈ Icc (2 / 5) (9 / 20)) :
    |(1-p) / Real.sqrt (p * (1-p)) - (-q / Real.sqrt (q * (1-q)))| < 5 / 2 := by
  have hsp := (effective_binomial_parameters p hp).2.1
  have hsq := (effective_binomial_parameters q hq).2.1
  have hsp0 : 0 < Real.sqrt (p * (1-p)) := by linarith
  have hsq0 : 0 < Real.sqrt (q * (1-q)) := by linarith
  have hu : (1-p) / Real.sqrt (p * (1-p)) ≤ 5 / 4 := by
    apply (div_le_iff₀ hsp0).mpr
    linarith [hp.1]
  have hl : q / Real.sqrt (q * (1-q)) ≤ 1 := by
    apply (div_le_one hsq0).mpr
    linarith [hq.2]
  have hp1 : 0 ≤ 1 - p := by linarith [hp.2]
  have hq0 : 0 ≤ q := by linarith [hq.1]
  rw [neg_div, sub_neg_eq_add, abs_of_nonneg (by positivity)]
  linarith

/-- Cost of the actual shared-uniform Bernoulli coupling. -/
theorem manuscript_standardizedBernoulli_wasserstein_actual (p q : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hq : q ∈ Icc (2 / 5) (9 / 20)) :
    wassersteinOne (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1).measure
      (standardizedBernoulliLaw q (effective_binomial_parameters q hq).1).measure ≤ 8 * |p-q| := by
  classical
  let D := Ioc (min p q) (max p q)
  let d := |p-q|
  have hd : 0 ≤ d := abs_nonneg _
  have hi (r : ℝ) : Integrable (manuscriptBernoulliUniformMap r) manuscriptUnitUniform := by
    exact Integrable.piecewise measurableSet_Iic (integrable_const _).integrableOn
      (integrable_const _).integrableOn
  have hcostI := ((hi p).sub (hi q)).abs
  have hw := manuscript_wasserstein_common_source manuscriptUnitUniform
    (manuscriptBernoulliUniformMap p) (manuscriptBernoulliUniformMap q)
    (manuscriptBernoulliUniformMap_measurable p) (manuscriptBernoulliUniformMap_measurable q) hcostI
  rw [manuscriptBernoulliUniformMap_law p (effective_binomial_parameters p hp).1,
    manuscriptBernoulliUniformMap_law q (effective_binomial_parameters q hq).1] at hw
  have hpq := manuscript_bernoulli_atoms_MVT p q hp hq
  have hcross := manuscript_bernoulli_cross_atom_bound p q hp hq
  have hcross' := manuscript_bernoulli_cross_atom_bound q p hq hp
  have hpoint (t : ℝ) :
      |manuscriptBernoulliUniformMap p t - manuscriptBernoulliUniformMap q t| ≤
        5 * d + (5/2) * D.indicator (fun _ => (1 : ℝ)) t := by
    have hi0 : 0 ≤ D.indicator (fun _ => (1 : ℝ)) t := by
      by_cases ht : t ∈ D <;> simp [ht]
    by_cases htp : t ≤ p <;> by_cases htq : t ≤ q
    · simp only [manuscriptBernoulliUniformMap, if_pos htp, if_pos htq]
      exact hpq.2.trans (by nlinarith)
    · have htD : t ∈ D := ⟨lt_of_le_of_lt (min_le_right p q) (lt_of_not_ge htq),
        htp.trans (le_max_left p q)⟩
      simp only [manuscriptBernoulliUniformMap, if_pos htp, if_neg htq, indicator_of_mem htD, mul_one]
      exact hcross.le.trans (by linarith)
    · have htD : t ∈ D := ⟨lt_of_le_of_lt (min_le_left p q) (lt_of_not_ge htp),
        htq.trans (le_max_right p q)⟩
      simp only [manuscriptBernoulliUniformMap, if_neg htp, if_pos htq, indicator_of_mem htD, mul_one]
      rw [abs_sub_comm]
      exact hcross'.le.trans (by linarith)
    · simp only [manuscriptBernoulliUniformMap, if_neg htp, if_neg htq]
      exact hpq.1.trans (by nlinarith)
  have hIntegral := integral_mono_ae hcostI
    ((integrable_const (5*d)).add (((integrable_const (1 : ℝ)).indicator measurableSet_Ioc).const_mul (5/2)))
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.add_apply, Pi.sub_apply] at hIntegral
  rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator measurableSet_Ioc).const_mul _),
    integral_const_mul (5/2), integral_indicator_const (1 : ℝ) measurableSet_Ioc] at hIntegral
  have hdis := manuscriptUnitUniform_disagreement p q
    ⟨(effective_binomial_parameters p hp).1.1.le, (effective_binomial_parameters p hp).1.2.le⟩
    ⟨(effective_binomial_parameters q hq).1.1.le, (effective_binomial_parameters q hq).1.2.le⟩
  change manuscriptUnitUniform.real D = d at hdis
  change _ ≤ (∫ _ : ℝ, 5 * d ∂manuscriptUnitUniform) + (5/2) * (manuscriptUnitUniform.real D * 1) at hIntegral
  rw [hdis] at hIntegral
  simp only [integral_const, probReal_univ, one_smul, mul_one] at hIntegral
  change wassersteinOne _ _ ≤ 8 * d
  exact hw.trans (by linarith)

end BerryEsseen
