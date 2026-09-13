import BerryEsseen.ManuscriptConfinementMass
import BerryEsseen.EffectiveSupportAnchors

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Apply the transport obstruction at the Bernoulli atom after the manuscript's
map T(x)=pE+sigmaE*x. The radius is measured in these affine coordinates. -/
theorem manuscript_affine_support_near_atom (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (r : ℝ) (hr : 0 < r)
    (hW : wassersteinOne (P.measure.map esseenAffine) (esseenLaw.measure.map esseenAffine) < 0.4 * r)
    (a : ℝ) (ha : a = 0 ∨ a = 1) :
    ∃ x ∈ P.measure.support, |esseenAffine x - a| < r := by
  let μ := P.measure.map esseenAffine
  let ν := esseenLaw.measure.map esseenAffine
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by unfold esseenAffine; fun_prop)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by unfold esseenAffine; fun_prop)
  by_contra h
  push_neg at h
  have hzero : ∫ x, supportTent a r x ∂μ = 0 := by
    rw [integral_map (by unfold esseenAffine; fun_prop) (supportTent_lipschitz a r).continuous.measurable.aestronglyMeasurable]
    apply integral_eq_zero_of_ae
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact max_eq_right (sub_nonpos.mpr (h x hx))
  have ht := lipschitz_integral_abs_le_wassersteinOne K μ ν
    (confinement_affine_first_integrable P pE sigmaE)
    (confinement_affine_first_integrable esseenLaw pE sigmaE)
    (supportTent a r) (supportTent_lipschitz a r)
  rw [hzero, zero_sub, abs_neg] at ht
  have he : (∫ x, supportTent a r x ∂ν) = qE * supportTent a r 0 + pE * supportTent a r 1 := by
    rw [integral_map (by unfold esseenAffine; fun_prop) (supportTent_lipschitz a r).continuous.measurable.aestronglyMeasurable]
    change (∫ x, supportTent a r (esseenAffine x) ∂esseenMeasure) = _
    rw [integral_esseen, esseenAffine_at_atoms.1, esseenAffine_at_atoms.2]
  have hnonneg (x : ℝ) : 0 ≤ supportTent a r x := le_max_right _ _
  have hval : supportTent a r a = r := by simp only [supportTent, sub_self, abs_zero, sub_zero, max_eq_left hr.le]
  have hlower : 0.4 * r ≤ ∫ x, supportTent a r x ∂ν := by
    rw [he]
    rcases ha with ha | ha
    · rw [← ha, hval]
      have hq : (0.4 : ℝ) ≤ qE := by linarith [pE_bounds.2, pE_add_qE]
      have hm := mul_le_mul_of_nonneg_right hq hr.le
      nlinarith only [hm, mul_nonneg pE_pos.le (hnonneg 1)]
    · rw [← ha, hval]
      have hm := mul_le_mul_of_nonneg_right pE_bounds.1.le hr.le
      nlinarith only [hm, mul_nonneg qE_pos.le (hnonneg 0)]
  have hab := le_abs_self (∫ x, supportTent a r x ∂ν)
  linarith only [hlower, hab, ht, hW]

theorem manuscript_effective_support_anchors (K : PublishedWassersteinDuality)
    (P : StandardizedLaw)
    (hW : wassersteinOne P.measure esseenLaw.measure ≤ Real.exp (-7 * appendixA)) :
    ∃ a ∈ P.measure.support, ∃ b ∈ P.measure.support,
      |esseenAffine a| < appendixZeta / 10 ∧ |esseenAffine b - 1| < appendixZeta / 10 := by
  have hz : 0 < appendixZeta / 10 := by have h := appendixZeta_bounds.1; positivity
  have hcost := (manuscript_esseen_affine_wasserstein_bound K P hW).trans_lt appendix_support_anchor_budget
  obtain ⟨a, ha, har⟩ := manuscript_affine_support_near_atom K P _ hz hcost 0 (Or.inl rfl)
  obtain ⟨b, hb, hbr⟩ := manuscript_affine_support_near_atom K P _ hz hcost 1 (Or.inr rfl)
  exact ⟨a, ha, b, hb, by simpa only [sub_zero] using har, hbr⟩

end BerryEsseen
