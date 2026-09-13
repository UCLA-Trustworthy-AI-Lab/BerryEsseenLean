import BerryEsseen.EffectiveContactIncrement
import BerryEsseen.EffectiveIntervals

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def supportTent (a r x : ℝ) : ℝ := max (r - |x - a|) 0

theorem supportTent_lipschitz (a r : ℝ) : LipschitzWith 1 (supportTent a r) := by
  have hf : LipschitzWith 1 (fun x : ℝ => r - |x - a|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show (r - |x - a|) - (r - |y - a|) = |y - a| - |x - a| by ring]
    have h := abs_abs_sub_abs_le_abs_sub (y - a) (x - a)
    simpa only [sub_sub_sub_cancel_right, abs_sub_comm y x] using h
  exact hf.max_const 0

theorem wasserstein_esseen_support_near_atom (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (r : ℝ) (hr : 0 < r)
    (hW : wassersteinOne P.measure esseenLaw.measure < 0.4 * r)
    (a : ℝ) (ha : a = -aE ∨ a = bE) :
    ∃ x ∈ P.measure.support, |x - a| < r := by
  by_contra h
  push_neg at h
  have hzero : ∫ x, supportTent a r x ∂P.measure = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact max_eq_right (sub_nonpos.mpr (h x hx))
  have ht := lipschitz_integral_abs_le_wassersteinOne K P.measure esseenLaw.measure
    P.first_integrable esseenLaw.first_integrable (supportTent a r) (supportTent_lipschitz a r)
  rw [hzero, zero_sub, abs_neg] at ht
  have he : (∫ x, supportTent a r x ∂esseenLaw.measure) =
      qE * supportTent a r (-aE) + pE * supportTent a r bE := integral_esseen _
  have hnonneg (x : ℝ) : 0 ≤ supportTent a r x := le_max_right _ _
  have hval : supportTent a r a = r := by simp only [supportTent, sub_self, abs_zero, sub_zero, max_eq_left hr.le]
  have hlower : 0.4 * r ≤ ∫ x, supportTent a r x ∂esseenLaw.measure := by
    rw [he]
    rcases ha with ha | ha
    · rw [← ha, hval]
      have hq : (0.4 : ℝ) ≤ qE := by linarith [pE_bounds.2, pE_add_qE]
      have hm := mul_le_mul_of_nonneg_right hq hr.le
      nlinarith only [hm, mul_nonneg pE_pos.le (hnonneg bE)]
    · rw [← ha, hval]
      have hm := mul_le_mul_of_nonneg_right pE_bounds.1.le hr.le
      nlinarith only [hm, mul_nonneg qE_pos.le (hnonneg (-aE))]
  have hab := le_abs_self (∫ x, supportTent a r x ∂esseenLaw.measure)
  linarith only [hlower, hab, ht, hW]

def appendixZeta : ℝ := appendixEtaStar / 2
def esseenAffine (x : ℝ) : ℝ := pE + sigmaE * x

theorem appendixZeta_bounds : appendixZeta ∈ Ioo 0 0.001 := by
  unfold appendixZeta
  have h := appendixEtaStar_bounds
  constructor <;> linarith [h.1.1, h.2.1]

theorem appendix_support_anchor_budget :
    Real.exp (-7 * appendixA) < 0.4 * (appendixZeta / 10) := by
  have h := exponential_relative_sixteenth 50 (7 * appendixA) (2 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  simp only [← neg_mul] at h
  unfold appendixZeta appendixEtaStar
  nlinarith only [h, Real.exp_pos (-2 * appendixA)]

theorem esseenAffine_at_atoms : esseenAffine (-aE) = 0 ∧ esseenAffine bE = 1 := by
  unfold esseenAffine aE bE
  constructor
  · field_simp [sigmaE_pos.ne'] <;> ring
  · rw [mul_div_cancel₀ _ sigmaE_pos.ne', pE_add_qE]

theorem effective_support_anchors (K : PublishedWassersteinDuality) (P : StandardizedLaw)
    (hW : wassersteinOne P.measure esseenLaw.measure ≤ Real.exp (-7 * appendixA)) :
    ∃ a ∈ P.measure.support, ∃ b ∈ P.measure.support,
      |esseenAffine a| < appendixZeta / 10 ∧ |esseenAffine b - 1| < appendixZeta / 10 := by
  have hz : 0 < appendixZeta / 10 := by have h := appendixZeta_bounds.1; positivity
  have hcost := hW.trans_lt appendix_support_anchor_budget
  obtain ⟨a, ha, har⟩ := wasserstein_esseen_support_near_atom K P _ hz hcost (-aE) (Or.inl rfl)
  obtain ⟨b, hb, hbr⟩ := wasserstein_esseen_support_near_atom K P _ hz hcost bE (Or.inr rfl)
  have hσ : sigmaE ≤ 1 / 2 := by nlinarith [sigmaE_sq, sigmaE_pos, pE_add_qE, sq_nonneg (pE - qE)]
  have he (x y : ℝ) : |esseenAffine x - esseenAffine y| = sigmaE * |x - y| := by
    rw [show esseenAffine x - esseenAffine y = sigmaE * (x - y) by unfold esseenAffine; ring, abs_mul, abs_of_pos sigmaE_pos]
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · have hm := mul_lt_mul_of_pos_left har sigmaE_pos
    have hb := mul_le_mul_of_nonneg_right hσ hz.le
    have he' := he a (-aE)
    rw [esseenAffine_at_atoms.1, sub_zero] at he'
    rw [he']
    nlinarith only [hm, hb, hz]
  · have hm := mul_lt_mul_of_pos_left hbr sigmaE_pos
    have hb := mul_le_mul_of_nonneg_right hσ hz.le
    have he' := he b bE
    rw [esseenAffine_at_atoms.2] at he'
    rw [he']
    nlinarith only [hm, hb, hz]

end BerryEsseen
