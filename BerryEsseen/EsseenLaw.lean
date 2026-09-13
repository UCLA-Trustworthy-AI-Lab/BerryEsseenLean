import BerryEsseen.CharacteristicTaylor
import BerryEsseen.PositiveBranch
import BerryEsseen.Resonances

/-! Actual measure, envelope and limit arguments for Esseen extremizers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

def esseenMeasure : Measure ℝ :=
  ENNReal.ofReal qE • Measure.dirac (-aE) + ENNReal.ofReal pE • Measure.dirac bE

theorem esseen_integrable (f : ℝ → ℝ) : Integrable f esseenMeasure := by
  simp only [esseenMeasure, integrable_add_measure]
  constructor <;> exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem integral_esseen (f : ℝ → ℝ) :
    (∫ x, f x ∂esseenMeasure) = qE * f (-aE) + pE * f bE := by
  have hi := esseen_integrable f
  rw [esseenMeasure, integrable_add_measure] at hi
  rw [esseenMeasure, integral_add_measure hi.1 hi.2]
  simp [integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal pE_pos.le,
    ENNReal.toReal_ofReal qE_pos.le]

theorem esseen_mean : (∫ x, x ∂esseenMeasure) = 0 := by
  rw [integral_esseen]
  unfold aE bE
  ring

theorem esseen_second : (∫ x, x ^ 2 ∂esseenMeasure) = 1 := by
  rw [integral_esseen]
  unfold aE bE
  field_simp [sigmaE_pos.ne']
  rw [sigmaE_sq]
  rw [pE_add_qE]
  ring

def esseenLaw : StandardizedLaw where
  measure := esseenMeasure
  probability := ⟨by
    simp only [esseenMeasure, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add qE_pos.le pE_pos.le]
    norm_num [add_comm qE pE, pE_add_qE]⟩
  first_integrable := esseen_integrable _
  second_integrable := esseen_integrable _
  third_integrable := esseen_integrable _
  mean_zero := esseen_mean
  second_one := esseen_second

theorem aE_pos : 0 < aE := div_pos pE_pos sigmaE_pos

theorem bE_pos : 0 < bE := div_pos qE_pos sigmaE_pos

theorem hE_pos : 0 < hE := one_div_pos.2 sigmaE_pos

theorem kappaE_pos : 0 < kappaE := by
  unfold kappaE
  apply div_pos _ sigmaE_pos
  linarith [pE_lt_half, pE_add_qE]

theorem thirdMoment_esseen : thirdMoment esseenLaw = betaE := by
  change (∫ x, |x| ^ 3 ∂esseenMeasure) = betaE
  rw [integral_esseen, abs_neg, abs_of_pos aE_pos, abs_of_pos bE_pos]
  unfold aE bE betaE
  field_simp [sigmaE_pos.ne']
  nlinarith [sigmaE_sq, pE_add_qE]

theorem signedThirdMoment_esseen : signedThirdMoment esseenLaw = kappaE := by
  change (∫ x, x ^ 3 ∂esseenMeasure) = kappaE
  rw [integral_esseen]
  unfold aE bE kappaE
  field_simp [sigmaE_pos.ne']
  rw [sigmaE_sq]
  have hf : -pE ^ 2 + qE ^ 2 = (qE - pE) * (pE + qE) := by ring
  rw [hf, pE_add_qE]
  ring

theorem reflectedLaw_signedThirdMoment (P : StandardizedLaw) :
    signedThirdMoment (reflectedLaw P) = -signedThirdMoment P := by
  unfold signedThirdMoment reflectedLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  have he (x : ℝ) : (-x) ^ 3 = -(x ^ 3) := by ring
  simp only [he, integral_neg]

theorem esseen_moment_span_identity : kappaE + 3 * hE = cStar * betaE := by
  rw [beta_identity]
  unfold kappaE hE qE pE
  ring

theorem esseen_peak_identity : (hE / 2 + kappaE / 6) * phi0 = cE * betaE := by
  rw [cE_eq]
  calc
    _ = phi0 / 6 * (kappaE + 3 * hE) := by ring
    _ = _ := by rw [esseen_moment_span_identity]; ring

theorem esseen_support : esseenMeasure.support = {-aE, bE} := by
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed (by
      convert (show IsClosed ({-aE} : Set ℝ) from isClosed_singleton).union
        (show IsClosed ({bE} : Set ℝ) from isClosed_singleton) using 1)
    rw [mem_ae_iff]
    simp [esseenMeasure]
  · intro x hx
    rcases mem_insert_iff.1 hx with rfl | hx
    · rw [Measure.mem_support_iff_forall]
      intro U hU
      have hxU := mem_of_mem_nhds hU
      simp only [esseenMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      have hl : 0 < ENNReal.ofReal qE * Measure.dirac (-aE) U := by
        rw [Measure.dirac_apply_of_mem hxU, mul_one]
        exact ENNReal.ofReal_pos.2 qE_pos
      exact hl.trans_le (le_add_right le_rfl)
    · have he : x = bE := mem_singleton_iff.1 hx
      subst x
      rw [Measure.mem_support_iff_forall]
      intro U hU
      have hxU := mem_of_mem_nhds hU
      simp only [esseenMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      have hr : 0 < ENNReal.ofReal pE * Measure.dirac bE U := by
        rw [Measure.dirac_apply_of_mem hxU, mul_one]
        exact ENNReal.ofReal_pos.2 pE_pos
      exact hr.trans_le (le_add_left le_rfl)

theorem esseen_lattice_span : IsLatticeSpan esseenLaw.measure hE := by
  refine ⟨hE_pos, -aE, ?_⟩
  intro x hx
  change x ∈ esseenMeasure.support at hx
  rw [esseen_support] at hx
  rcases mem_insert_iff.1 hx with rfl | hx
  · exact ⟨0, by simp⟩
  · refine ⟨1, ?_⟩
    rw [mem_singleton_iff.1 hx]
    simp only [Int.cast_one, one_mul]
    linarith [span_identity]

theorem reflected_measure_twice (μ : Measure ℝ) :
    (μ.map (fun x => -x)).map (fun x => -x) = μ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, neg_neg, Measure.map_id']

theorem reflected_support_subset (P : StandardizedLaw) :
    (reflectedLaw P).measure.support ⊆ {x : ℝ | -x ∈ P.measure.support} := by
  apply Measure.support_subset_of_isClosed
    (P.measure.isClosed_support.preimage (by fun_prop))
  change ∀ᵐ x ∂P.measure.map (fun x => -x), -x ∈ P.measure.support
  rw [ae_map_iff (by fun_prop) (P.measure.isClosed_support.preimage continuous_neg).measurableSet]
  simpa only [neg_neg] using P.measure.support_mem_ae

theorem reflected_lattice_span (P : StandardizedLaw) (h : ℝ)
    (hh : IsLatticeSpan P.measure h) : IsLatticeSpan (reflectedLaw P).measure h := by
  obtain ⟨hh, a, ha⟩ := hh
  refine ⟨hh, -a, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := ha (-x) (reflected_support_subset P hx)
  refine ⟨-k, ?_⟩
  push_cast
  linarith

theorem standardizedLaw_eq_of_measure_eq (P Q : StandardizedLaw)
    (h : P.measure = Q.measure) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

end BerryEsseen
