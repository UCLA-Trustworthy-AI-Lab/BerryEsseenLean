import BerryEsseen.EsseenLaw
import BerryEsseen.EdgeworthEnvelopes

/-! Actual measure, envelope and limit arguments for Esseen extremizers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

/-- The derivative of the negative branch in Lemma 5.1, with
`A = h / 2` and `B = κ / 6`. -/
theorem negative_edgeworth_envelope_hasDerivAt (h κ x : ℝ) :
    HasDerivAt (edgeworthEnvelope h (-κ))
      (x * standardNormalDensity x * ((κ - h) / 2 - κ / 6 * x ^ 2)) x := by
  have hd := (((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)).const_mul
    ((-κ) / 6)).const_add (h / 2)
  convert hd.mul (standardNormalDensity_hasDerivAt x) using 1 <;>
    (dsimp [edgeworthEnvelope]; ring)

theorem negative_edgeworth_envelope_even (h κ : ℝ) :
    Function.Even (edgeworthEnvelope h (-κ)) := by
  intro x
  simp only [edgeworthEnvelope, standardNormalDensity_formula, neg_sq]

/-- The manuscript's derivative sign gives monotonicity on the positive
half-line, including its endpoint by continuity. -/
theorem negative_edgeworth_envelope_antitoneOn (h κ : ℝ)
    (hk : 0 ≤ κ) (hh : κ ≤ h) :
    AntitoneOn (edgeworthEnvelope h (-κ)) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ => (negative_edgeworth_envelope_hasDerivAt h κ x).continuousAt.continuousWithinAt)
    (fun x _ => (negative_edgeworth_envelope_hasDerivAt h κ x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(negative_edgeworth_envelope_hasDerivAt h κ x).deriv]
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hx0.le (standardNormalDensity_pos x).le)
  have hb := mul_nonneg (div_nonneg hk (by norm_num : (0 : ℝ) ≤ 6)) (sq_nonneg x)
  linarith

theorem negative_edgeworth_envelope_strictAntiOn (h κ : ℝ)
    (hk : 0 ≤ κ) (hh : κ < h) :
    StrictAntiOn (edgeworthEnvelope h (-κ)) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (fun x _ => (negative_edgeworth_envelope_hasDerivAt h κ x).continuousAt.continuousWithinAt)
  intro x hx
  rw [(negative_edgeworth_envelope_hasDerivAt h κ x).deriv]
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  apply mul_neg_of_pos_of_neg (mul_pos hx0 (standardNormalDensity_pos x))
  have hb := mul_nonneg (div_nonneg hk (by norm_num : (0 : ℝ) ≤ 6)) (sq_nonneg x)
  linarith

theorem negative_edgeworth_envelope_bound (h κ x : ℝ) (hk : 0 ≤ κ) (hh : κ ≤ h) :
    edgeworthEnvelope h (-κ) x ≤ (h / 2 - κ / 6) * phi0 := by
  have he : edgeworthEnvelope h (-κ) x = edgeworthEnvelope h (-κ) |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, negative_edgeworth_envelope_even h κ x]
  rw [he]
  have hm := negative_edgeworth_envelope_antitoneOn h κ hk hh
    (show (0 : ℝ) ∈ Ici 0 by simp) (show |x| ∈ Ici 0 from abs_nonneg x) (abs_nonneg x)
  simpa only [edgeworthEnvelope, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero, mul_one, standardNormalDensity_zero, neg_div, sub_eq_add_neg, neg_zero, add_zero] using hm

theorem kappaE_le_hE : kappaE ≤ hE := by
  unfold kappaE hE
  apply (div_le_div_iff_of_pos_right sigmaE_pos).2
  linarith [pE_add_qE, pE_pos]

theorem kappaE_lt_hE : kappaE < hE := by
  unfold kappaE hE
  apply (div_lt_div_iff_of_pos_right sigmaE_pos).2
  linarith [pE_add_qE, pE_pos]

/-- The original negative-envelope shape: evenness, strict decrease, and
its attained global maximum. The maximum is derived from that shape. -/
theorem reflected_esseen_envelope_shape :
    Function.Even (edgeworthEnvelope hE (-kappaE)) ∧
      StrictAntiOn (edgeworthEnvelope hE (-kappaE)) (Ici 0) ∧
      IsGreatest (Set.range (edgeworthEnvelope hE (-kappaE)))
        ((hE / 2 - kappaE / 6) * phi0) := by
  have he := negative_edgeworth_envelope_even hE kappaE
  have hm := negative_edgeworth_envelope_strictAntiOn hE kappaE kappaE_pos.le kappaE_lt_hE
  have hz : edgeworthEnvelope hE (-kappaE) 0 = (hE / 2 - kappaE / 6) * phi0 := by
    simp only [edgeworthEnvelope, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      sub_zero, mul_one, standardNormalDensity_zero, neg_div, sub_eq_add_neg, neg_zero, add_zero]
  refine ⟨he, hm, ⟨⟨0, hz⟩, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  have hx : edgeworthEnvelope hE (-kappaE) x = edgeworthEnvelope hE (-kappaE) |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, he x]
  rw [hx, ← hz]
  exact hm.antitoneOn (by simp) (abs_nonneg x) (abs_nonneg x)

theorem reflected_esseen_envelope_gap (x : ℝ) :
    edgeworthEnvelope hE (-kappaE) x ≤ cE * betaE - kappaE / 3 * phi0 := by
  have hb := reflected_esseen_envelope_shape.2.2.2 (Set.mem_range_self x)
  rw [← esseen_peak_identity]
  convert hb using 1 <;> ring

theorem positive_esseen_envelope_away (ε x : ℝ) (hε : 0 ≤ ε) (hx : ε ≤ |x|) :
    edgeworthEnvelope hE kappaE x ≤ cE * betaE * Real.exp (-ε ^ 2 / 2) := by
  have hcoef : hE / 2 + kappaE / 6 * (1 - x ^ 2) ≤ hE / 2 + kappaE / 6 := by
    nlinarith [mul_nonneg kappaE_pos.le (sq_nonneg x)]
  have hm := mul_le_mul_of_nonneg_right hcoef (standardNormalDensity_pos x).le
  have hxs : ε ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
  have hex : Real.exp (-x ^ 2 / 2) ≤ Real.exp (-ε ^ 2 / 2) := Real.exp_le_exp.2 (by linarith)
  have hc : 0 ≤ (hE / 2 + kappaE / 6) * phi0 :=
    mul_nonneg (by linarith [hE_pos, kappaE_pos]) phi0_pos.le
  have he := mul_le_mul_of_nonneg_left hex hc
  unfold edgeworthEnvelope
  apply hm.trans
  rw [standardNormalDensity_formula]
  rw [← esseen_peak_identity]
  convert he using 1 <;> ring

end BerryEsseen
