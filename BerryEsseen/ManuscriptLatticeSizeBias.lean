import BerryEsseen.LatticeDeficit
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The actual positive and negative size-biased probability measures used in
the manuscript's lattice-deficit decomposition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def manuscriptHalfFirstMoment (P : StandardizedLaw) : ℝ :=
  (∫ x, |x| ∂P.measure) / 2

theorem manuscriptHalfFirstMoment_pos (P : StandardizedLaw) :
    0 < manuscriptHalfFirstMoment P := by
  have hn : 0 ≤ ∫ x, |x| ∂P.measure := integral_nonneg (fun _ => abs_nonneg _)
  have hz : (∫ x, |x| ∂P.measure) ≠ 0 := by
    intro h
    have ha := (integral_eq_zero_iff_of_nonneg (fun x : ℝ => abs_nonneg x)
      P.first_integrable.abs).mp h
    have he : (∫ x, x ^ 2 ∂P.measure) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ha] with x hx
      have hxx : x = 0 := abs_eq_zero.mp hx
      simp [hxx]
    rw [P.second_one] at he
    norm_num at he
  exact div_pos (lt_of_le_of_ne hn (Ne.symm hz)) (by norm_num)

theorem manuscript_positive_part_integral (P : StandardizedLaw) :
    (∫ x, max x 0 ∂P.measure) = manuscriptHalfFirstMoment P := by
  have he : (fun x : ℝ => max x 0) = fun x => (|x| + x) / 2 := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
  rw [he, integral_div, integral_add P.first_integrable.abs P.first_integrable,
    P.mean_zero, add_zero]
  rfl

theorem manuscriptHalfFirstMoment_reflected (P : StandardizedLaw) :
    manuscriptHalfFirstMoment (reflectedLaw P) = manuscriptHalfFirstMoment P := by
  unfold manuscriptHalfFirstMoment reflectedLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_neg]

def manuscriptPositiveSizeBias (P : StandardizedLaw) : Measure ℝ :=
  P.measure.withDensity (fun x => ENNReal.ofReal (max x 0 / manuscriptHalfFirstMoment P))

def manuscriptNegativeSizeBias (P : StandardizedLaw) : Measure ℝ :=
  manuscriptPositiveSizeBias (reflectedLaw P)

def manuscriptSizeBiasedProduct (P : StandardizedLaw) : Measure (ℝ × ℝ) :=
  (manuscriptNegativeSizeBias P).prod (manuscriptPositiveSizeBias P)

theorem manuscriptPositiveSizeBias_integral (P : StandardizedLaw) (f : ℝ → ℝ) :
    (∫ x, f x ∂manuscriptPositiveSizeBias P) =
      (∫ x, max x 0 * f x ∂P.measure) / manuscriptHalfFirstMoment P := by
  rw [manuscriptPositiveSizeBias, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (le_max_right _ _)
    (manuscriptHalfFirstMoment_pos P).le), smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact integral_div _ _

theorem manuscriptPositiveSizeBias_integrable_iff (P : StandardizedLaw) (f : ℝ → ℝ) :
    Integrable f (manuscriptPositiveSizeBias P) ↔
      Integrable (fun x => max x 0 * f x) P.measure := by
  rw [manuscriptPositiveSizeBias, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by simp)]
  simp only [ENNReal.toReal_ofReal (div_nonneg (le_max_right _ _)
    (manuscriptHalfFirstMoment_pos P).le), smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  constructor
  · intro hi
    simpa only [div_mul_cancel₀ _ (manuscriptHalfFirstMoment_pos P).ne'] using
      hi.mul_const (manuscriptHalfFirstMoment P)
  · exact fun hi => hi.div_const _

instance manuscriptPositiveSizeBias_finite (P : StandardizedLaw) :
    IsFiniteMeasure (manuscriptPositiveSizeBias P) :=
  isFiniteMeasure_withDensity_ofReal
    ((P.first_integrable.sup (integrable_const 0)).div_const _).hasFiniteIntegral

instance manuscriptPositiveSizeBias_probability (P : StandardizedLaw) :
    IsProbabilityMeasure (manuscriptPositiveSizeBias P) := by
  have hm := manuscriptHalfFirstMoment_pos P
  have he := manuscriptPositiveSizeBias_integral P (fun _ => 1)
  simp only [integral_const, smul_eq_mul, mul_one, manuscript_positive_part_integral,
    div_self hm.ne'] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he

instance manuscriptNegativeSizeBias_probability (P : StandardizedLaw) :
    IsProbabilityMeasure (manuscriptNegativeSizeBias P) :=
  manuscriptPositiveSizeBias_probability (reflectedLaw P)

instance manuscriptSizeBiasedProduct_probability (P : StandardizedLaw) :
    IsProbabilityMeasure (manuscriptSizeBiasedProduct P) := by
  unfold manuscriptSizeBiasedProduct
  infer_instance

theorem manuscriptPositiveSizeBias_positive (P : StandardizedLaw) :
    ∀ᵐ x ∂manuscriptPositiveSizeBias P, 0 < x := by
  rw [manuscriptPositiveSizeBias, ae_withDensity_iff (by fun_prop)]
  filter_upwards [] with x hx
  by_contra hn
  have hle : x ≤ 0 := le_of_not_gt hn
  simp [max_eq_right hle] at hx

theorem manuscriptPositiveSizeBias_ae (P : StandardizedLaw) (p : ℝ → Prop)
    (hp : ∀ᵐ x ∂P.measure, p x) : ∀ᵐ x ∂manuscriptPositiveSizeBias P, p x :=
  (withDensity_absolutelyContinuous P.measure _).ae_le hp

theorem manuscriptNegativeSizeBias_integral (P : StandardizedLaw) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ x, f x ∂manuscriptNegativeSizeBias P) =
      (∫ x, max (-x) 0 * f (-x) ∂P.measure) / manuscriptHalfFirstMoment P := by
  rw [manuscriptNegativeSizeBias, manuscriptPositiveSizeBias_integral,
    manuscriptHalfFirstMoment_reflected]
  congr 1
  change (∫ x, max x 0 * f x ∂P.measure.map (fun x => -x)) = _
  rw [integral_map (by fun_prop) (by fun_prop)]

theorem manuscriptSizeBias_weighted_first_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => max x 0 * x) P.measure := by
  apply P.second_integrable.mono' (by fun_prop)
  filter_upwards [] with x
  rcases le_total 0 x with hx | hx
  · simp only [max_eq_left hx, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
    nlinarith
  · simp [max_eq_right hx, sq_nonneg]

theorem manuscriptSizeBias_weighted_second_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => max x 0 * x ^ 2) P.measure := by
  apply P.third_integrable.mono' (by fun_prop)
  filter_upwards [] with x
  rcases le_total 0 x with hx | hx
  · simp only [max_eq_left hx, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx]
    nlinarith
  · simp [max_eq_right hx, pow_nonneg (abs_nonneg x)]

theorem manuscriptPositiveSizeBias_first_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x) (manuscriptPositiveSizeBias P) :=
  (manuscriptPositiveSizeBias_integrable_iff P _).mpr
    (manuscriptSizeBias_weighted_first_integrable P)

theorem manuscriptPositiveSizeBias_second_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x ^ 2) (manuscriptPositiveSizeBias P) :=
  (manuscriptPositiveSizeBias_integrable_iff P _).mpr
    (manuscriptSizeBias_weighted_second_integrable P)

theorem manuscriptNegativeSizeBias_first_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x) (manuscriptNegativeSizeBias P) :=
  manuscriptPositiveSizeBias_first_integrable (reflectedLaw P)

theorem manuscriptNegativeSizeBias_second_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x ^ 2) (manuscriptNegativeSizeBias P) :=
  manuscriptPositiveSizeBias_second_integrable (reflectedLaw P)

theorem manuscriptSizeBias_negative_weighted_first_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => max (-x) 0 * (-x)) P.measure := by
  have hi := manuscriptSizeBias_weighted_first_integrable (reflectedLaw P)
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mp hi

theorem manuscriptSizeBias_negative_weighted_second_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => max (-x) 0 * (-x) ^ 2) P.measure := by
  have hi := manuscriptSizeBias_weighted_second_integrable (reflectedLaw P)
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mp hi

theorem manuscriptSizeBiasedProduct_first_identity (P : StandardizedLaw) :
    manuscriptHalfFirstMoment P *
      (∫ z, z.1 + z.2 ∂manuscriptSizeBiasedProduct P) = 1 := by
  rw [manuscriptSizeBiasedProduct, integral_add
    ((manuscriptNegativeSizeBias_first_integrable P).comp_fst _)
    ((manuscriptPositiveSizeBias_first_integrable P).comp_snd _),
    integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x)]
  simp only [probReal_univ, one_smul]
  rw [manuscriptNegativeSizeBias_integral P _ (by fun_prop),
    manuscriptPositiveSizeBias_integral]
  rw [← add_div]
  have hm := manuscriptHalfFirstMoment_pos P
  rw [mul_div_cancel₀ _ hm.ne']
  rw [← integral_add (manuscriptSizeBias_negative_weighted_first_integrable P)
    (manuscriptSizeBias_weighted_first_integrable P)]
  convert P.second_one using 1
  congr 1
  funext x
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; ring

theorem manuscriptSizeBiasedProduct_second_identity (P : StandardizedLaw) :
    manuscriptHalfFirstMoment P *
      (∫ z, z.1 ^ 2 + z.2 ^ 2 ∂manuscriptSizeBiasedProduct P) = thirdMoment P := by
  rw [manuscriptSizeBiasedProduct, integral_add
    ((manuscriptNegativeSizeBias_second_integrable P).comp_fst _)
    ((manuscriptPositiveSizeBias_second_integrable P).comp_snd _),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)]
  simp only [probReal_univ, one_smul]
  rw [manuscriptNegativeSizeBias_integral P _ (by fun_prop),
    manuscriptPositiveSizeBias_integral]
  rw [← add_div, mul_div_cancel₀ _ (manuscriptHalfFirstMoment_pos P).ne']
  rw [← integral_add (manuscriptSizeBias_negative_weighted_second_integrable P)
    (manuscriptSizeBias_weighted_second_integrable P)]
  unfold thirdMoment
  congr 1
  funext x
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]; ring
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), abs_of_nonpos hx]; ring

theorem manuscriptSizeBiasedProduct_signed_identity (P : StandardizedLaw) :
    manuscriptHalfFirstMoment P *
      (∫ z, z.2 ^ 2 - z.1 ^ 2 ∂manuscriptSizeBiasedProduct P) = signedThirdMoment P := by
  rw [manuscriptSizeBiasedProduct, integral_sub
    ((manuscriptPositiveSizeBias_second_integrable P).comp_snd _)
    ((manuscriptNegativeSizeBias_second_integrable P).comp_fst _),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2)]
  simp only [probReal_univ, one_smul]
  rw [manuscriptNegativeSizeBias_integral P _ (by fun_prop),
    manuscriptPositiveSizeBias_integral]
  rw [← sub_div, mul_div_cancel₀ _ (manuscriptHalfFirstMoment_pos P).ne']
  rw [← integral_sub (manuscriptSizeBias_weighted_second_integrable P)
    (manuscriptSizeBias_negative_weighted_second_integrable P)]
  unfold signedThirdMoment
  congr 1
  funext x
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]; ring
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]; ring

def manuscriptLatticeDeficitKernel (h : ℝ) (z : ℝ × ℝ) : ℝ :=
  (Real.sqrt (cStar - 2) * z.1 - Real.sqrt (cStar - 4) * z.2) ^ 2 +
    3 * (z.1 + z.2) * (z.1 + z.2 - h)

theorem manuscriptLatticeDeficitKernel_identity (h : ℝ) (z : ℝ × ℝ) :
    manuscriptLatticeDeficitKernel h z =
      cStar * (z.1 ^ 2 + z.2 ^ 2) - (z.2 ^ 2 - z.1 ^ 2) - 3 * h * (z.1 + z.2) := by
  have hc := cStar_effective_bounds.1
  have ha := Real.sq_sqrt (show 0 ≤ cStar - 2 by linarith)
  have hb := Real.sq_sqrt (show 0 ≤ cStar - 4 by linarith)
  have hab : (cStar - 2) * (cStar - 4) = 9 := by
    unfold cStar
    nlinarith only [sqrt10_sq]
  have hs : Real.sqrt (cStar - 2) * Real.sqrt (cStar - 4) = 3 := by
    have hsq : (Real.sqrt (cStar - 2) * Real.sqrt (cStar - 4)) ^ 2 = 9 := by
      rw [mul_pow, ha, hb, hab]
    have hn := mul_nonneg (Real.sqrt_nonneg (cStar - 2)) (Real.sqrt_nonneg (cStar - 4))
    nlinarith
  unfold manuscriptLatticeDeficitKernel
  rw [show (Real.sqrt (cStar - 2) * z.1 - Real.sqrt (cStar - 4) * z.2) ^ 2 =
    (Real.sqrt (cStar - 2)) ^ 2 * z.1 ^ 2 +
    (Real.sqrt (cStar - 4)) ^ 2 * z.2 ^ 2 -
    2 * (Real.sqrt (cStar - 2) * Real.sqrt (cStar - 4)) * (z.1 * z.2) by ring,
    ha, hb, hs]
  ring

theorem manuscriptLatticeDeficitKernel_integrable (P : StandardizedLaw) (h : ℝ) :
    Integrable (manuscriptLatticeDeficitKernel h) (manuscriptSizeBiasedProduct P) := by
  change Integrable (fun z => manuscriptLatticeDeficitKernel h z) _
  simp_rw [manuscriptLatticeDeficitKernel_identity]
  have ha1 := (manuscriptNegativeSizeBias_first_integrable P).comp_fst (manuscriptPositiveSizeBias P)
  have hb1 := (manuscriptPositiveSizeBias_first_integrable P).comp_snd (manuscriptNegativeSizeBias P)
  have ha2 := (manuscriptNegativeSizeBias_second_integrable P).comp_fst (manuscriptPositiveSizeBias P)
  have hb2 := (manuscriptPositiveSizeBias_second_integrable P).comp_snd (manuscriptNegativeSizeBias P)
  exact (((ha2.add hb2).const_mul cStar).sub (hb2.sub ha2)).sub
    ((ha1.add hb1).const_mul (3 * h))

/-- Equation (effective-lattice-deficit), with the actual size-biased product. -/
theorem manuscript_lattice_deficit_decomposition (P : StandardizedLaw) (h : ℝ)
    (hκ : 0 ≤ signedThirdMoment P) :
    latticeMomentDeficit P h = manuscriptHalfFirstMoment P *
      ∫ z, manuscriptLatticeDeficitKernel h z ∂manuscriptSizeBiasedProduct P := by
  have ha1 := (manuscriptNegativeSizeBias_first_integrable P).comp_fst (manuscriptPositiveSizeBias P)
  have hb1 := (manuscriptPositiveSizeBias_first_integrable P).comp_snd (manuscriptNegativeSizeBias P)
  have ha2 := (manuscriptNegativeSizeBias_second_integrable P).comp_fst (manuscriptPositiveSizeBias P)
  have hb2 := (manuscriptPositiveSizeBias_second_integrable P).comp_snd (manuscriptNegativeSizeBias P)
  have he : (∫ z, manuscriptLatticeDeficitKernel h z ∂manuscriptSizeBiasedProduct P) =
      cStar * (∫ z, z.1 ^ 2 + z.2 ^ 2 ∂manuscriptSizeBiasedProduct P) -
        (∫ z, z.2 ^ 2 - z.1 ^ 2 ∂manuscriptSizeBiasedProduct P) -
        3 * h * (∫ z, z.1 + z.2 ∂manuscriptSizeBiasedProduct P) := by
    simp_rw [manuscriptLatticeDeficitKernel_identity]
    unfold manuscriptSizeBiasedProduct
    have hi : Integrable (fun z : ℝ × ℝ => cStar * (z.1 ^ 2 + z.2 ^ 2) -
        (z.2 ^ 2 - z.1 ^ 2)) ((manuscriptNegativeSizeBias P).prod (manuscriptPositiveSizeBias P)) :=
      ((ha2.add hb2).const_mul cStar).sub (hb2.sub ha2)
    have hj : Integrable (fun z : ℝ × ℝ => 3 * h * (z.1 + z.2))
        ((manuscriptNegativeSizeBias P).prod (manuscriptPositiveSizeBias P)) :=
      (ha1.add hb1).const_mul (3 * h)
    have hs := integral_sub hi hj
    simp only [Pi.sub_apply] at hs
    rw [hs]
    have hs' := integral_sub ((ha2.add hb2).const_mul cStar) (hb2.sub ha2)
    simp only [Pi.sub_apply, Pi.add_apply] at hs'
    rw [hs', integral_const_mul, integral_const_mul]
  rw [he]
  have h1 := manuscriptSizeBiasedProduct_first_identity P
  have h2 := manuscriptSizeBiasedProduct_second_identity P
  have h3 := manuscriptSizeBiasedProduct_signed_identity P
  unfold latticeMomentDeficit
  rw [abs_of_nonneg hκ]
  linear_combination -cStar * h2 + h3 + 3 * h * h1

end BerryEsseen
