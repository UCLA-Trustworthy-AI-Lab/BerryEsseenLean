import BerryEsseen.TwoPointNormalization
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem cube_difference_six (x y : ℝ) (hx : |x| ≤ 6) (hy : |y| ≤ 6) :
    |x ^ 3 - y ^ 3| ≤ 108 * |x - y| := by
  have hxx : |x| ^ 2 ≤ 36 := by nlinarith [abs_nonneg x]
  have hyy : |y| ^ 2 ≤ 36 := by nlinarith [abs_nonneg y]
  have hxy : |x| * |y| ≤ 36 := by
    have h := mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 6)
    norm_num at h
    exact h
  have hfactor : |x ^ 2 + x * y + y ^ 2| ≤ 108 := by
    calc
      _ ≤ |x ^ 2 + x * y| + |y ^ 2| := abs_add_le _ _
      _ ≤ |x ^ 2| + |x * y| + |y ^ 2| := by linarith [abs_add_le (x ^ 2) (x * y)]
      _ ≤ 108 := by rw [abs_pow, abs_pow, abs_mul]; linarith
  rw [show x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) by ring, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hfactor (abs_nonneg (x - y))]

theorem absolute_cube_difference_six (x y : ℝ) (hx : |x| ≤ 6) (hy : |y| ≤ 6) :
    |(|x| ^ 3) - |y| ^ 3| ≤ 108 * |x - y| := by
  have h := cube_difference_six |x| |y| (by simpa using hx) (by simpa using hy)
  exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by norm_num))

theorem real_function_integrable_of_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (C : ℝ) (hf : Measurable f) (hC : ∀ᵐ x ∂μ, |f x| ≤ C) : Integrable f μ := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using hC

/-- The manuscript's mean-value estimate, on a neighborhood of [-5,5]. -/
theorem manuscript_cube_centering_mvt (x y : ℝ)
    (hx : |x| ≤ 51 / 10) (hy : |y| ≤ 51 / 10) :
    |x ^ 3 - y ^ 3| ≤ 100 * |x - y| := by
  have hd : ∀ z ∈ Icc (-(51 / 10 : ℝ)) (51 / 10),
      HasDerivWithinAt (fun t : ℝ => t ^ 3) (3 * z ^ 2)
        (Icc (-(51 / 10 : ℝ)) (51 / 10)) z := by
    intro z hz
    simpa using ((hasDerivAt_id z).pow 3).hasDerivWithinAt
  have hb : ∀ z ∈ Icc (-(51 / 10 : ℝ)) (51 / 10), ‖3 * z ^ 2‖ ≤ 100 := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hz.1, hz.2]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
    (abs_le.mp hy) (abs_le.mp hx)
  simpa only [Real.norm_eq_abs] using hh

theorem manuscript_absolute_cube_centering_mvt (x y : ℝ)
    (hx : |x| ≤ 51 / 10) (hy : |y| ≤ 51 / 10) :
    |(|x| ^ 3) - |y| ^ 3| ≤ 100 * |x - y| := by
  have hh := manuscript_cube_centering_mvt |x| |y| (by simpa using hx) (by simpa using hy)
  exact hh.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by norm_num))

theorem bounded_cubic_centering_errors (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m δ : ℝ) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hm : |m| ≤ 2 * δ) (hx : ∀ᵐ x ∂μ, |x| ≤ 5) :
    |(∫ x, |x - m| ^ 3 ∂μ) - ∫ x, |x| ^ 3 ∂μ| ≤ 200 * δ ∧
      |(∫ x, (x - m) ^ 3 ∂μ) - ∫ x, x ^ 3 ∂μ| ≤ 200 * δ := by
  have hm1 : |m| ≤ 1 := by linarith [hδ.2]
  have hy : ∀ᵐ x ∂μ, |x - m| ≤ 6 := by
    filter_upwards [hx] with x hx
    linarith [abs_sub x m]
  have hy' : ∀ᵐ x ∂μ, |x - m| ≤ 51 / 10 := by
    filter_upwards [hx] with x hx
    linarith [abs_sub x m, hδ.2]
  have hdiff1 : ∀ᵐ x ∂μ, |(|x - m| ^ 3) - |x| ^ 3| ≤ 200 * δ := by
    filter_upwards [hx, hy'] with x hx hy
    have h := manuscript_absolute_cube_centering_mvt (x - m) x hy (by linarith)
    have he : |x - m - x| = |m| := by rw [show x - m - x = -m by ring, abs_neg]
    rw [he] at h
    linarith
  have hdiff2 : ∀ᵐ x ∂μ, |(x - m) ^ 3 - x ^ 3| ≤ 200 * δ := by
    filter_upwards [hx, hy'] with x hx hy
    have h := manuscript_cube_centering_mvt (x - m) x hy (by linarith)
    have he : |x - m - x| = |m| := by rw [show x - m - x = -m by ring, abs_neg]
    rw [he] at h
    linarith
  have hi (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ᵐ x ∂μ, |f x| ≤ 216) : Integrable f μ :=
    real_function_integrable_of_abs_le μ f 216 hf hb
  have hix : Integrable (fun x : ℝ => x ^ 3) μ := hi _ (by fun_prop) (by
    filter_upwards [hx] with x hx
    rw [abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg x) (show |x| ≤ 6 by linarith) 3
    norm_num at h
    exact h)
  have hiy : Integrable (fun x : ℝ => (x - m) ^ 3) μ := hi _ (by fun_prop) (by
    filter_upwards [hy] with x hy
    rw [abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg (x - m)) hy 3
    norm_num at h
    exact h)
  have hiax : Integrable (fun x : ℝ => |x| ^ 3) μ := by simpa only [Real.norm_eq_abs, abs_pow] using hix.norm
  have hiay : Integrable (fun x : ℝ => |x - m| ^ 3) μ := by simpa only [Real.norm_eq_abs, abs_pow] using hiy.norm
  constructor
  · rw [← integral_sub hiay hiax]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x : ℝ => |x - m| ^ 3 - |x| ^ 3) (by simpa only [Real.norm_eq_abs] using hdiff1)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  · rw [← integral_sub hiy hix]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x : ℝ => (x - m) ^ 3 - x ^ 3) (by simpa only [Real.norm_eq_abs] using hdiff2)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem latticeDeficitPolynomial_nonneg (h x : ℝ) (hx : h ≤ |x|) :
    0 ≤ latticeDeficitPolynomial h x := by
  have hpow : h * x ^ 2 ≤ |x| ^ 3 := by
    calc
      h * x ^ 2 = h * |x| ^ 2 := by rw [sq_abs]
      _ ≤ |x| * |x| ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
      _ = |x| ^ 3 := by ring
  have hcube : x ^ 3 ≤ |x| ^ 3 := by
    have hc : x ^ 3 ≤ |x ^ 3| := le_abs_self (x ^ 3)
    rwa [abs_pow] at hc
  have hc := mul_nonneg (show 0 ≤ cStar - 4 by linarith [cStar_effective_bounds.1])
    (pow_nonneg (abs_nonneg x) 3)
  unfold latticeDeficitPolynomial
  nlinarith only [hpow, hcube, hc]

theorem conditional_lattice_deficit_bound (P : StandardizedLaw) (a b h δ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = h) (hκ : 0 ≤ signedThirdMoment P)
    (hgeom : ∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x)
    (hD : latticeMomentDeficit P h ≤ δ) (hδ : 0 ≤ δ)
    (hmass : 1 / 2 ≤ P.measure.real {-a, b}) :
    (∫ x, latticeDeficitPolynomial h x ∂ProbabilityTheory.cond P.measure {-a, b}) ≤ 2 * δ := by
  have hset : MeasurableSet ({-a, b} : Set ℝ) := (measurableSet_singleton b).insert (-a)
  have hout : 0 ≤ ∫ x in ({-a, b}ᶜ : Set ℝ), latticeDeficitPolynomial h x ∂P.measure := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae hgeom, ae_restrict_mem hset.compl] with x hx hs
    have hne : x ≠ -a ∧ x ≠ b := by simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using hs
    apply latticeDeficitPolynomial_nonneg
    rcases hx with hx | hx | hx | hx
    · exact False.elim (hne.1 hx)
    · exact False.elim (hne.2 hx)
    · exact (show h ≤ -x by linarith).trans (neg_le_abs x)
    · exact (show h ≤ x by linarith).trans (le_abs_self x)
  have hsplit := integral_add_compl hset (latticeDeficitPolynomial_integrable P h)
  rw [latticeDeficitPolynomial_integral, ← abs_of_nonneg hκ] at hsplit
  change _ + _ = latticeMomentDeficit P h at hsplit
  rw [conditional_integral_real]
  apply (div_le_iff₀ (by linarith : 0 < P.measure.real {-a, b})).mpr
  nlinarith only [hsplit, hout, hD, mul_le_mul_of_nonneg_left hmass hδ]

def latticeCenteredDeficit (μ : Measure ℝ) (h : ℝ) : ℝ :=
  cStar * rawThirdAbsoluteMoment μ - (∫ x, (x - rawMean μ) ^ 3 ∂μ) - 3 * h * rawStdDev μ ^ 2

theorem manuscript_lattice_centering_quadratic_budget (h m δ : ℝ)
    (hh : h ∈ Icc 0 5) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hm : |m| ≤ 2 * δ) : 3 * h * m ^ 2 ≤ 60 * δ ^ 2 ∧ 60 * δ ^ 2 ≤ δ := by
  have hm2 : m ^ 2 ≤ 4 * δ ^ 2 := by
    have hp := mul_self_le_mul_self (abs_nonneg m) hm
    nlinarith [sq_abs m]
  have hhm := mul_le_mul_of_nonneg_right hh.2 (sq_nonneg m)
  constructor <;> nlinarith [hδ.1, hδ.2]

theorem bounded_lattice_centered_deficit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h δ : ℝ) (hh : h ∈ Icc 0 5) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hx : ∀ᵐ x ∂μ, |x| ≤ 5) (hm : |rawMean μ| ≤ 2 * δ)
    (hF : (∫ x, latticeDeficitPolynomial h x ∂μ) ≤ 2 * δ) :
    latticeCenteredDeficit μ h ≤ 2000 * δ := by
  have h1 : Integrable (fun x : ℝ => x) μ := real_function_integrable_of_abs_le μ _ 5 (by fun_prop) hx
  have h2 : Integrable (fun x : ℝ => x ^ 2) μ := real_function_integrable_of_abs_le μ _ 25 (by fun_prop) (by
    filter_upwards [hx] with x hx
    rw [abs_pow]
    nlinarith [abs_nonneg x])
  have h3 : Integrable (fun x : ℝ => x ^ 3) μ := real_function_integrable_of_abs_le μ _ 125 (by fun_prop) (by
    filter_upwards [hx] with x hx
    rw [abs_pow]
    have hp := pow_le_pow_left₀ (abs_nonneg x) hx 3
    norm_num at hp
    exact hp)
  have ha3 : Integrable (fun x : ℝ => |x| ^ 3) μ := by simpa only [Real.norm_eq_abs, abs_pow] using h3.norm
  have he : (∫ x, latticeDeficitPolynomial h x ∂μ) =
      cStar * (∫ x, |x| ^ 3 ∂μ) - (∫ x, x ^ 3 ∂μ) - 3 * h * (∫ x, x ^ 2 ∂μ) := by
    unfold latticeDeficitPolynomial
    have hi : Integrable (fun x : ℝ => cStar * |x| ^ 3 - x ^ 3) μ := (ha3.const_mul cStar).sub h3
    rw [integral_sub hi (h2.const_mul _), integral_sub (ha3.const_mul _) h3,
      integral_const_mul, integral_const_mul]
  rw [he] at hF
  have herr := bounded_cubic_centering_errors μ (rawMean μ) δ hδ hm hx
  have habs := (abs_le.mp herr.1).2
  have hsgn := (abs_le.mp herr.2).1
  have hc := cStar_effective_bounds
  have hmult := mul_le_mul_of_nonneg_left habs (show 0 ≤ cStar by linarith [hc.1])
  have hcδ := mul_le_mul_of_nonneg_right hc.2.le hδ.1
  have hquadratic := manuscript_lattice_centering_quadratic_budget h (rawMean μ) δ hh hδ hm
  unfold latticeCenteredDeficit rawThirdAbsoluteMoment
  rw [raw_centered_variance_formula μ h1 h2]
  nlinarith [hδ.1, hδ.2, hquadratic.1, hquadratic.2]

theorem conditional_pair_mem (μ : Measure ℝ) (a b : ℝ) :
    ∀ᵐ x ∂ProbabilityTheory.cond μ {a, b}, x = a ∨ x = b := by
  unfold ProbabilityTheory.cond
  apply Measure.ae_smul_measure
  have hset : MeasurableSet ({a, b} : Set ℝ) := (measurableSet_singleton b).insert a
  simpa only [mem_insert_iff, mem_singleton_iff] using ae_restrict_mem (μ := μ) hset

theorem effective_lattice_centered_conditioning (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧ P.measure {-a, b} ≠ 0 ∧
      P.measure.real ({-a, b}ᶜ : Set ℝ) ≤ δ ∧
      |rawMean (ProbabilityTheory.cond P.measure {-a, b})| ≤ 2 * δ ∧
      |rawStdDev (ProbabilityTheory.cond P.measure {-a, b}) ^ 2 - 1| ≤ 5 * δ ∧
      0 < rawStdDev (ProbabilityTheory.cond P.measure {-a, b}) ∧
      latticeCenteredDeficit (ProbabilityTheory.cond P.measure {-a, b}) h ≤ 2000 * δ := by
  obtain ⟨a, b, ha, hb, hab, hgeom, hnz, hr, hs1, hs2, hm, hv⟩ :=
    effective_lattice_conditioning P h δ hlat hβ hκ hD hδ
  let ν := ProbabilityTheory.cond P.measure {-a, b}
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  have hδ0 := hD.1.trans hD.2
  have hh := effective_lattice_span_bounds P h δ hβ hD hδ
  have hx : ∀ᵐ x ∂ν, |x| ≤ 5 := by
    filter_upwards [conditional_pair_mem P.measure (-a) b] with x hx
    rcases hx with rfl | rfl
    · rw [abs_neg, abs_of_pos ha]
      linarith [hh.2]
    · rw [abs_of_pos hb]
      linarith [hh.2]
  have hmass : 1 / 2 ≤ P.measure.real {-a, b} := by
    have he := probReal_compl_eq_one_sub ((measurableSet_singleton b).insert (-a)) (μ := P.measure)
    linarith
  have hF := conditional_lattice_deficit_bound P a b h δ ha hb hab hκ hgeom hD.2 hδ0 hmass
  have hσ : 0 < rawStdDev ν := by
    have hσ0 : 0 ≤ rawStdDev ν := Real.sqrt_nonneg _
    have hvlo := (abs_le.mp hv).1
    change -(5 * δ) ≤ rawStdDev ν ^ 2 - 1 at hvlo
    nlinarith
  exact ⟨a, b, ha, hb, hab, hnz, hr, hm, hv, hσ,
    bounded_lattice_centered_deficit ν h δ ⟨hlat.1.le, hh.2.le⟩ ⟨hδ0, hδ⟩ hx hm hF⟩

end BerryEsseen
