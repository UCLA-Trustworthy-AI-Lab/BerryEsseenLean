import BerryEsseen.ManuscriptClusterDifference

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

/-- Conditional centering cancels the first-order Taylor term for each label pair. -/
theorem manuscript_conditional_difference_taylor (P Q : CenteredFourthLaw) (ε a C : ℝ)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (g : ℝ → ℝ) (hg : Measurable g) (d : ℝ)
    (ht : ∀ x : ℝ, |x| ≤ 2 * ε → |g (a + x) - g a - d * x| ≤ C / 2 * x ^ 2) :
    Integrable (fun x => g (a + x)) (manuscriptDifferenceLaw P.measure Q.measure) ∧
    |(∫ x, g (a + x) ∂manuscriptDifferenceLaw P.measure Q.measure) - g a| ≤
      C / 2 * (P.secondMoment + Q.secondMoment) := by
  let ν := manuscriptDifferenceLaw P.measure Q.measure
  have h1 := manuscript_centered_difference_first_integrable P Q
  have h2 := manuscript_centered_difference_second_integrable P Q
  have hrem : Integrable (fun x => g (a + x) - g a - d * x) ν := by
    apply (h2.const_mul (C / 2)).mono' (by fun_prop)
    filter_upwards [manuscript_centered_difference_bounded P Q ε hP hQ] with x hx
    simpa only [Real.norm_eq_abs] using ht x hx
  have hi : Integrable (fun x => g (a + x)) ν := by
    convert (hrem.add (integrable_const (g a))).add (h1.const_mul d) using 1
    funext x
    dsimp
    ring
  have hi0 : Integrable (fun x => g (a+x) - g a) ν := hi.sub (integrable_const (g a))
  have he : (∫ x, g (a + x) - g a - d * x ∂ν) = (∫ x, g (a + x) ∂ν) - g a := by
    rw [integral_sub hi0 (h1.const_mul d),
      integral_sub hi (integrable_const _), integral_const_mul, manuscript_centered_difference_mean]
    simp
  have hr := abs_integral_le_integral_abs (f := fun x => g (a + x) - g a - d * x) (μ := ν)
  rw [he] at hr
  refine ⟨hi, hr.trans ?_⟩
  have hb := integral_mono_ae hrem.abs (h2.const_mul (C / 2))
    ((manuscript_centered_difference_bounded P Q ε hP hQ).mono fun x hx => ht x hx)
  rw [integral_const_mul, manuscript_centered_difference_second] at hb
  exact hb

theorem manuscript_cluster_difference_integral (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc 0 1) (g : ℝ → ℝ) (hg : Measurable g)
    (h00 : Integrable g (manuscriptDifferenceLaw P.measure P.measure))
    (h01 : Integrable (fun x => g (-1 + x)) (manuscriptDifferenceLaw P.measure Q.measure))
    (h10 : Integrable (fun x => g (1 + x)) (manuscriptDifferenceLaw Q.measure P.measure))
    (h11 : Integrable g (manuscriptDifferenceLaw Q.measure Q.measure)) :
    (∫ x, g x ∂manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)) =
      (1-p)^2 * (∫ x, g x ∂manuscriptDifferenceLaw P.measure P.measure) +
      (1-p)*p * (∫ x, g (-1+x) ∂manuscriptDifferenceLaw P.measure Q.measure) +
      (p*(1-p) * (∫ x, g (1+x) ∂manuscriptDifferenceLaw Q.measure P.measure) +
      p^2 * (∫ x, g x ∂manuscriptDifferenceLaw Q.measure Q.measure)) := by
  have h01' : Integrable g ((manuscriptDifferenceLaw P.measure Q.measure).map (fun x => -1+x)) :=
    (integrable_map_measure hg.aestronglyMeasurable (by fun_prop)).mpr h01
  have h10' : Integrable g ((manuscriptDifferenceLaw Q.measure P.measure).map (fun x => 1+x)) :=
    (integrable_map_measure hg.aestronglyMeasurable (by fun_prop)).mpr h10
  rw [manuscript_cluster_difference_measure]
  have h0 := h00.smul_measure (c := ENNReal.ofReal (1-p) * ENNReal.ofReal (1-p)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have h1 := h01'.smul_measure (c := ENNReal.ofReal (1-p) * ENNReal.ofReal p) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have h2 := h10'.smul_measure (c := ENNReal.ofReal p * ENNReal.ofReal (1-p)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have h3 := h11.smul_measure (c := ENNReal.ofReal p * ENNReal.ofReal p) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  rw [integral_add_measure (h0.add_measure h1) (h2.add_measure h3),
    integral_add_measure h0 h1, integral_add_measure h2 h3]
  simp only [integral_smul_measure, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2), smul_eq_mul]
  rw [integral_map (by fun_prop) hg.aestronglyMeasurable, integral_map (by fun_prop) hg.aestronglyMeasurable]
  ring

/-- Weighted conditional Taylor: E(D_U|B,B')=0 and E D_U²=2s. -/
theorem manuscript_cluster_conditional_taylor (P Q : CenteredFourthLaw) (p ε C : ℝ)
    (hp : p ∈ Icc 0 1)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (g g' : ℝ → ℝ) (hg : Measurable g)
    (ht : ∀ a ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, |x| ≤ 2 * ε →
      |g (a + x) - g a - g' a * x| ≤ C / 2 * x ^ 2) :
    |(∫ x, g x ∂manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p)) -
      ((1-p)^2 * g 0 + (1-p)*p*g (-1) + (p*(1-p)*g 1 + p^2*g 0))| ≤
      averageNoiseVariance P Q p * C := by
  have h00 := manuscript_conditional_difference_taylor P P ε 0 C hP hP g hg (g' 0) (ht 0 (by norm_num))
  have h01 := manuscript_conditional_difference_taylor P Q ε (-1) C hP hQ g hg (g' (-1)) (ht (-1) (by norm_num))
  have h10 := manuscript_conditional_difference_taylor Q P ε 1 C hQ hP g hg (g' 1) (ht 1 (by norm_num))
  have h11 := manuscript_conditional_difference_taylor Q Q ε 0 C hQ hQ g hg (g' 0) (ht 0 (by norm_num))
  simp only [zero_add] at h00 h11
  rw [manuscript_cluster_difference_integral P Q p hp g hg h00.1 h01.1 h10.1 h11.1]
  let A := (∫ x, g x ∂manuscriptDifferenceLaw P.measure P.measure) - g 0
  let B := (∫ x, g (-1+x) ∂manuscriptDifferenceLaw P.measure Q.measure) - g (-1)
  let D := (∫ x, g (1+x) ∂manuscriptDifferenceLaw Q.measure P.measure) - g 1
  let E := (∫ x, g x ∂manuscriptDifferenceLaw Q.measure Q.measure) - g 0
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp.2
  have h00' := mul_le_mul_of_nonneg_left h00.2 (sq_nonneg (1-p))
  have h01' := mul_le_mul_of_nonneg_left h01.2 (mul_nonneg hq hp.1)
  have h10' := mul_le_mul_of_nonneg_left h10.2 (mul_nonneg hp.1 hq)
  have h11' := mul_le_mul_of_nonneg_left h11.2 (sq_nonneg p)
  have h := (abs_add_le ((1-p)^2*A + (1-p)*p*B) (p*(1-p)*D + p^2*E)).trans
    (add_le_add (abs_add_le _ _) (abs_add_le _ _))
  simp only [abs_mul, abs_of_nonneg (sq_nonneg (1-p)), abs_of_nonneg (mul_nonneg hq hp.1),
    abs_of_nonneg (mul_nonneg hp.1 hq), abs_of_nonneg (sq_nonneg p), abs_of_nonneg hq, abs_of_nonneg hp.1] at h
  have hb := add_le_add (add_le_add h00' h01') (add_le_add h10' h11')
  have hh := h.trans hb
  convert hh using 1
  · congr 1
    dsimp [A,B,D,E]
    ring
  · unfold averageNoiseVariance
    ring

end BerryEsseen
