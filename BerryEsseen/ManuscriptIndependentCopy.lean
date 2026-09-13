import BerryEsseen.SharpComplexTaylor
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

/-- Difference of two independent samples, on the actual product probability space. -/
def manuscriptDifferenceLaw (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun xy : ℝ × ℝ => xy.1 - xy.2)

instance manuscriptDifferenceLaw_probability (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (manuscriptDifferenceLaw μ ν) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem manuscriptDifferenceLaw_charFun (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (u : ℝ) :
    charFun (manuscriptDifferenceLaw μ ν) u = charFun μ u * conj (charFun ν u) := by
  rw [← charFun_neg, charFun_apply_real, manuscriptDifferenceLaw,
    integral_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ × ℝ => Complex.exp ((u : ℂ) * (x.1 - x.2 : ℝ) * Complex.I)) =
      (fun x => Complex.exp ((u : ℂ) * (x.1 : ℂ) * Complex.I) *
        Complex.exp (((-u : ℝ) : ℂ) * (x.2 : ℂ) * Complex.I)) := by
    funext x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_prod_mul (fun x : ℝ => Complex.exp ((u : ℂ) * x * Complex.I))
    (fun x : ℝ => Complex.exp (((-u : ℝ) : ℂ) * x * Complex.I)), ← charFun_apply_real, ← charFun_apply_real]

theorem manuscriptDifferenceLaw_cos (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    (∫ x, Real.cos (u * x) ∂manuscriptDifferenceLaw μ μ) = ‖charFun μ u‖ ^ 2 := by
  have h := congrArg Complex.re (manuscriptDifferenceLaw_charFun μ μ u)
  rw [charFun_apply_real] at h
  change RCLike.re (∫ x, Complex.exp ((u : ℂ) * x * Complex.I) ∂manuscriptDifferenceLaw μ μ) = _ at h
  rw [← integral_re] at h
  · simpa only [RCLike.re_to_complex, ← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] using h
  · apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by simpa only [← Complex.ofReal_mul] using (le_of_eq (Complex.norm_exp_ofReal_mul_I (u * x))))

theorem manuscriptDifferenceLaw_second_integrable (P : StandardizedLaw) :
    Integrable (fun x : ℝ => x ^ 2) (manuscriptDifferenceLaw P.measure P.measure) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  convert ((P.second_integrable.comp_fst P.measure).sub
    ((P.first_integrable.mul_prod P.first_integrable).const_mul 2)).add
    (P.second_integrable.comp_snd P.measure) using 1
  funext x
  dsimp
  ring

theorem manuscriptDifferenceLaw_second (P : StandardizedLaw) :
    (∫ x, x ^ 2 ∂manuscriptDifferenceLaw P.measure P.measure) = 2 := by
  rw [manuscriptDifferenceLaw, integral_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ × ℝ => (x.1 - x.2) ^ 2) =
      (fun x => x.1 ^ 2 - 2 * (x.1 * x.2) + x.2 ^ 2) := by funext x; ring
  have hi : Integrable (fun x : ℝ × ℝ => x.1 ^ 2 - 2 * (x.1 * x.2)) (P.measure.prod P.measure) :=
    (P.second_integrable.comp_fst P.measure).sub ((P.first_integrable.mul_prod P.first_integrable).const_mul 2)
  rw [he, integral_add hi (P.second_integrable.comp_snd P.measure),
    integral_sub (P.second_integrable.comp_fst P.measure) ((P.first_integrable.mul_prod P.first_integrable).const_mul 2),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2), integral_const_mul,
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x), P.second_one, P.mean_zero]
  norm_num

theorem manuscriptDifferenceLaw_fourth_integrable (P : StandardizedLaw)
    (h4 : Integrable (fun x : ℝ => x ^ 4) P.measure) :
    Integrable (fun x : ℝ => x ^ 4) (manuscriptDifferenceLaw P.measure P.measure) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  have h3 := signedThirdMoment_integrable P
  convert ((((h4.comp_fst P.measure).sub ((h3.mul_prod P.first_integrable).const_mul 4)).add
    ((P.second_integrable.mul_prod P.second_integrable).const_mul 6)).sub
    ((P.first_integrable.mul_prod h3).const_mul 4)).add (h4.comp_snd P.measure) using 1
  funext x
  dsimp
  ring

theorem manuscriptDifferenceLaw_fourth (P : StandardizedLaw)
    (h4 : Integrable (fun x : ℝ => x ^ 4) P.measure) :
    (∫ x, x ^ 4 ∂manuscriptDifferenceLaw P.measure P.measure) = 2 * (∫ x, x ^ 4 ∂P.measure) + 6 := by
  have h3 := signedThirdMoment_integrable P
  have h31 := (h3.mul_prod P.first_integrable).const_mul 4
  have h22 := (P.second_integrable.mul_prod P.second_integrable).const_mul 6
  have h13 := (P.first_integrable.mul_prod h3).const_mul 4
  rw [manuscriptDifferenceLaw, integral_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ × ℝ => (x.1 - x.2) ^ 4) =
      (fun x => x.1 ^ 4 - 4 * (x.1 ^ 3 * x.2) + 6 * (x.1 ^ 2 * x.2 ^ 2) - 4 * (x.1 * x.2 ^ 3) + x.2 ^ 4) := by funext x; ring
  have hA : Integrable (fun x : ℝ × ℝ => x.1 ^ 4 - 4 * (x.1 ^ 3 * x.2)) (P.measure.prod P.measure) := (h4.comp_fst P.measure).sub h31
  have hB : Integrable (fun x : ℝ × ℝ => x.1 ^ 4 - 4 * (x.1 ^ 3 * x.2) + 6 * (x.1 ^ 2 * x.2 ^ 2)) (P.measure.prod P.measure) := hA.add h22
  have hC : Integrable (fun x : ℝ × ℝ => x.1 ^ 4 - 4 * (x.1 ^ 3 * x.2) + 6 * (x.1 ^ 2 * x.2 ^ 2) - 4 * (x.1 * x.2 ^ 3)) (P.measure.prod P.measure) := hB.sub h13
  rw [he, integral_add hC (h4.comp_snd P.measure),
    integral_sub hB h13,
    integral_add hA h22,
    integral_sub (h4.comp_fst P.measure) h31, integral_fun_fst (fun x : ℝ => x ^ 4),
    integral_fun_snd (fun x : ℝ => x ^ 4), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_prod_mul (fun x : ℝ => x ^ 3) (fun x : ℝ => x),
    integral_prod_mul (fun x : ℝ => x ^ 2) (fun x : ℝ => x ^ 2),
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x ^ 3), P.mean_zero, P.second_one]
  simp only [probReal_univ, one_smul]
  ring

end BerryEsseen
