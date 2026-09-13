import BerryEsseen.ClusterCharacteristic

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem manuscriptDifferenceLaw_add (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b : ℝ) :
    manuscriptDifferenceLaw (μ.map (fun x => a + x)) (ν.map (fun x => b + x)) =
      (manuscriptDifferenceLaw μ ν).map (fun x => (a - b) + x) := by
  rw [manuscriptDifferenceLaw, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), manuscriptDifferenceLaw,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  dsimp
  ring

/-- The four label pairs of two independent copies. -/
theorem manuscript_cluster_difference_measure (P Q : CenteredFourthLaw) (p : ℝ) :
    manuscriptDifferenceLaw (twoClusterMeasure P Q p) (twoClusterMeasure P Q p) =
      (ENNReal.ofReal (1-p) * ENNReal.ofReal (1-p)) • manuscriptDifferenceLaw P.measure P.measure +
      (ENNReal.ofReal (1-p) * ENNReal.ofReal p) • (manuscriptDifferenceLaw P.measure Q.measure).map (fun x => -1 + x) +
      ((ENNReal.ofReal p * ENNReal.ofReal (1-p)) • (manuscriptDifferenceLaw Q.measure P.measure).map (fun x => 1 + x) +
      (ENNReal.ofReal p * ENNReal.ofReal p) • manuscriptDifferenceLaw Q.measure Q.measure) := by
  let ν := Q.measure.map (fun x : ℝ => 1 + x)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have h01 : manuscriptDifferenceLaw P.measure ν = (manuscriptDifferenceLaw P.measure Q.measure).map (fun x => -1 + x) := by
    simpa only [zero_add, sub_zero, zero_sub, Measure.map_id', ν] using manuscriptDifferenceLaw_add P.measure Q.measure 0 1
  have h10 : manuscriptDifferenceLaw ν P.measure = (manuscriptDifferenceLaw Q.measure P.measure).map (fun x => 1 + x) := by
    simpa only [zero_add, sub_zero, zero_sub, Measure.map_id', ν] using manuscriptDifferenceLaw_add Q.measure P.measure 1 0
  have h11 : manuscriptDifferenceLaw ν ν = manuscriptDifferenceLaw Q.measure Q.measure := by
    simpa only [sub_self, zero_add, Measure.map_id', ν] using manuscriptDifferenceLaw_add Q.measure Q.measure 1 1
  letI : IsFiniteMeasure (ENNReal.ofReal (1-p) • P.measure) := Measure.smul_finite P.measure ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (ENNReal.ofReal p • ν) := Measure.smul_finite ν ENNReal.ofReal_ne_top
  change manuscriptDifferenceLaw ((ENNReal.ofReal (1-p)) • P.measure + ENNReal.ofReal p • ν)
    ((ENNReal.ofReal (1-p)) • P.measure + ENNReal.ofReal p • ν) = _
  simp only [manuscriptDifferenceLaw, Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.map_add _ _ (by fun_prop : Measurable (fun x : ℝ × ℝ => x.1 - x.2)),
    Measure.map_smul, smul_smul]
  rw [show (P.measure.prod ν).map (fun x : ℝ × ℝ => x.1-x.2) = _ from h01,
    show (ν.prod P.measure).map (fun x : ℝ × ℝ => x.1-x.2) = _ from h10,
    show (ν.prod ν).map (fun x : ℝ × ℝ => x.1-x.2) = _ from h11]
  simp only [smul_add, smul_smul, manuscriptDifferenceLaw]
  simp only [mul_comm (ENNReal.ofReal p) (ENNReal.ofReal (1-p))]
  abel

theorem manuscript_centered_difference_first_integrable (P Q : CenteredFourthLaw) :
    Integrable (fun x : ℝ => x) (manuscriptDifferenceLaw P.measure Q.measure) := by
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    ((P.first_integrable.comp_fst Q.measure).sub (Q.first_integrable.comp_snd P.measure))

theorem manuscript_centered_difference_mean (P Q : CenteredFourthLaw) :
    (∫ x, x ∂manuscriptDifferenceLaw P.measure Q.measure) = 0 := by
  rw [manuscriptDifferenceLaw, integral_map (by fun_prop) (by fun_prop),
    integral_sub (P.first_integrable.comp_fst Q.measure) (Q.first_integrable.comp_snd P.measure),
    integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x), P.mean_zero, Q.mean_zero]
  simp

theorem manuscript_centered_difference_second_integrable (P Q : CenteredFourthLaw) :
    Integrable (fun x : ℝ => x ^ 2) (manuscriptDifferenceLaw P.measure Q.measure) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  convert (((P.integrable_pow 2 (by omega)).comp_fst Q.measure).sub
    ((P.first_integrable.mul_prod Q.first_integrable).const_mul 2)).add
    ((Q.integrable_pow 2 (by omega)).comp_snd P.measure) using 1
  funext x
  dsimp
  ring

theorem manuscript_centered_difference_second (P Q : CenteredFourthLaw) :
    (∫ x, x ^ 2 ∂manuscriptDifferenceLaw P.measure Q.measure) = P.secondMoment + Q.secondMoment := by
  have hi : Integrable (fun x : ℝ × ℝ => x.1 ^ 2 - 2 * (x.1 * x.2)) (P.measure.prod Q.measure) :=
    ((P.integrable_pow 2 (by omega)).comp_fst Q.measure).sub ((P.first_integrable.mul_prod Q.first_integrable).const_mul 2)
  rw [manuscriptDifferenceLaw, integral_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ × ℝ => (x.1 - x.2) ^ 2) =
      (fun x => x.1 ^ 2 - 2 * (x.1 * x.2) + x.2 ^ 2) := by funext x; ring
  rw [he, integral_add hi ((Q.integrable_pow 2 (by omega)).comp_snd P.measure),
    integral_sub ((P.integrable_pow 2 (by omega)).comp_fst Q.measure) ((P.first_integrable.mul_prod Q.first_integrable).const_mul 2),
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2), integral_const_mul,
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x), P.mean_zero, Q.mean_zero]
  simp only [probReal_univ, one_smul, mul_zero, sub_zero]
  rfl

theorem manuscript_centered_difference_bounded (P Q : CenteredFourthLaw) (ε : ℝ)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    ∀ᵐ x ∂manuscriptDifferenceLaw P.measure Q.measure, |x| ≤ 2 * ε := by
  apply (ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)).mpr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [hP] with x hx
  filter_upwards [hQ] with y hy
  exact (abs_sub x y).trans (by linarith)

end BerryEsseen
