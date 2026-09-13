import BerryEsseen.LatticeConditioning

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem probability_two_atoms_mixture (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a ≠ b) (hx : ∀ᵐ x ∂μ, x = a ∨ x = b) :
    μ = mixtureMeasure (Measure.dirac a) (Measure.dirac b) (μ.real {b}) := by
  have he := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac hab).mp hx
  have hcomp : μ.real {a} = 1 - μ.real {b} := by
    rw [← probReal_compl_eq_one_sub (measurableSet_singleton b)]
    apply measureReal_congr
    filter_upwards [hx] with x hx
    apply propext
    constructor
    · rintro rfl
      exact hab
    · exact hx.resolve_right
  have hleft : ENNReal.ofReal (1 - μ.real {b}) = μ {a} := by
    rw [← hcomp]
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hright : ENNReal.ofReal (μ.real {b}) = μ {b} := ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [mixtureMeasure, hleft, hright]
  exact he

theorem two_atoms_standardizedMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a < b) (hx : ∀ᵐ x ∂μ, x = a ∨ x = b) :
    standardizedMeasure μ a (b - a) = bernoulliMeasure (μ.real {b}) := by
  have he := probability_two_atoms_mixture μ a b hab.ne hx
  conv_lhs => rw [he]
  unfold standardizedMeasure mixtureMeasure bernoulliMeasure
  rw [Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul,
    Measure.map_dirac (by fun_prop), Measure.map_dirac (by fun_prop)]
  simp only [sub_self, zero_div, div_self (sub_pos.mpr hab).ne']
  rfl

theorem rawStdDev_dirac (a : ℝ) : rawStdDev (Measure.dirac a) = 0 := by
  simp [rawStdDev, rawMean]

theorem two_atoms_probability_interior (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a < b) (hx : ∀ᵐ x ∂μ, x = a ∨ x = b)
    (hσ : 0 < rawStdDev μ) : μ.real {b} ∈ Ioo 0 1 := by
  have hp0 : 0 ≤ μ.real {b} := measureReal_nonneg
  have hp1 : μ.real {b} ≤ 1 := measureReal_le_one
  have he := probability_two_atoms_mixture μ a b hab.ne hx
  constructor
  · by_contra h
    have hz : μ.real {b} = 0 := le_antisymm (le_of_not_gt h) hp0
    have hm : μ = Measure.dirac a := by simpa [mixtureMeasure, hz] using he
    rw [hm, rawStdDev_dirac] at hσ
    exact lt_irrefl 0 hσ
  · by_contra h
    have hz : μ.real {b} = 1 := le_antisymm hp1 (le_of_not_gt h)
    have hm : μ = Measure.dirac b := by simpa [mixtureMeasure, hz] using he
    rw [hm, rawStdDev_dirac] at hσ
    exact lt_irrefl 0 hσ

theorem two_atoms_canonical_standardization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a < b) (hx : ∀ᵐ x ∂μ, x = a ∨ x = b)
    (hσ : 0 < rawStdDev μ) :
    (standardizedBernoulliLaw (μ.real {b}) (two_atoms_probability_interior μ a b hab hx hσ)).measure =
      standardizedMeasure μ (rawMean μ) (rawStdDev μ) ∧
      rawMean μ = a + (b - a) * μ.real {b} ∧
      rawStdDev μ = (b - a) * Real.sqrt (μ.real {b} * (1 - μ.real {b})) := by
  let p := μ.real {b}
  have hp := two_atoms_probability_interior μ a b hab hx hσ
  have hscale : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  have hrep := two_atoms_standardizedMeasure μ a b hab hx
  have hmap : (standardizedBernoulliLaw p hp).measure =
      standardizedMeasure μ (a + (b - a) * p) ((b - a) * Real.sqrt (p * (1 - p))) := by
    rw [standardizedBernoulliLaw, standardizedTwoClusterLaw_measure, zero_clusterVariance, twoCluster_zero_noise]
    change standardizedMeasure (bernoulliMeasure p) p (Real.sqrt (p * (1 - p))) = _
    rw [← hrep]
    unfold standardizedMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    change ((x - a) / (b - a) - p) / Real.sqrt (p * (1 - p)) = _
    field_simp [(sub_pos.mpr hab).ne', hscale.ne']
    <;> ring
  have hmom := raw_moments_of_standardized_representation μ (standardizedBernoulliLaw p hp)
    (a + (b - a) * p) ((b - a) * Real.sqrt (p * (1 - p)))
    (mul_pos (sub_pos.mpr hab) hscale) hmap
  refine ⟨?_, hmom.1, hmom.2.1⟩
  rw [hmom.1, hmom.2.1]
  exact hmap

end BerryEsseen
