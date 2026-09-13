import BerryEsseen.SmallVarianceSequence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem standardizedLaw_rigidity (P Q : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hmap : Q.measure = standardizedMeasure P.measure m σ) : Q = P := by
  have hmean := Q.mean_zero
  rw [hmap, standardizedMeasure, integral_map (by fun_prop) (by fun_prop), integral_div,
    integral_sub P.first_integrable (integrable_const m), P.mean_zero] at hmean
  simp only [integral_const, probReal_univ, one_smul, zero_sub] at hmean
  have hm : m = 0 := by
    have h := (div_eq_zero_iff).1 hmean
    rcases h with h | h
    · exact neg_eq_zero.1 h
    · exact False.elim (hσ.ne' h)
  have hsecond := Q.second_one
  rw [hmap, standardizedMeasure, integral_map (by fun_prop) (by fun_prop)] at hsecond
  simp only [hm, sub_zero, div_pow] at hsecond
  rw [integral_div, P.second_one] at hsecond
  have hs : σ = 1 := by
    have h := (div_eq_one_iff_eq (pow_ne_zero 2 hσ.ne')).1 hsecond
    nlinarith
  apply standardizedLaw_eq_of_measure_eq
  rw [hmap, hm, hs]
  simp [standardizedMeasure]

theorem standardizedTwoCluster_eq_of_affine_representation (Z : StandardizedLaw)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Ioo 0 1) (m d : ℝ) (hd : 0 < d)
    (hrep : standardizedMeasure Z.measure m d = twoClusterMeasure P Q p) :
    standardizedTwoClusterLaw P Q p hp = Z := by
  let σ := Real.sqrt (clusterVariance P Q p)
  have hσ : 0 < σ := Real.sqrt_pos.2 (clusterVariance_pos P Q p hp)
  apply standardizedLaw_rigidity Z _ (m + d * p) (d * σ) (mul_pos hd hσ)
  rw [standardizedTwoClusterLaw_measure, ← hrep]
  unfold standardizedMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  change ((x - m) / d - p) / σ = (x - (m + d * p)) / (d * σ)
  field_simp [hd.ne', hσ.ne']
  ring

end BerryEsseen
