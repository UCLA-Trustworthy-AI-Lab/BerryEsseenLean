import BerryEsseen.LatticeIdentificationTransfer
import BerryEsseen.SignedSecondLimit

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem esseen_absolute_bound_three : ∀ᵐ x ∂esseenLaw.measure, |x| ≤ 3 := by
  filter_upwards [esseenLaw.measure.support_mem_ae] with x hx
  change x ∈ esseenMeasure.support at hx
  rw [esseen_support] at hx
  rcases mem_insert_iff.mp hx with rfl | hx
  · rw [abs_neg, abs_of_pos aE_pos]
    linarith [span_identity, bE_pos, hE_le_three]
  · rw [mem_singleton_iff.mp hx, abs_of_pos bE_pos]
    linarith [span_identity, aE_pos, hE_le_three]

theorem signed_esseen_measure_moments (ε : ℝ) (hε : ε ∈ ({-1, 1} : Set ℝ)) :
    (∫ x, |x| ^ 3 ∂(esseenLaw.measure.map (fun x => ε * x))) = betaE ∧
      (∫ x, x ^ 3 ∂(esseenLaw.measure.map (fun x => ε * x))) = ε * kappaE ∧
      (∫ x, x * |x| ∂(esseenLaw.measure.map (fun x => ε * x))) = ε * signedSecondMoment esseenLaw := by
  have hcases : ε = -1 ∨ ε = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hε
  have habs : |ε| = 1 := by rcases hcases with rfl | rfl <;> norm_num
  have hcube : ε ^ 3 = ε := by rcases hcases with rfl | rfl <;> norm_num
  constructor
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [abs_mul, habs, one_mul]
    exact thirdMoment_esseen
  constructor
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [mul_pow, hcube, integral_const_mul]
    rw [show (∫ x, x ^ 3 ∂esseenLaw.measure) = kappaE from signedThirdMoment_esseen]
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [abs_mul, habs, one_mul, mul_assoc, integral_const_mul]
    rfl

theorem signed_square_difference_bounded (R x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |(x * |x|) - (y * |y|)| ≤ 2 * R * |x - y| := by
  have he : x * |x| - y * |y| = (x - y) * |x| + y * (|x| - |y|) := by ring
  rw [he]
  have htri := abs_add_le ((x - y) * |x|) (y * (|x| - |y|))
  simp only [abs_mul, abs_abs] at htri
  have h1 := mul_le_mul_of_nonneg_left hx (abs_nonneg (x - y))
  have h2 := mul_le_mul hy (abs_abs_sub_abs_le_abs_sub x y) (abs_nonneg _)
    (le_trans (abs_nonneg x) hx)
  nlinarith only [htri, h1, h2]

theorem appendix_identification_moment_budget : 108 * Real.exp (-7 * appendixA) ≤ Real.exp (-6 * appendixA) := by
  have h := exponential_relative_sixteenth 108 (7 * appendixA) (6 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(7 * appendixA) = -7 * appendixA by ring,
    show -(6 * appendixA) = -6 * appendixA by ring] at h
  nlinarith only [h, Real.exp_pos (-6 * appendixA)]

theorem identification_moments_from_wasserstein (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (ε : ℝ) (hε : ε ∈ ({-1, 1} : Set ℝ))
    (hW : wassersteinOne P.measure (esseenLaw.measure.map (fun x => ε * x)) ≤ Real.exp (-7 * appendixA)) :
    |thirdMoment P - betaE| ≤ Real.exp (-6 * appendixA) ∧
      |signedThirdMoment P - ε * kappaE| ≤ Real.exp (-6 * appendixA) ∧
      |signedSecondMoment P - ε * signedSecondMoment esseenLaw| ≤ Real.exp (-6 * appendixA) := by
  let ν := esseenLaw.measure.map (fun x => ε * x)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hcases : ε = -1 ∨ ε = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hε
  have habs : |ε| = 1 := by rcases hcases with rfl | rfl <;> norm_num
  have hν : ∀ᵐ x ∂ν, |x| ≤ 6 := by
    apply (ae_map_iff (by fun_prop) (measurableSet_le measurable_abs measurable_const)).mpr
    filter_upwards [esseen_absolute_bound_three] with x hx
    change |ε * x| ≤ 6
    rw [abs_mul, habs, one_mul]
    linarith
  obtain ⟨hρ, hκ, hM⟩ := signed_esseen_measure_moments ε hε
  have hbudget : 108 * wassersteinOne P.measure ν ≤ Real.exp (-6 * appendixA) :=
    (mul_le_mul_of_nonneg_left hW (by norm_num : (0 : ℝ) ≤ 108)).trans appendix_identification_moment_budget
  have hr := (bounded_lipschitz_integral_transport K P.measure ν 6 108 (by norm_num) (by norm_num) hP hν
    (fun x : ℝ => |x| ^ 3) (by
      intro x y hx hy
      convert absolute_cube_difference_bounded 6 x y (by norm_num) hx hy using 1 <;> norm_num)).2.2
  have hk := (bounded_lipschitz_integral_transport K P.measure ν 6 108 (by norm_num) (by norm_num) hP hν
    (fun x : ℝ => x ^ 3) (by
      intro x y hx hy
      convert cube_difference_bounded 6 x y (by norm_num) hx hy using 1 <;> norm_num)).2.2
  have hsecond := (bounded_lipschitz_integral_transport K P.measure ν 6 108 (by norm_num) (by norm_num) hP hν
    (fun x : ℝ => x * |x|) (by
      intro x y hx hy
      have h := signed_square_difference_bounded 6 x y hx hy
      dsimp only
      nlinarith only [h, abs_nonneg (x - y)])).2.2
  change |thirdMoment P - (∫ x, |x| ^ 3 ∂(esseenLaw.measure.map (fun x => ε * x)))| ≤ _ at hr
  change |signedThirdMoment P - (∫ x, x ^ 3 ∂(esseenLaw.measure.map (fun x => ε * x)))| ≤ _ at hk
  change |signedSecondMoment P - (∫ x, x * |x| ∂(esseenLaw.measure.map (fun x => ε * x)))| ≤ _ at hsecond
  rw [hρ] at hr
  rw [hκ] at hk
  rw [hM] at hsecond
  exact ⟨hr.trans hbudget, hk.trans hbudget, hsecond.trans hbudget⟩

end BerryEsseen
