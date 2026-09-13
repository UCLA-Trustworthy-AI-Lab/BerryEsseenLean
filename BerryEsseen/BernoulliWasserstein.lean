import BerryEsseen.WassersteinBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem weighted_product_difference (w z A B d : ℝ) (hw : |w| ≤ 1) (hd : 0 ≤ d)
    (hwz : |w - z| ≤ d) (hAB : |A - B| ≤ d) (hB : |B| ≤ 3) :
    |w * A - z * B| ≤ 4 * d := by
  rw [show w * A - z * B = w * (A - B) + (w - z) * B by ring]
  have h := abs_add_le (w * (A - B)) ((w - z) * B)
  rw [abs_mul, abs_mul] at h
  have h1 := mul_le_mul hw hAB (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h2 := mul_le_mul hwz hB (abs_nonneg _) hd
  linarith

theorem bernoulli_span_le_three (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    |(Real.sqrt (p * (1 - p)))⁻¹| ≤ 3 := by
  have hslo := (effective_binomial_parameters p hp).2.1
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith
  rw [abs_of_pos (inv_pos.mpr hs), inv_eq_one_div, div_le_iff₀ hs]
  linarith

theorem bernoulli_atoms_lipschitz (p q : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hq : q ∈ Icc (2 / 5) (9 / 20)) :
    |(-p / Real.sqrt (p * (1 - p))) - (-q / Real.sqrt (q * (1 - q)))| ≤ 4 * |p - q| ∧
      |((1 - p) / Real.sqrt (p * (1 - p))) - ((1 - q) / Real.sqrt (q * (1 - q)))| ≤ 4 * |p - q| := by
  have hA := bernoulli_span_lipschitz p q hp hq
  have hB := bernoulli_span_le_three q hq
  have hp01 := (effective_binomial_parameters p hp).1
  have hpabs : |p| ≤ 1 := by rw [abs_of_pos hp01.1]; exact hp01.2.le
  have hqabs : |1 - p| ≤ 1 := by rw [abs_of_pos (sub_pos.mpr hp01.2)]; linarith [hp01.1]
  constructor
  · have h := weighted_product_difference p q _ _ |p - q| hpabs (abs_nonneg _) le_rfl hA hB
    rw [show (-p / Real.sqrt (p * (1 - p))) - (-q / Real.sqrt (q * (1 - q))) =
      -(p * (Real.sqrt (p * (1 - p)))⁻¹ - q * (Real.sqrt (q * (1 - q)))⁻¹) by ring, abs_neg]
    exact h
  · have hdiff : |(1 - p) - (1 - q)| ≤ |p - q| := by
      rw [show (1 - p) - (1 - q) = -(p - q) by ring, abs_neg]
    have h := weighted_product_difference (1 - p) (1 - q) _ _ |p - q| hqabs (abs_nonneg _) hdiff hA hB
    simpa only [div_eq_mul_inv] using h

theorem standardizedBernoulli_wasserstein (K : PublishedWassersteinDuality)
    (p q : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hq : q ∈ Icc (2 / 5) (9 / 20)) :
    wassersteinOne (standardizedBernoulliLaw p (effective_binomial_parameters p hp).1).measure
      (standardizedBernoulliLaw q (effective_binomial_parameters q hq).1).measure ≤ 7 * |p - q| := by
  let P := standardizedBernoulliLaw p (effective_binomial_parameters p hp).1
  let Q := standardizedBernoulliLaw q (effective_binomial_parameters q hq).1
  apply wassersteinOne_le_of_lipschitz K P.measure Q.measure P.first_integrable Q.first_integrable
  intro f hf
  dsimp only [P, Q]
  rw [integral_standardizedBernoulli, integral_standardizedBernoulli]
  let l := -p / Real.sqrt (p * (1 - p))
  let u := (1 - p) / Real.sqrt (p * (1 - p))
  let l' := -q / Real.sqrt (q * (1 - q))
  let u' := (1 - q) / Real.sqrt (q * (1 - q))
  have hatoms := bernoulli_atoms_lipschitz p q hp hq
  have hlo : |f l - f l'| ≤ 4 * |p - q| := (lipschitz_one_pointwise f hf _ _).trans hatoms.1
  have hup : |f u - f u'| ≤ 4 * |p - q| := (lipschitz_one_pointwise f hf _ _).trans hatoms.2
  have hgap : |f u' - f l'| ≤ 3 := by
    apply (lipschitz_one_pointwise f hf _ _).trans
    have he : u' - l' = (Real.sqrt (q * (1 - q)))⁻¹ := by dsimp only [u', l']; ring
    rw [he]
    exact bernoulli_span_le_three q hq
  have hp01 := (effective_binomial_parameters p hp).1
  have h1 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hlo) (sub_pos.mpr hp01.2).le
  have h2 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hup) hp01.1.le
  have h3 : (p - q) * (f u' - f l') ≤ 3 * |p - q| := by
    calc
      _ ≤ |(p - q) * (f u' - f l')| := le_abs_self _
      _ = |p - q| * |f u' - f l'| := abs_mul _ _
      _ ≤ 3 * |p - q| := by nlinarith [mul_le_mul_of_nonneg_left hgap (abs_nonneg (p - q))]
  change (1 - p) * f l + p * f u - ((1 - q) * f l' + q * f u') ≤ 7 * |p - q|
  nlinarith only [h1, h2, h3]

end BerryEsseen
