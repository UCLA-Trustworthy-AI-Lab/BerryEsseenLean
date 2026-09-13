import BerryEsseen.WassersteinMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem bounded_complex_lipschitz_integral_transport (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 < L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ x ∂ν, |x| ≤ R)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hLip : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → ‖f x - f y‖ ≤ L * |x - y|) :
    Integrable f μ ∧ Integrable f ν ∧
      ‖(∫ x, f x ∂μ) - (∫ x, f x ∂ν)‖ ≤ L * wassersteinOne μ ν := by
  have hib (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hρ : ∀ᵐ x ∂ρ, |x| ≤ R) : Integrable f ρ := by
    apply (integrable_const (L * R + ‖f 0‖)).mono' hf.aestronglyMeasurable
    filter_upwards [hρ] with x hx
    have hp := hLip x 0 hx (by simpa using hR)
    rw [sub_zero] at hp
    have ht := norm_sub_norm_le (f x) (f 0)
    have hm := mul_le_mul_of_nonneg_left hx hL.le
    linarith only [hp, ht, hm]
  have hiμ := hib μ hμ
  have hiν := hib ν hν
  refine ⟨hiμ, hiν, ?_⟩
  let z := (∫ x, f x ∂μ) - (∫ x, f x ∂ν)
  by_cases hz : ‖z‖ = 0
  · change ‖z‖ ≤ _
    rw [hz]
    have h1 := real_function_integrable_of_abs_le μ (fun x : ℝ => x) R measurable_id hμ
    have h2 := real_function_integrable_of_abs_le ν (fun x : ℝ => x) R measurable_id hν
    exact mul_nonneg hL.le (wassersteinOne_nonneg K μ ν h1 h2)
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    let g : ℝ → ℝ := fun x => (conj z * f x).re
    have hg : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |g x - g y| ≤ (‖z‖ * L) * |x - y| := by
      intro x y hx hy
      change |(conj z * f x).re - (conj z * f y).re| ≤ (‖z‖ * L) * |x - y|
      rw [← Complex.sub_re, ← mul_sub]
      have hb := Complex.abs_re_le_norm (conj z * (f x - f y))
      rw [norm_mul, Complex.norm_conj] at hb
      have hm := mul_le_mul_of_nonneg_left (hLip x y hx hy) (norm_nonneg z)
      nlinarith only [hb, hm]
    have h := (bounded_lipschitz_integral_transport K μ ν R (‖z‖ * L) hR
      (mul_pos hzpos hL) hμ hν g hg).2.2
    have he : (∫ x, g x ∂μ) - (∫ x, g x ∂ν) = ‖z‖ ^ 2 := by
      dsimp only [g]
      have hrμ : (∫ x, (conj z * f x).re ∂μ) = (∫ x, conj z * f x ∂μ).re := integral_re (hiμ.const_mul (conj z))
      have hrν : (∫ x, (conj z * f x).re ∂ν) = (∫ x, conj z * f x ∂ν).re := integral_re (hiν.const_mul (conj z))
      rw [hrμ, hrν,
        integral_const_mul, integral_const_mul, ← Complex.sub_re, ← mul_sub]
      change (conj z * z).re = ‖z‖ ^ 2
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [he, abs_of_nonneg (sq_nonneg _)] at h
    change ‖z‖ ≤ _
    apply le_of_mul_le_mul_left (a := ‖z‖) _ hzpos
    nlinarith only [h]

end BerryEsseen
