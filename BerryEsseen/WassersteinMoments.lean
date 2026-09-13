import BerryEsseen.WassersteinBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem wassersteinOne_nonneg (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    0 ≤ wassersteinOne μ ν := by
  have h := lipschitz_integral_le_wassersteinOne K μ ν hμ hν (fun _ => 0)
    (LipschitzWith.of_dist_le_mul (by simp))
  simpa using h

theorem lipschitz_integral_abs_le_wassersteinOne (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ wassersteinOne μ ν := by
  have hp := lipschitz_integral_le_wassersteinOne K μ ν hμ hν f hf
  have hn := lipschitz_integral_le_wassersteinOne K μ ν hμ hν (fun x => -f x) hf.neg
  simp only [integral_neg] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

def intervalClip (R x : ℝ) : ℝ := max (-R) (min R x)

theorem intervalClip_bounds (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : |intervalClip R x| ≤ R := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem intervalClip_eq (R x : ℝ) (hx : |x| ≤ R) : intervalClip R x = x := by
  rw [intervalClip, min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

theorem intervalClip_lipschitz (R : ℝ) : LipschitzWith 1 (intervalClip R) :=
  (LipschitzWith.id.const_min R).const_max (-R)

theorem bounded_lipschitz_integral_transport (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 < L)
    (hμ : ∀ᵐ x ∂μ, |x| ≤ R) (hν : ∀ᵐ x ∂ν, |x| ≤ R)
    (f : ℝ → ℝ) (hf : ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |f x - f y| ≤ L * |x - y|) :
    Integrable f μ ∧ Integrable f ν ∧
      |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤ L * wassersteinOne μ ν := by
  let g : ℝ → ℝ := fun x => f (intervalClip R x) / L
  have hg : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    change |f (intervalClip R x) / L - f (intervalClip R y) / L| ≤ |x - y|
    rw [← sub_div, abs_div, abs_of_pos hL]
    apply (div_le_iff₀ hL).mpr
    have h1 := hf (intervalClip R x) (intervalClip R y)
      (intervalClip_bounds R hR x) (intervalClip_bounds R hR y)
    have h2 := mul_le_mul_of_nonneg_left
      (lipschitz_one_pointwise _ (intervalClip_lipschitz R) x y) hL.le
    linarith
  have hiμ := real_function_integrable_of_abs_le μ (fun x : ℝ => x) R measurable_id hμ
  have hiν := real_function_integrable_of_abs_le ν (fun x : ℝ => x) R measurable_id hν
  have hgμ := lipschitz_one_integrable μ hiμ g hg
  have hgν := lipschitz_one_integrable ν hiν g hg
  have hfgμ : f =ᵐ[μ] fun x => L * g x := by
    filter_upwards [hμ] with x hx
    dsimp [g]
    rw [intervalClip_eq R x hx]
    field_simp
  have hfgν : f =ᵐ[ν] fun x => L * g x := by
    filter_upwards [hν] with x hx
    dsimp [g]
    rw [intervalClip_eq R x hx]
    field_simp
  refine ⟨(hgμ.const_mul L).congr hfgμ.symm, (hgν.const_mul L).congr hfgν.symm, ?_⟩
  rw [integral_congr_ae hfgμ, integral_congr_ae hfgν, integral_const_mul, integral_const_mul,
    ← mul_sub, abs_mul, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left (lipschitz_integral_abs_le_wassersteinOne K μ ν hiμ hiν g hg) hL.le

theorem cube_difference_bounded (R x y : ℝ) (hR : 0 ≤ R) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 3 - y ^ 3| ≤ 3 * R ^ 2 * |x - y| := by
  have hxx : |x| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hyy : |y| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hxy : |x| * |y| ≤ R ^ 2 := by nlinarith only [mul_le_mul hx hy (abs_nonneg y) hR]
  have hfactor : |x ^ 2 + x * y + y ^ 2| ≤ 3 * R ^ 2 := by
    calc
      _ ≤ |x ^ 2 + x * y| + |y ^ 2| := abs_add_le _ _
      _ ≤ |x ^ 2| + |x * y| + |y ^ 2| := by linarith [abs_add_le (x ^ 2) (x * y)]
      _ ≤ _ := by rw [abs_pow, abs_pow, abs_mul]; linarith
  rw [show x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) by ring, abs_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hfactor (abs_nonneg (x - y))]

theorem absolute_cube_difference_bounded (R x y : ℝ) (hR : 0 ≤ R) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |(|x| ^ 3) - |y| ^ 3| ≤ 3 * R ^ 2 * |x - y| := by
  have h := cube_difference_bounded R |x| |y| hR (by simpa using hx) (by simpa using hy)
  exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (by positivity))

theorem square_difference_bounded (R x y : ℝ) (hR : 0 ≤ R) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 2 - y ^ 2| ≤ 2 * R * |x - y| := by
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
  have h : |x + y| ≤ 2 * R := (abs_add_le x y).trans (by linarith)
  nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg (x - y))]

end BerryEsseen
