import BerryEsseen.TaylorBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The three scalar second-order Taylor remainders used after conditioning
on the two Bernoulli labels in the original cluster-jitter proof. -/
noncomputable section
open Set
namespace BerryEsseen

theorem manuscript_taylor_second_on_affine (f f₁ f₂ : ℝ → ℝ) (C a d : ℝ)
    (h₁ : ∀ x, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hC : ∀ t ∈ Icc 0 1, |f₂ (a + d * t)| ≤ C) :
    |f (a + d) - f a - d * f₁ a| ≤ C * d ^ 2 / 2 := by
  have hd₁ (t : ℝ) : HasDerivAt (fun v => f (a + d * v))
      (d * f₁ (a + d * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f _ a d t 0 (h₁ _)
  have hd₂ (t : ℝ) : HasDerivAt (fun v => d * f₁ (a + d * v))
      (d ^ 2 * f₂ (a + d * t)) t := by
    simpa using hasDerivAt_scaled_affine_comp f₁ _ a d t 1 (h₂ _)
  have hb (t : ℝ) (ht : t ∈ Icc 0 1) :
      |d ^ 2 * f₂ (a + d * t)| ≤ d ^ 2 * C := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
    exact mul_le_mul_of_nonneg_left (hC t ht) (sq_nonneg d)
  have hh := taylor_second_abs _ _ _ (d ^ 2 * C)
    (fun t _ => hd₁ t) (fun t _ => hd₂ t) hb
  convert hh using 1 <;> (try simp only [mul_one, mul_zero, add_zero]) <;> ring

theorem manuscript_cluster_affine_bound (a d ε t : ℝ)
    (hε : 0 ≤ ε) (ha : |a| ≤ 1) (hd : |d| ≤ 2 * ε) (ht : t ∈ Icc 0 1) :
    |a + d * t| ≤ 1 + 2 * ε := by
  calc
    |a + d * t| ≤ |a| + |d * t| := abs_add_le _ _
    _ = |a| + |d| * t := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ 1 + (2 * ε) * 1 := add_le_add ha (mul_le_mul hd ht.2 ht.1 (by positivity))
    _ = _ := by ring

def manuscriptClusterCos (u x : ℝ) : ℝ := Real.cos (u * x)
def manuscriptClusterSinWeight (u x : ℝ) : ℝ := -x * Real.sin (u * x)
def manuscriptClusterCosSquareWeight (u x : ℝ) : ℝ := -(x ^ 2) * Real.cos (u * x)

theorem manuscript_cluster_cos_deriv (u x : ℝ) :
    HasDerivAt (manuscriptClusterCos u) (-u * Real.sin (u * x)) x := by
  convert ((hasDerivAt_id x).const_mul u).cos using 1 <;> dsimp [manuscriptClusterCos] <;> ring

theorem manuscript_cluster_cos_deriv_two (u x : ℝ) :
    HasDerivAt (fun y => -u * Real.sin (u * y)) (-(u ^ 2) * Real.cos (u * x)) x := by
  convert (((hasDerivAt_id x).const_mul u).sin).const_mul (-u) using 1 <;> dsimp <;> ring

theorem manuscript_cluster_sinWeight_deriv (u x : ℝ) :
    HasDerivAt (manuscriptClusterSinWeight u)
      (-Real.sin (u * x) - x * u * Real.cos (u * x)) x := by
  convert (hasDerivAt_id x).neg.mul (((hasDerivAt_id x).const_mul u).sin) using 1 <;>
    dsimp [manuscriptClusterSinWeight] <;> ring

theorem manuscript_cluster_sinWeight_deriv_two (u x : ℝ) :
    HasDerivAt (fun y => -Real.sin (u * y) - y * u * Real.cos (u * y))
      (-2 * u * Real.cos (u * x) + x * u ^ 2 * Real.sin (u * x)) x := by
  convert (((hasDerivAt_id x).const_mul u).sin).neg.sub
    (((hasDerivAt_id x).mul_const u).mul (((hasDerivAt_id x).const_mul u).cos)) using 1 <;>
    dsimp <;> ring

theorem manuscript_cluster_cosSquareWeight_deriv (u x : ℝ) :
    HasDerivAt (manuscriptClusterCosSquareWeight u)
      (-2 * x * Real.cos (u * x) + x ^ 2 * u * Real.sin (u * x)) x := by
  convert ((hasDerivAt_id x).pow 2).neg.mul (((hasDerivAt_id x).const_mul u).cos) using 1 <;>
    dsimp [manuscriptClusterCosSquareWeight] <;> ring

theorem manuscript_cluster_cosSquareWeight_deriv_two (u x : ℝ) :
    HasDerivAt (fun y => -2 * y * Real.cos (u * y) + y ^ 2 * u * Real.sin (u * y))
      (-2 * Real.cos (u * x) + 4 * x * u * Real.sin (u * x) +
        x ^ 2 * u ^ 2 * Real.cos (u * x)) x := by
  convert (((hasDerivAt_id x).const_mul (-2)).mul (((hasDerivAt_id x).const_mul u).cos)).add
    ((((hasDerivAt_id x).pow 2).mul_const u).mul (((hasDerivAt_id x).const_mul u).sin)) using 1 <;>
    dsimp <;> ring

theorem manuscript_cluster_cos_second_bound (u x : ℝ) :
    |-(u ^ 2) * Real.cos (u * x)| ≤ u ^ 2 := by
  rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg u)]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (u * x)) (sq_nonneg u)

theorem manuscript_cluster_sinWeight_second_bound (u x M : ℝ) (hx : |x| ≤ M) :
    |-2 * u * Real.cos (u * x) + x * u ^ 2 * Real.sin (u * x)| ≤
      2 * |u| + M * u ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have h1 : |-2 * u * Real.cos (u * x)| ≤ 2 * |u| := by
    rw [abs_mul, abs_mul]
    norm_num
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (u * x)) (by positivity : 0 ≤ 2 * |u|)
  have h2 : |x * u ^ 2 * Real.sin (u * x)| ≤ M * u ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg u)]
    calc
      |x| * u ^ 2 * |Real.sin (u * x)| ≤ M * u ^ 2 * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = _ := mul_one _
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem manuscript_cluster_cosSquareWeight_second_bound (u x M : ℝ) (hx : |x| ≤ M) :
    |-2 * Real.cos (u * x) + 4 * x * u * Real.sin (u * x) +
        x ^ 2 * u ^ 2 * Real.cos (u * x)| ≤ 2 + 4 * M * |u| + M ^ 2 * u ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg x).trans hx
  have h1 : |-2 * Real.cos (u * x)| ≤ 2 := by
    rw [abs_mul]
    norm_num
    linarith only [Real.abs_cos_le_one (u * x)]
  have h2 : |4 * x * u * Real.sin (u * x)| ≤ 4 * M * |u| := by
    simp only [abs_mul, show |(4 : ℝ)| = 4 by norm_num]
    calc
      4 * |x| * |u| * |Real.sin (u * x)| ≤ 4 * M * |u| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = _ := mul_one _
  have h3 : |x ^ 2 * u ^ 2 * Real.cos (u * x)| ≤ M ^ 2 * u ^ 2 := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (sq_nonneg u)]
    calc
      |x| ^ 2 * u ^ 2 * |Real.cos (u * x)| ≤ M ^ 2 * u ^ 2 * 1 := by gcongr; exact Real.abs_cos_le_one _
      _ = _ := mul_one _
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)

theorem manuscript_cluster_cos_taylor (u a d : ℝ) :
    |manuscriptClusterCos u (a + d) - manuscriptClusterCos u a -
      d * (-u * Real.sin (u * a))| ≤ u ^ 2 * d ^ 2 / 2 :=
  manuscript_taylor_second_on_affine _ _ _ _ a d
    (manuscript_cluster_cos_deriv u) (manuscript_cluster_cos_deriv_two u)
    (fun _ _ => manuscript_cluster_cos_second_bound _ _)

theorem manuscript_cluster_sinWeight_taylor (u a d ε : ℝ)
    (hε : 0 ≤ ε) (ha : |a| ≤ 1) (hd : |d| ≤ 2 * ε) :
    |manuscriptClusterSinWeight u (a + d) - manuscriptClusterSinWeight u a -
      d * (-Real.sin (u * a) - a * u * Real.cos (u * a))| ≤
        (2 * |u| + (1 + 2 * ε) * u ^ 2) * d ^ 2 / 2 :=
  manuscript_taylor_second_on_affine _ _ _ _ a d
    (manuscript_cluster_sinWeight_deriv u) (manuscript_cluster_sinWeight_deriv_two u)
    (fun t ht => manuscript_cluster_sinWeight_second_bound _ _ _
      (manuscript_cluster_affine_bound a d ε t hε ha hd ht))

theorem manuscript_cluster_cosSquareWeight_taylor (u a d ε : ℝ)
    (hε : 0 ≤ ε) (ha : |a| ≤ 1) (hd : |d| ≤ 2 * ε) :
    |manuscriptClusterCosSquareWeight u (a + d) - manuscriptClusterCosSquareWeight u a -
      d * (-2 * a * Real.cos (u * a) + a ^ 2 * u * Real.sin (u * a))| ≤
        (2 + 4 * (1 + 2 * ε) * |u| + (1 + 2 * ε) ^ 2 * u ^ 2) * d ^ 2 / 2 :=
  manuscript_taylor_second_on_affine _ _ _ _ a d
    (manuscript_cluster_cosSquareWeight_deriv u) (manuscript_cluster_cosSquareWeight_deriv_two u)
    (fun t ht => manuscript_cluster_cosSquareWeight_second_bound _ _ _
      (manuscript_cluster_affine_bound a d ε t hε ha hd ht))

end BerryEsseen
