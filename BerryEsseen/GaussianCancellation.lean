import BerryEsseen.GaussianScale
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Uniform Gaussian cancellation, including an explicit uniform remainder. -/
noncomputable section
open Set Filter
open scoped Topology
namespace BerryEsseen

def gaussianH (s z y : ℝ) : ℝ :=
  s ^ 3 * (normalCDF ((z - y / s) / Real.sqrt (1 - 1 / s ^ 2)) - normalCDF z) +
    s ^ 2 * y * standardNormalDensity z +
    s / 2 * z * standardNormalDensity z * (y ^ 2 - 1)

def gaussianTranslationPart (s z y : ℝ) : ℝ :=
  s ^ 3 * (normalCDF (z - y / s) - normalCDF z + y / s * standardNormalDensity z +
    (y / s) ^ 2 * z * standardNormalDensity z / 2)

def gaussianScalePart (s z y : ℝ) : ℝ :=
  s ^ 3 * (normalCDF ((z - y / s) / Real.sqrt (1 - 1 / s ^ 2)) - normalCDF (z - y / s) -
    (1 / s ^ 2) * (z - y / s) * standardNormalDensity (z - y / s) / 2)

def gaussianDensityPart (s z y : ℝ) : ℝ :=
  s / 2 * ((z - y / s) * standardNormalDensity (z - y / s) - z * standardNormalDensity z)

theorem gaussianH_decomposition (s z y : ℝ) (hs : s ≠ 0) :
    gaussianH s z y = gaussianTranslationPart s z y + gaussianScalePart s z y +
      gaussianDensityPart s z y := by
  unfold gaussianH gaussianTranslationPart gaussianScalePart gaussianDensityPart
  field_simp <;> ring

theorem gaussianTranslationPart_bound (s z y : ℝ) (hs : 0 < s) :
    |gaussianTranslationPart s z y| ≤ phi0 / 6 * |y| ^ 3 := by
  have hb := mul_le_mul_of_nonneg_left (gaussian_translation_bound z (-y / s))
    (pow_nonneg hs.le 3)
  rw [gaussianTranslationPart, abs_mul, abs_of_pos (pow_pos hs 3)]
  convert hb using 1
  · congr 2 <;> ring_nf
  · rw [abs_div, abs_neg, abs_of_pos hs]
    field_simp <;> ring

theorem gaussianScalePart_bound (s z y : ℝ) (hs : 0 < s) (hs2 : 2 ≤ s ^ 2) :
    |gaussianScalePart s z y| ≤ 9 * phi0 / s := by
  have hd : (1 / s ^ 2 : ℝ) ∈ Icc 0 (1 / 2) :=
    ⟨by positivity, (div_le_iff₀ (sq_pos_of_pos hs)).2 (by linarith)⟩
  have hb := mul_le_mul_of_nonneg_left (gaussian_scale_remainder (z - y / s) (1 / s ^ 2) hd)
    (pow_nonneg hs.le 3)
  rw [gaussianScalePart, abs_mul, abs_of_pos (pow_pos hs 3)]
  convert hb using 1
  field_simp <;> ring

theorem gaussianDensityPart_bound (s z y : ℝ) (hs : 0 < s) :
    |gaussianDensityPart s z y| ≤ phi0 / 2 * |y| := by
  have hb := mul_le_mul_of_nonneg_left (gaussian_x_density_lipschitz z (z - y / s))
    (by positivity : 0 ≤ s / 2)
  rw [gaussianDensityPart, abs_mul, abs_of_pos (by positivity : 0 < s / 2)]
  convert hb using 1
  rw [show z - y / s - z = -y / s by ring, abs_div, abs_neg, abs_of_pos hs]
  field_simp <;> ring

/-- The global estimate, with an explicit constant A = 9 phi(0). -/
theorem gaussianH_global_bound (s z y : ℝ) (hs : 1 ≤ s) (hs2 : 2 ≤ s ^ 2) :
    |gaussianH s z y| ≤ phi0 / 6 * |y| ^ 3 + 9 * phi0 * (1 + |y|) := by
  have hsp : 0 < s := by linarith
  rw [gaussianH_decomposition s z y hsp.ne']
  have hb := (abs_add_three (gaussianTranslationPart s z y) (gaussianScalePart s z y)
    (gaussianDensityPart s z y)).trans
    (add_le_add (add_le_add (gaussianTranslationPart_bound s z y hsp)
      (gaussianScalePart_bound s z y hsp hs2)) (gaussianDensityPart_bound s z y hsp))
  have hc : 9 * phi0 / s ≤ 9 * phi0 :=
    (div_le_iff₀ hsp).2 (by nlinarith [phi0_pos])
  have hp := mul_nonneg phi0_pos.le (abs_nonneg y)
  linarith

theorem gaussianTranslationPart_remainder (s z y : ℝ) (hs : 0 < s) :
    |gaussianTranslationPart s z y + y ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6| ≤
      (3 / 4 : ℝ) * phi0 * |y| ^ 4 / s := by
  have hb := mul_le_mul_of_nonneg_left (gaussian_translation_fourth_bound z (-y / s))
    (pow_nonneg hs.le 3)
  rw [← abs_of_pos (pow_pos hs 3), ← abs_mul] at hb
  convert hb using 1
  · congr 1
    unfold gaussianTranslationPart
    rw [show z + -y / s = z - y / s by ring]
    field_simp <;> ring
  · rw [abs_div, abs_neg, abs_of_pos hs, abs_of_pos (pow_pos hs 3)]
    field_simp <;> ring

theorem gaussianDensityPart_remainder (s z y : ℝ) (hs : 0 < s) :
    |gaussianDensityPart s z y - y * (z ^ 2 - 1) * standardNormalDensity z / 2| ≤
      (9 / 2 : ℝ) * phi0 * |y| ^ 2 / s := by
  have hb := mul_le_mul_of_nonneg_left (gaussian_x_density_translation_bound z (-y / s))
    (by positivity : 0 ≤ s / 2)
  rw [← abs_of_pos (by positivity : 0 < s / 2), ← abs_mul] at hb
  convert hb using 1
  · congr 1
    unfold gaussianDensityPart
    rw [show z + -y / s = z - y / s by ring]
    field_simp <;> ring
  · simp only [abs_div, abs_neg, abs_of_pos hs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    field_simp <;> ring

/-- The remainder estimate is uniform in the unrestricted normal argument z. -/
theorem gaussianH_remainder (s z y : ℝ) (hs : 0 < s) (hs2 : 2 ≤ s ^ 2) :
    |gaussianH s z y - (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6)| ≤
      phi0 * ((3 / 4 : ℝ) * |y| ^ 4 + (9 / 2 : ℝ) * |y| ^ 2 + 9) / s := by
  have he : gaussianH s z y - (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6) =
      (gaussianTranslationPart s z y + y ^ 3 * (z ^ 2 - 1) * standardNormalDensity z / 6) +
      gaussianScalePart s z y +
      (gaussianDensityPart s z y - y * (z ^ 2 - 1) * standardNormalDensity z / 2) := by
    rw [gaussianH_decomposition s z y hs.ne']
    ring
  rw [he]
  have hb := (abs_add_three _ _ _).trans (add_le_add
    (add_le_add (gaussianTranslationPart_remainder s z y hs) (gaussianScalePart_bound s z y hs hs2))
    (gaussianDensityPart_remainder s z y hs))
  convert hb using 1
  ring

def gaussianRemainderConstant (L : ℝ) : ℝ := phi0 * ((3 / 4 : ℝ) * L ^ 4 + (9 / 2 : ℝ) * L ^ 2 + 9)

theorem gaussianH_uniform_remainder (s z y L : ℝ) (hs : 0 < s) (hs2 : 2 ≤ s ^ 2)
    (hy : |y| ≤ L) :
    |gaussianH s z y - (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6)| ≤
      gaussianRemainderConstant L / s := by
  apply (gaussianH_remainder s z y hs hs2).trans
  unfold gaussianRemainderConstant
  have hp := phi0_pos.le
  gcongr

def gaussianHn (n : ℕ) (z y : ℝ) : ℝ := gaussianH (Real.sqrt (n : ℝ)) z y

theorem gaussianHn_global_bound (n : ℕ) (hn : 2 ≤ n) (z y : ℝ) :
    |gaussianHn n z y| ≤ phi0 / 6 * |y| ^ 3 + 9 * phi0 * (1 + |y|) := by
  apply gaussianH_global_bound
  · exact Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ n by omega))
  · rw [Real.sq_sqrt (by positivity)]
    exact_mod_cast hn

theorem gaussianHn_uniform_remainder (n : ℕ) (hn : 2 ≤ n) (z y L : ℝ) (hy : |y| ≤ L) :
    |gaussianHn n z y - (z ^ 2 - 1) * standardNormalDensity z * (y / 2 - y ^ 3 / 6)| ≤
      gaussianRemainderConstant L / Real.sqrt (n : ℝ) := by
  apply gaussianH_uniform_remainder _ _ _ _ _ _ hy
  · exact Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  · rw [Real.sq_sqrt (by positivity)]
    exact_mod_cast hn

theorem gaussian_limit_polynomial_bound (y L : ℝ) (hy : |y| ≤ L) :
    |y / 2 - y ^ 3 / 6| ≤ L / 2 + L ^ 3 / 6 := by
  calc
    |y / 2 - y ^ 3 / 6| ≤ |y / 2| + |y ^ 3 / 6| := abs_sub _ _
    _ = |y| / 2 + |y| ^ 3 / 6 := by rw [abs_div, abs_div, abs_pow]; norm_num
    _ ≤ _ := by gcongr

/-- The compact uniform convergence conclusion in `lem:gaussian-expansion`. -/
theorem gaussianHn_uniform_limit (n : ℕ → ℕ) (z : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hz : Tendsto z atTop (𝓝 0)) (L : ℝ) :
    TendstoUniformlyOn (fun j y => gaussianHn (n j) (z j) y)
      (fun y => phi0 / 6 * (y ^ 3 - 3 * y)) atTop (Icc (-L) L) := by
  have hc : Continuous (fun x : ℝ => (x ^ 2 - 1) * standardNormalDensity x) :=
    ((continuous_id.pow 2).sub continuous_const).mul standardNormalDensity_continuous
  have hcoef : Tendsto (fun j => |((z j) ^ 2 - 1) * standardNormalDensity (z j) + phi0|)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub, neg_one_mul,
      standardNormalDensity_zero, neg_add_cancel, abs_zero] using
      (((hc.tendsto 0).comp hz).add_const phi0).abs
  have hden : Tendsto (fun j => Real.sqrt (n j : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have herr : Tendsto (fun j => gaussianRemainderConstant L / Real.sqrt (n j : ℝ) +
      |((z j) ^ 2 - 1) * standardNormalDensity (z j) + phi0| * (L / 2 + L ^ 3 / 6))
      atTop (𝓝 0) := by
    simpa using (hden.const_div_atTop (gaussianRemainderConstant L)).add
      (hcoef.mul_const (L / 2 + L ^ 3 / 6))
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  filter_upwards [hn.eventually (eventually_ge_atTop 2), herr.eventually (eventually_lt_nhds hε)]
    with j hnj hj y hy
  have habs : |y| ≤ L := abs_le.2 hy
  have hp := gaussian_limit_polynomial_bound y L habs
  have hr := gaussianHn_uniform_remainder (n j) hnj (z j) y L habs
  have he : gaussianHn (n j) (z j) y - phi0 / 6 * (y ^ 3 - 3 * y) =
      (gaussianHn (n j) (z j) y - ((z j) ^ 2 - 1) * standardNormalDensity (z j) *
        (y / 2 - y ^ 3 / 6)) +
      (((z j) ^ 2 - 1) * standardNormalDensity (z j) + phi0) * (y / 2 - y ^ 3 / 6) := by ring
  have hb₂ : |(((z j) ^ 2 - 1) * standardNormalDensity (z j) + phi0) * (y / 2 - y ^ 3 / 6)| ≤
      |((z j) ^ 2 - 1) * standardNormalDensity (z j) + phi0| * (L / 2 + L ^ 3 / 6) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have hb := (abs_add_le _ _).trans (add_le_add hr hb₂)
  rw [← he] at hb
  simpa only [Real.dist_eq, abs_sub_comm] using hb.trans_lt hj

end BerryEsseen
