import BerryEsseen.EffectiveCentralDerivative
import BerryEsseen.ManuscriptBinomialTheorem

/-! The appendix's relative-density proof. The accumulated-variance hypothesis
is retained: the argument and logarithmic density errors are O(1 / sqrt n). -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_small_variance_scale_ratio (p s : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12)) :
    Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) ∈ Icc (1 - 3 * s) 1 ∧
    Real.sqrt (p * (1 - p) / (p * (1 - p) + s)) =
      Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) := by
  let a := Real.sqrt (p * (1 - p))
  let b := Real.sqrt (p * (1 - p) + s)
  have hb := effective_small_variance_scale p s hp hs
  have ha : (0.48 : ℝ) ≤ a := (effective_binomial_parameters p hp).2.1
  have hb0 : 0 < b := by have h := hb.1.1; change (0.48 : ℝ) ≤ b at h; linarith
  have hd : 0 ≤ b - a := hb.2.1.1
  have hv : 0 ≤ p * (1 - p) := by
    have h := (effective_binomial_parameters p hp).1
    exact mul_nonneg h.1.le (sub_nonneg.mpr h.2.le)
  have he : (b - a) * (b + a) = s := by
    have h1 := Real.sq_sqrt hv
    have h2 := Real.sq_sqrt (show 0 ≤ p * (1 - p) + s by linarith [hs.1])
    change a ^ 2 = _ at h1
    change b ^ 2 = _ at h2
    nlinarith only [h1, h2]
  have hprod : 1 ≤ 3 * b * (b + a) := by
    have hb48 : (0.48 : ℝ) ≤ b := hb.1.1
    have hm := mul_le_mul hb48 (show (0.96 : ℝ) ≤ b + a by linarith)
      (by norm_num : (0 : ℝ) ≤ 0.96) hb0.le
    nlinarith only [hm]
  have hmul := mul_le_mul_of_nonneg_right hprod hd
  have hid : 3 * b * (b + a) * (b - a) = 3 * s * b := by
    calc
      _ = 3 * b * ((b - a) * (b + a)) := by ring
      _ = _ := by rw [he]; ring
  rw [hid, one_mul] at hmul
  have hdiff : b - a ≤ 3 * s * b := hmul
  refine ⟨⟨(le_div_iff₀ hb0).mpr (by nlinarith only [hdiff]),
    (div_le_one hb0).mpr (by linarith only [hd])⟩, ?_⟩
  exact Real.sqrt_div hv _

theorem manuscript_central_gaussian_argument (p s : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hns : (n : ℝ) * s ≤ 1 / (10 : ℝ) ^ 12)
    (hz : |binomialZ p n k| ≤ 5) (u : ℝ) (hu : |u| ≤ 3 / 5) :
    |(((k : ℝ) - n * p + u) / (Real.sqrt (n : ℝ) * Real.sqrt (p * (1 - p) + s))) -
      binomialZ p n k| ≤ 3 / Real.sqrt (n : ℝ) := by
  let r := Real.sqrt (n : ℝ)
  let a := Real.sqrt (p * (1 - p))
  let b := Real.sqrt (p * (1 - p) + s)
  let z := binomialZ p n k
  have hp01 := (effective_binomial_parameters p hp).1
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hb48 : (0.48 : ℝ) ≤ b := (effective_small_variance_scale p s hp hs).1.1
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := Real.sqrt_pos.mpr (mul_pos hp01.1 (sub_pos.mpr hp01.2))
  have hrat := (manuscript_small_variance_scale_ratio p s hp hs).1
  change a / b ∈ Icc (1 - 3 * s) 1 at hrat
  have hratabs : |a / b - 1| ≤ 3 * s := by
    rw [abs_of_nonpos (by linarith [hrat.2])]
    linarith [hrat.1]
  have ht : r * a * z = (k : ℝ) - n * p := by
    rw [show r * a * z = a * (r * z) by ring, binomialZ_scaling p hp01 n (by omega) k]
    exact mul_div_cancel₀ _ ha0.ne'
  have he : ((k : ℝ) - n * p + u) / (r * b) - z = z * (a / b - 1) + u / (r * b) := by
    rw [← ht]
    field_simp
    <;> ring
  have harg : |((k : ℝ) - n * p + u) / (r * b) - z| ≤ 15 * s + 2 / r := by
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_div, abs_of_pos (mul_pos hr hb0)]
    have hm := mul_le_mul hz hratabs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
    have ht : |u| / (r * b) ≤ 2 / r := by
      apply (div_le_iff₀ (mul_pos hr hb0)).mpr
      rw [show 2 / r * (r * b) = 2 * b by field_simp]
      linarith only [hu, hb48]
    linarith only [hm, ht]
  have hrs : r * s ≤ 1 / (10 : ℝ) ^ 12 := by
    have hrr : r ≤ r ^ 2 := by nlinarith only [hr1]
    have hm := mul_le_mul_of_nonneg_right hrr hs.1
    rw [hr2] at hm
    exact hm.trans hns
  have hsmall : 15 * s ≤ 1 / r := (le_div_iff₀ hr).mpr (by nlinarith only [hrs])
  change _ ≤ 3 / r
  apply harg.trans
  simp only [div_eq_mul_inv] at hsmall ⊢
  linarith only [hsmall]

theorem manuscript_gaussian_density_ratio_log (w z : ℝ) :
    Real.log (standardNormalDensity w / standardNormalDensity z) = -(w ^ 2 - z ^ 2) / 2 := by
  have he : standardNormalDensity w / standardNormalDensity z = Real.exp (-(w ^ 2 - z ^ 2) / 2) := by
    rw [standardNormalDensity_formula, standardNormalDensity_formula,
      mul_div_mul_left _ _ phi0_pos.ne', ← Real.exp_sub]
    congr 1
    ring
  rw [he, Real.log_exp]

theorem manuscript_central_density_log_bound (r w z : ℝ) (hr : 1 ≤ r)
    (hz : |z| ≤ 5) (hd : |w - z| ≤ 3 / r) :
    |Real.log (standardNormalDensity w / standardNormalDensity z)| ≤ 20 / r := by
  have hr0 : 0 < r := by linarith
  have hi : 3 / r ≤ 3 := (div_le_iff₀ hr0).mpr (by linarith)
  have hw : |w| ≤ 8 := by
    have h := abs_add_le (w - z) z
    rw [sub_add_cancel] at h
    linarith only [h, hd, hi, hz]
  have hsum : |w + z| ≤ 13 := (abs_add_le _ _).trans (by linarith only [hw, hz])
  rw [manuscript_gaussian_density_ratio_log, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    show w ^ 2 - z ^ 2 = (w - z) * (w + z) by ring, abs_mul]
  have hm := mul_le_mul hd hsum (abs_nonneg _) (div_nonneg (by norm_num) hr0.le)
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm, hinv]

theorem manuscript_density_ratio_of_log_bound (r w z : ℝ) (hr : (10 : ℝ) ^ 50 ≤ r)
    (hlog : |Real.log (standardNormalDensity w / standardNormalDensity z)| ≤ 20 / r) :
    standardNormalDensity w / standardNormalDensity z ∈ Icc 0.999 1.001 := by
  have hr0 : 0 < r := by positivity
  have hsmall : 20 / r ≤ 1 / 2000 := (div_le_iff₀ hr0).mpr (by norm_num at hr ⊢; linarith)
  have he := Real.abs_exp_sub_one_le (hlog.trans (hsmall.trans (by norm_num)))
  rw [Real.exp_log (div_pos (standardNormalDensity_pos w) (standardNormalDensity_pos z))] at he
  have h := abs_le.mp (he.trans (mul_le_mul_of_nonneg_left (hlog.trans hsmall) (by norm_num : (0 : ℝ) ≤ 2)))
  constructor <;> linarith [h.1, h.2]

theorem manuscript_effective_central_gaussian_derivative_ratio
    (p s : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hns : (n : ℝ) * s ≤ 1 / (10 : ℝ) ^ 12)
    (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    0 < binomialWeight p n k ∧ ∀ u : ℝ, |u| ≤ 3 / 5 →
      (0.98 : ℝ) ≤ deriv (clusterGaussianIncrement p n k s) u ∧ deriv (clusterGaussianIncrement p n k s) u ≤ 1.02 := by
  let r := Real.sqrt (n : ℝ)
  let a := Real.sqrt (p * (1 - p))
  let b := Real.sqrt (p * (1 - p) + s)
  let z := binomialZ p n k
  let q := r * a * binomialWeight p n k / standardNormalDensity z
  have hp01 := (effective_binomial_parameters p hp).1
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hp01.1 (sub_pos.mpr hp01.2))
  have hb : 0 < b := Real.sqrt_pos.mpr (by have hv := mul_pos hp01.1 (sub_pos.mpr hp01.2); linarith [hs.1])
  have hφ : 0 < standardNormalDensity z := standardNormalDensity_pos z
  have hmass := manuscript_effective_binomial_central p hp n hn k hk hz
  rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n)] at hmass
  have hq : q ∈ Icc 0.99 1.01 := ⟨hmass.1, hmass.2.1⟩
  have hq0 : 0 < q := by linarith [hq.1]
  have hw : 0 < binomialWeight p n k := by
    have hprod := (div_pos_iff_of_pos_right hφ).mp hq0
    exact (mul_pos_iff_of_pos_left (mul_pos hr ha)).mp hprod
  refine ⟨hw, ?_⟩
  intro u hu
  let w := ((k : ℝ) - n * p + u) / (r * b)
  have harg := manuscript_central_gaussian_argument p s hp hs n k hn hns hz u hu
  have hlog := manuscript_central_density_log_bound r w z hr1 hz harg
  have hratio := manuscript_density_ratio_of_log_bound r w z (effective_binomial_root_lower n hn) hlog
  have hscale := (manuscript_small_variance_scale_ratio p s hp hs).1
  have hscale' : a / b ∈ Icc 0.999 1 := ⟨by linarith [hscale.1, hs.2], hscale.2⟩
  have hprod := mul_le_mul hratio.1 hscale'.1 (by norm_num : (0 : ℝ) ≤ 0.999)
    (div_pos (standardNormalDensity_pos w) hφ).le
  have hprod' := mul_le_mul hratio.2 hscale'.2 (div_pos ha hb).le (by norm_num : (0 : ℝ) ≤ 1.001)
  have he : standardNormalDensity w / (r * b * binomialWeight p n k) =
      (standardNormalDensity w / standardNormalDensity z) * (a / b) / q := by
    dsimp only [q]
    field_simp
  rw [clusterGaussianIncrement_deriv, Real.sqrt_mul (Nat.cast_nonneg n)]
  change (0.98 : ℝ) ≤ standardNormalDensity w / (r * b * binomialWeight p n k) ∧
    standardNormalDensity w / (r * b * binomialWeight p n k) ≤ 1.02
  rw [he]
  constructor
  · apply (le_div_iff₀ hq0).mpr
    nlinarith only [hprod, hq.2]
  · apply (div_le_iff₀ hq0).mpr
    nlinarith only [hprod', hq.1]

theorem manuscript_effective_central_gaussian_derivative
    (p s : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hns : (n : ℝ) * s ≤ 1 / (10 : ℝ) ^ 12)
    (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    0 < binomialWeight p n k ∧ ∀ u : ℝ, |u| ≤ 3 / 5 →
      3 / 4 ≤ deriv (clusterGaussianIncrement p n k s) u ∧ deriv (clusterGaussianIncrement p n k s) u ≤ 5 / 4 := by
  obtain ⟨hb, hd⟩ := manuscript_effective_central_gaussian_derivative_ratio p s hp hs n k hn hns hk hz
  refine ⟨hb, ?_⟩
  intro u hu
  have h := hd u hu
  constructor <;> linarith [h.1, h.2]

end BerryEsseen
