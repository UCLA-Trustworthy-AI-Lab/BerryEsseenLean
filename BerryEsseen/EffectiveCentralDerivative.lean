import BerryEsseen.EffectiveBinomial
import BerryEsseen.CentralClusterBudget

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem effective_small_variance_scale (p s : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12)) :
    Real.sqrt (p * (1 - p) + s) ∈ Icc 0.48 1 ∧
    (Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p))) ∈ Icc 0 (2 * s) ∧
    |Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) - 1| ≤ 5 * s := by
  have hb := effective_binomial_parameters p hp
  have hv := mul_pos hb.1.1 (sub_pos.mpr hb.1.2)
  have hV : 0 < p * (1 - p) + s := by linarith [hs.1]
  have hσ0 := Real.sqrt_pos.mpr hV
  have hv2 := Real.sq_sqrt hv.le
  have hV2 := Real.sq_sqrt hV.le
  have hm : Real.sqrt (p * (1 - p)) ≤ Real.sqrt (p * (1 - p) + s) := Real.sqrt_le_sqrt (by linarith [hs.1])
  have hσlo : (0.48 : ℝ) ≤ Real.sqrt (p * (1 - p) + s) := hb.2.1.trans hm
  have hσhi : Real.sqrt (p * (1 - p) + s) ≤ 1 := by
    nlinarith [sq_nonneg (p - 1 / 2), hs.2]
  have hd0 : 0 ≤ Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p)) := sub_nonneg.mpr hm
  have hd : Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p)) ≤ 2 * s := by
    have hprod := mul_nonneg hd0 (show 0 ≤ Real.sqrt (p * (1 - p) + s) + Real.sqrt (p * (1 - p)) - 1 / 2 by linarith [hb.2.1])
    nlinarith only [hprod, hv2, hV2]
  refine ⟨⟨hσlo, hσhi⟩, ⟨hd0, hd⟩, ?_⟩
  have hle : Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) - 1 ≤ 0 := by
    have h := (div_le_one hσ0).mpr hm
    linarith
  rw [abs_of_nonpos hle]
  have he : -(Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) - 1) =
      (Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p))) / Real.sqrt (p * (1 - p) + s) := by field_simp [hσ0.ne']; ring
  rw [he]
  apply (div_le_iff₀ hσ0).mpr
  nlinarith [mul_le_mul_of_nonneg_left hσlo hs.1]

theorem effective_central_gaussian_derivative (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (p s : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    0 < binomialWeight p n k ∧ ∀ u : ℝ, |u| ≤ 3 / 5 →
      3 / 4 ≤ deriv (clusterGaussianIncrement p n k s) u ∧ deriv (clusterGaussianIncrement p n k s) u ≤ 5 / 4 := by
  let r := Real.sqrt (n : ℝ)
  let v := p * (1 - p)
  let σ := Real.sqrt (v + s)
  let z := binomialZ p n k
  let b := binomialWeight p n k
  have hb := effective_binomial_parameters p hp
  have hv : 0 < v := mul_pos hb.1.1 (sub_pos.mpr hb.1.2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hσb := effective_small_variance_scale p s hp hs
  have hσ : 0 < σ := by have h := hσb.1.1; change (0.48 : ℝ) ≤ σ at h; linarith
  have hbase := Real.sqrt_pos.mpr hv
  have hfloor := standardNormalDensity_effective_central z hz
  have hmass := effective_binomial_local_error S p hp n hn k hk
  change |r * b - standardNormalDensity z / Real.sqrt v| ≤ 4 / (10 : ℝ) ^ 47 at hmass
  have hw := effective_binomial_mass_upper B p hp n k (by omega)
  have hw0 : 0 ≤ b := binomialWeight_nonneg p ⟨hb.1.1.le, hb.1.2.le⟩ n k
  have hrb : r * b ≤ 2 := by
    change b ≤ 2 / r at hw
    have h := (le_div_iff₀ hr).mp hw
    nlinarith only [h]
  have hrb0 : 0 ≤ r * b := mul_nonneg hr.le hw0
  have hD : |σ * (r * b) - standardNormalDensity z| ≤ (1 / (10 : ℝ) ^ 6) / 10 := by
    have hmass' := abs_le.mp hmass
    have hleft := mul_le_mul_of_nonneg_left hmass'.1 hbase.le
    have hright := mul_le_mul_of_nonneg_left hmass'.2 hbase.le
    rw [mul_sub, mul_div_cancel₀ _ hbase.ne'] at hleft hright
    have hd := mul_le_mul hσb.2.1.2 hrb hrb0 (mul_nonneg (by norm_num) hs.1)
    have hd0 := mul_nonneg hσb.2.1.1 hrb0
    change (σ - Real.sqrt v) * (r * b) ≤ (2 * s) * 2 at hd
    change 0 ≤ (σ - Real.sqrt v) * (r * b) at hd0
    rw [abs_le]
    constructor <;> nlinarith [hs.2, hb.2.2.1]
  have hDpos := (positive_ratio_of_tenth_errors (standardNormalDensity z) (σ * (r * b))
    (standardNormalDensity z) (1 / (10 : ℝ) ^ 6) (by positivity) hfloor.le (by simp; positivity) hD).1
  have hbpos : 0 < b := (mul_pos_iff_of_pos_left hr).mp ((mul_pos_iff_of_pos_left hσ).mp hDpos)
  refine ⟨hbpos, ?_⟩
  intro u hu
  have hN := scaled_argument_density_bound r v s z u 5 (3 / 5) hr hv hs.1 (by norm_num) (by norm_num) hz hu
  have hrootlower := effective_binomial_root_lower n hn
  have htail : (3 / 5 : ℝ) / (r * σ) ≤ 2 / r := by
    apply (div_le_iff₀ (mul_pos hr hσ)).mpr
    have he : 2 / r * (r * σ) = 2 * σ := by field_simp
    rw [he]
    have h := hσb.1.1
    change (0.48 : ℝ) ≤ σ at h
    linarith
  have hinv : 2 / r ≤ 2 / (10 : ℝ) ^ 50 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hrootlower
  have hnum : 3 * phi0 * (5 * |Real.sqrt v / σ - 1| + (3 / 5 : ℝ) / (r * σ)) ≤ (1 / (10 : ℝ) ^ 6) / 10 := by
    have hrat := hσb.2.2
    change |Real.sqrt v / σ - 1| ≤ 5 * s at hrat
    have hinside : 5 * |Real.sqrt v / σ - 1| + (3 / 5 : ℝ) / (r * σ) ≤
        25 / (10 : ℝ) ^ 12 + 2 / (10 : ℝ) ^ 50 := by nlinarith [hs.2]
    have hm := mul_le_mul (show 3 * phi0 ≤ (1.2 : ℝ) by linarith [phi0_lt_two_fifths]) hinside
      (by positivity : 0 ≤ 5 * |Real.sqrt v / σ - 1| + (3 / 5 : ℝ) / (r * σ)) (by norm_num : (0 : ℝ) ≤ 1.2)
    nlinarith only [hm]
  have ht : r * Real.sqrt v * z = (k : ℝ) - n * p := by
    calc
      r * Real.sqrt v * z = Real.sqrt v * (r * z) := by ring
      _ = _ := by
        rw [binomialZ_scaling p hb.1 n (by omega) k]
        change Real.sqrt v * (((k : ℝ) - n * p) / Real.sqrt v) = _
        exact mul_div_cancel₀ _ hbase.ne'
  rw [ht] at hN
  have hratio := positive_ratio_of_tenth_errors
    (standardNormalDensity (((k : ℝ) - n * p + u) / (r * σ))) (σ * (r * b))
    (standardNormalDensity z) (1 / (10 : ℝ) ^ 6) (by positivity) hfloor.le (hN.trans hnum) hD
  rw [clusterGaussianIncrement_deriv, Real.sqrt_mul (Nat.cast_nonneg n)]
  change 3 / 4 ≤ standardNormalDensity (((k : ℝ) - n * p + u) / (r * σ)) / ((r * σ) * b) ∧
    standardNormalDensity (((k : ℝ) - n * p + u) / (r * σ)) / ((r * σ) * b) ≤ 5 / 4
  rw [show (r * σ) * b = σ * (r * b) by ring]
  exact hratio.2

end BerryEsseen
