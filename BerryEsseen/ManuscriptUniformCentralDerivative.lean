import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.CentralGaussianDerivative
import BerryEsseen.GeneralBinomialConsequences

/-! Uniform central estimates on the manuscript's fixed initial parameter
interval. The window is fixed before the variance budget is selected. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_uniform_variance_scale (p s : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hs : s ∈ Icc 0 (1 / 4)) :
    Real.sqrt (p * (1 - p) + s) ∈ Icc (2 / 5) 1 ∧
    Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p)) ∈ Icc 0 (2 * s) ∧
    |Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) - 1| ≤ 5 * s := by
  have hb := bernoulli_general_parameter_bounds p (2 / 5) (by norm_num) hp.1
    (by linarith [hp.2])
  have hv : 0 < p * (1 - p) := mul_pos hb.1.1 (sub_pos.mpr hb.1.2)
  have hV : 0 < p * (1 - p) + s := by linarith [hs.1]
  have hσ := Real.sqrt_pos.mpr hV
  have hv2 := Real.sq_sqrt hv.le
  have hV2 := Real.sq_sqrt hV.le
  have hm : Real.sqrt (p * (1 - p)) ≤ Real.sqrt (p * (1 - p) + s) :=
    Real.sqrt_le_sqrt (by linarith [hs.1])
  have hlo : (2 / 5 : ℝ) ≤ Real.sqrt (p * (1 - p) + s) := hb.2.1.trans hm
  have hhi : Real.sqrt (p * (1 - p) + s) ≤ 1 := by
    nlinarith [sq_nonneg (p - 1 / 2), hs.2]
  have hd0 : 0 ≤ Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p)) :=
    sub_nonneg.mpr hm
  have hd : Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p)) ≤ 2 * s := by
    have hprod := mul_nonneg hd0
      (show 0 ≤ Real.sqrt (p * (1 - p) + s) + Real.sqrt (p * (1 - p)) - 1 / 2 by
        linarith [hb.2.1])
    nlinarith only [hprod, hv2, hV2]
  refine ⟨⟨hlo, hhi⟩, ⟨hd0, hd⟩, ?_⟩
  have hrat : Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) - 1 ≤ 0 := by
    have hh := (div_le_one hσ).mpr hm
    linarith
  rw [abs_of_nonpos hrat]
  have he : -(Real.sqrt (p * (1 - p)) / Real.sqrt (p * (1 - p) + s) - 1) =
      (Real.sqrt (p * (1 - p) + s) - Real.sqrt (p * (1 - p))) /
        Real.sqrt (p * (1 - p) + s) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ hσ).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlo hs.1]

theorem manuscript_uniform_central_derivative (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ s0 > 0, ∃ c > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ p ∈ Icc (2 / 5 : ℝ) (9 / 20), ∀ n ≥ N, ∀ s ∈ Icc 0 s0,
      ∀ k : ℕ, k ≤ n → |binomialZ p n k| ≤ M →
        c ≤ Real.sqrt (n : ℝ) * binomialWeight p n k ∧
        0 < binomialWeight p n k ∧
        ∀ u : ℝ, |u| ≤ 3 / 5 →
          3 / 4 ≤ deriv (clusterGaussianIncrement p n k s) u ∧
          deriv (clusterGaussianIncrement p n k s) u ≤ 5 / 4 := by
  let m := centralDensityFloor M
  have hm : 0 < m := centralDensityFloor_pos M
  let δ := min 1 (m / 40)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδm : δ ≤ m / 40 := min_le_right _ _
  let s0 := min (1 / 4 : ℝ) (min (m / 320) (m / (300 * (M + 1))))
  have hs0 : 0 < s0 := lt_min (by norm_num)
    (lt_min (by positivity) (div_pos hm (by positivity)))
  have hK : Icc (2 / 5 : ℝ) (9 / 20) ⊆ Ioo 0 1 := by
    intro p hp
    constructor <;> linarith [hp.1, hp.2]
  obtain ⟨Nb, hNb⟩ := compact_binomial_local_mass W S _ isCompact_Icc hK δ hδ
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nr, hNr⟩ := eventually_atTop.mp (hroot.eventually_ge_atTop (120 / m))
  refine ⟨s0, hs0, m / 2, by positivity, max (max Nb Nr) 1, le_max_right _ _, ?_⟩
  intro p hp n hn s hs k _hk hz
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnNb : Nb ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnNr : Nr ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hpar := bernoulli_general_parameter_bounds p (2 / 5) (by norm_num) hp.1
    (by linarith [hp.2])
  let v := p * (1 - p)
  let r := Real.sqrt (n : ℝ)
  let σ := Real.sqrt (v + s)
  let z := binomialZ p n k
  let b := binomialWeight p n k
  have hv : 0 < v := mul_pos hpar.1.1 (sub_pos.mpr hpar.1.2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hbase : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hbaselo : (2 / 5 : ℝ) ≤ Real.sqrt v := hpar.2.1
  have hbasehi : Real.sqrt v ≤ 1 := hpar.2.2.1.trans (by norm_num)
  have hsquarter : s ≤ 1 / 4 := hs.2.trans (min_le_left _ _)
  have hsm : s ≤ m / 320 := hs.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsM : s ≤ m / (300 * (M + 1)) := hs.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hσbounds := manuscript_uniform_variance_scale p s hp ⟨hs.1, hsquarter⟩
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by linarith [hs.1])
  have hσlo : (2 / 5 : ℝ) ≤ σ := hσbounds.1.1
  have hC : m ≤ standardNormalDensity z := standardNormalDensity_central_lower M z hM hz
  have hmass : |r * b - standardNormalDensity z / Real.sqrt v| ≤ δ := by
    have hh := (hNb n hnNb p hp (k : ℤ)).le
    simpa only [binomialIntegerWeight, Int.natCast_nonneg, if_true, Int.toNat_natCast] using hh
  have hb0 : 0 ≤ b := binomialWeight_nonneg p ⟨hpar.1.1.le, hpar.1.2.le⟩ n k
  have hrb0 : 0 ≤ r * b := mul_nonneg hr.le hb0
  have hCratio : m ≤ standardNormalDensity z / Real.sqrt v := by
    apply (le_div_iff₀ hbase).mpr
    exact (mul_le_mul_of_nonneg_left hbasehi hm.le).trans (by simpa using hC)
  have hrblower : m / 2 ≤ r * b := by
    have hh := (abs_le.mp hmass).1
    linarith only [hh, hCratio, hδm, hm]
  have hbpos : 0 < b := (mul_pos_iff_of_pos_left hr).mp ((by positivity : 0 < m / 2).trans_le hrblower)
  have hCupper : standardNormalDensity z / Real.sqrt v ≤ 3 := by
    apply (div_le_iff₀ hbase).mpr
    have hh := (standardNormalDensity_le_phi0 z).trans phi0_lt_two_fifths.le
    linarith only [hh, hbaselo]
  have hrbupper : r * b ≤ 4 := by
    have hh := (abs_le.mp hmass).2
    linarith only [hh, hCupper, hδ1]
  have hD : |σ * (r * b) - standardNormalDensity z| ≤ m / 10 := by
    have hmasslo := mul_le_mul_of_nonneg_left (abs_le.mp hmass).1 hbase.le
    have hmasshi := mul_le_mul_of_nonneg_left (abs_le.mp hmass).2 hbase.le
    rw [mul_sub, mul_div_cancel₀ _ hbase.ne'] at hmasslo hmasshi
    have he := mul_le_mul_of_nonneg_right hbasehi hδ.le
    have hdiff := mul_le_mul hσbounds.2.1.2 hrbupper hrb0 (mul_nonneg (by norm_num) hs.1)
    have hdiff0 := mul_nonneg hσbounds.2.1.1 hrb0
    change (σ - Real.sqrt v) * (r * b) ≤ (2 * s) * 4 at hdiff
    change 0 ≤ (σ - Real.sqrt v) * (r * b) at hdiff0
    rw [abs_le]
    constructor <;> nlinarith only [hmasslo, hmasshi, he, hdiff, hdiff0, hδm, hsm, hm]
  refine ⟨hrblower, hbpos, ?_⟩
  intro u hu
  have hN := scaled_argument_density_bound r v s z u M (3 / 5) hr hv hs.1 hM
    (by norm_num) hz hu
  have htail : (3 / 5 : ℝ) / (r * σ) ≤ 2 / r := by
    apply (div_le_iff₀ (mul_pos hr hσ)).mpr
    have he : 2 / r * (r * σ) = 2 * σ := by field_simp
    rw [he]
    linarith only [hσlo]
  have hrlarge : 120 / m ≤ r := hNr n hnNr
  have hinv : 2 / r ≤ m / 60 := by
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ hm).mp hrlarge
    nlinarith only [hh]
  have hMs : 5 * M * s ≤ m / 60 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 300 * (M + 1))).mp hsM
    nlinarith only [hh, hs.1]
  have hrat : |Real.sqrt v / σ - 1| ≤ 5 * s := hσbounds.2.2
  have hinside : M * |Real.sqrt v / σ - 1| + (3 / 5 : ℝ) / (r * σ) ≤ m / 30 := by
    have hh := mul_le_mul_of_nonneg_left hrat hM
    nlinarith only [hh, hMs, htail, hinv]
  have hnum : 3 * phi0 * (M * |Real.sqrt v / σ - 1| + (3 / 5 : ℝ) / (r * σ)) ≤ m / 10 := by
    have hh := mul_le_mul (show 3 * phi0 ≤ (3 : ℝ) by linarith [phi0_lt_two_fifths]) hinside
      (by positivity : 0 ≤ M * |Real.sqrt v / σ - 1| + (3 / 5 : ℝ) / (r * σ))
      (by norm_num : (0 : ℝ) ≤ 3)
    linarith only [hh]
  have ht : r * Real.sqrt v * z = (k : ℝ) - n * p := by
    calc
      r * Real.sqrt v * z = Real.sqrt v * (r * z) := by ring
      _ = _ := by
        rw [binomialZ_scaling p hpar.1 n hn1 k]
        change Real.sqrt v * (((k : ℝ) - n * p) / Real.sqrt v) = _
        exact mul_div_cancel₀ _ hbase.ne'
  rw [ht] at hN
  have hratio := positive_ratio_of_tenth_errors
    (standardNormalDensity (((k : ℝ) - n * p + u) / (r * σ))) (σ * (r * b))
    (standardNormalDensity z) m hm hC (hN.trans hnum) hD
  rw [clusterGaussianIncrement_deriv, Real.sqrt_mul (Nat.cast_nonneg n)]
  change 3 / 4 ≤ standardNormalDensity (((k : ℝ) - n * p + u) / (r * σ)) / ((r * σ) * b) ∧
    standardNormalDensity (((k : ℝ) - n * p + u) / (r * σ)) / ((r * σ) * b) ≤ 5 / 4
  rw [show (r * σ) * b = σ * (r * b) by ring]
  exact hratio.2

end BerryEsseen
