import BerryEsseen.ManuscriptClusterSquare
import BerryEsseen.EffectivePeakCalculus
import BerryEsseen.IntegerWindow

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem effective_cluster_frequency_budget (s T u : ℝ) (hs : 0 ≤ s) (hT : 10 ≤ T)
    (hsT : s * T ^ 2 ≤ 1 / 10000) (hu : |u| ≤ T + 1 / 2) :
    10 * s * (1 + u ^ 2) ≤ 0.0011125 ∧
      s * (2 * |u| + (3 / 2) * u ^ 2) ≤ 0.0002 ∧
      s * (2 * |u| + (3 / 2) * u ^ 2) ≤ 3 * s * T ^ 2 := by
  have hT2 : 100 ≤ T ^ 2 := by nlinarith
  have huT : |u| ≤ (21 / 20 : ℝ) * T := by linarith
  have hu2 : u ^ 2 ≤ (441 / 400 : ℝ) * T ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg u) huT 2
    norm_num only [mul_pow, sq_abs] at h
    exact h
  have hu1 : |u| ≤ (21 / 200 : ℝ) * T ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) (show 0 ≤ T by linarith)]
  have hA : 1 + u ^ 2 ≤ (89 / 80 : ℝ) * T ^ 2 := by linarith
  have hB : 2 * |u| + (3 / 2 : ℝ) * u ^ 2 ≤ 2 * T ^ 2 := by nlinarith
  have hAm := mul_le_mul_of_nonneg_left hA hs
  have hBm := mul_le_mul_of_nonneg_left hB hs
  have hs0 := mul_nonneg hs (sq_nonneg T)
  constructor
  · nlinarith only [hAm, hsT]
  constructor <;> nlinarith only [hBm, hsT, hs0]

theorem effective_cluster_variance_budget (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc 0 1) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    averageNoiseVariance P Q p * T ^ 2 ≤ 1 / 10000 := by
  have hT0 : 0 < T := by linarith
  have hmul : ε * T ≤ 1 / 100 := by
    have h := (le_div_iff₀ (by positivity : 0 < 100 * T)).mp (show ε ≤ 1 / (100 * T) by simpa only [one_div] using hεT)
    nlinarith
  have hsq := pow_le_pow_left₀ (mul_nonneg hε hT0.le) hmul 2
  have hP2 := mul_le_mul_of_nonneg_left (P.secondMoment_le_sq ε hε hP) (sub_nonneg.mpr hp.2)
  have hQ2 := mul_le_mul_of_nonneg_left (Q.secondMoment_le_sq ε hε hQ) hp.1
  have hs : averageNoiseVariance P Q p ≤ ε ^ 2 := by
    unfold averageNoiseVariance
    nlinarith only [hP2, hQ2]
  have hsT := mul_le_mul_of_nonneg_right hs (sq_nonneg T)
  nlinarith only [hsq, hsT]

theorem effective_cluster_curvature (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (j : ℤ) (u : ℝ) (hu : |u| ≤ T + 1 / 2) (huj : |u - j * (2 * Real.pi)| ≤ 1 / 4) :
    twoClusterSquareCurvature P Q p u ≤ -2 / 5 := by
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hεsmall : ε ≤ 1 / 10 := by
    apply hεT.trans
    apply (inv_le_comm₀ (by positivity : 0 < 100 * T) (by norm_num : (0 : ℝ) < 1 / 10)).mpr
    norm_num
    linarith
  have hsT := effective_cluster_variance_budget P Q p ε T hp01 hε hT hεT hP hQ
  have hbudget := (effective_cluster_frequency_budget (averageNoiseVariance P Q p) T u
    (averageNoiseVariance_nonneg P Q p hp01) hT hsT hu).1
  have hdiff := manuscript_twoCluster_square_curvature_difference P Q p ε hp01 ⟨hε, hεsmall⟩ hP hQ u
  rw [bernoulliSquareCurvature_formula] at hdiff
  have hv : 6 / 25 ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (show 0 ≤ 3 / 5 - p by linarith [hp.2])]
  have hcos : 31 / 32 ≤ Real.cos u := by
    have hsquare := pow_le_pow_left₀ (abs_nonneg (u - j * (2 * Real.pi))) huj 2
    rw [sq_abs] at hsquare
    have hc := Real.one_sub_sq_div_two_le_cos (x := u - j * (2 * Real.pi))
    rw [Real.cos_sub_int_mul_two_pi] at hc
    nlinarith only [hsquare, hc]
  have hvcos := mul_le_mul hv hcos (by norm_num : (0 : ℝ) ≤ 31 / 32) (by positivity : 0 ≤ p * (1 - p))
  have hupper := (abs_le.mp hdiff).2
  nlinarith only [hupper, hvcos, hbudget]

theorem bernoulli_endpoint_slopes (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20)) (j : ℤ) :
    0.11 < bernoulliSquareSlope p ((j : ℝ) * (2 * Real.pi) - 1 / 4) ∧
      bernoulliSquareSlope p ((j : ℝ) * (2 * Real.pi) + 1 / 4) < -0.11 := by
  have hv : 6 / 25 ≤ p * (1 - p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (show 0 ≤ 3 / 5 - p by linarith [hp.2])]
  have hsin : (6 / 25 : ℝ) < Real.sin (1 / 4) := by
    have h := Real.sin_gt_sub_cube (x := 1 / 4) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hprod := mul_lt_mul_of_pos_left hsin (show 0 < p * (1 - p) by linarith)
  rw [bernoulliSquareSlope_formula, bernoulliSquareSlope_formula,
    Real.sin_int_mul_two_pi_sub, add_comm ((j : ℝ) * (2 * Real.pi)), Real.sin_add_int_mul_two_pi]
  constructor <;> nlinarith only [hv, hprod]

theorem effective_cluster_peak (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (j : ℤ) (hj : |(j : ℝ) * (2 * Real.pi)| ≤ T + 1 / 4) :
    ∃ m ∈ Ioo ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4),
      twoClusterSquareSlope P Q p m = 0 ∧
      |m - (j : ℝ) * (2 * Real.pi)| ≤ 8 * averageNoiseVariance P Q p * T ^ 2 ∧
      ∀ u ∈ Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4), ∀ n : ℕ,
        ‖charFun (twoClusterMeasure P Q p) u‖ ^ n ≤ Real.exp (-(n : ℝ) * (u - m) ^ 2 / 10) := by
  let r : ℝ := (j : ℝ) * (2 * Real.pi)
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hp05 : p ∈ Icc 0 (1 / 2) := ⟨hp01.1, by linarith [hp.2]⟩
  have hεsmall : ε ∈ Icc 0 (1 / 10) := by
    refine ⟨hε, hεT.trans ?_⟩
    apply (inv_le_comm₀ (by positivity : 0 < 100 * T) (by norm_num : (0 : ℝ) < 1 / 10)).mpr
    norm_num
    linarith
  letI := twoClusterMeasure_probability P Q p hp01
  have hs0 := averageNoiseVariance_nonneg P Q p hp01
  have hsT := effective_cluster_variance_budget P Q p ε T hp01 hε hT hεT hP hQ
  have hlocal (u : ℝ) (hu : u ∈ Icc (r - 1 / 4) (r + 1 / 4)) : |u - r| ≤ 1 / 4 := by
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hrange (u : ℝ) (hu : u ∈ Icc (r - 1 / 4) (r + 1 / 4)) : |u| ≤ T + 1 / 2 := by
    have h := abs_add_le (u - r) r
    rw [sub_add_cancel] at h
    have hb := hlocal u hu
    change |r| ≤ T + 1 / 4 at hj
    linarith
  have hcurv (u : ℝ) (hu : u ∈ Icc (r - 1 / 4) (r + 1 / 4)) :
      twoClusterSquareCurvature P Q p u ≤ -2 / 5 :=
    effective_cluster_curvature P Q p ε T hp hε hT hεT hP hQ j u (hrange u hu) (hlocal u hu)
  have hdiff (u : ℝ) (hu : u ∈ Icc (r - 1 / 4) (r + 1 / 4)) :
      |twoClusterSquareSlope P Q p u - bernoulliSquareSlope p u| ≤ 0.0002 :=
    (manuscript_twoCluster_square_slope_difference P Q p ε hp01 hεsmall hP hQ u).trans
      (effective_cluster_frequency_budget _ T u hs0 hT hsT (hrange u hu)).2.1
  have hL : 0 < twoClusterSquareSlope P Q p (r - 1 / 4) := by
    have h := (abs_le.mp (hdiff _ ⟨le_rfl, by linarith⟩)).1
    have hB := (bernoulli_endpoint_slopes p hp j).1
    change (0.11 : ℝ) < bernoulliSquareSlope p (r - 1 / 4) at hB
    linarith
  have hR : twoClusterSquareSlope P Q p (r + 1 / 4) < 0 := by
    have h := (abs_le.mp (hdiff _ ⟨by linarith, le_rfl⟩)).2
    have hB := (bernoulli_endpoint_slopes p hp j).2
    change bernoulliSquareSlope p (r + 1 / 4) < (-0.11 : ℝ) at hB
    linarith
  obtain ⟨m, hm, hcrit⟩ := exists_interior_critical_point (twoClusterSquareSlope P Q p)
    (twoClusterSquareCurvature P Q p) (r - 1 / 4) (r + 1 / 4) (by linarith)
    (fun u _ => twoClusterSquareSlope_hasDerivAt P Q p hp01 u) hL hR
  have hmcc : m ∈ Icc (r - 1 / 4) (r + 1 / 4) := ⟨hm.1.le, hm.2.le⟩
  have hrcc : r ∈ Icc (r - 1 / 4) (r + 1 / 4) := ⟨by linarith, by linarith⟩
  have hdist := critical_point_distance_of_curvature (twoClusterSquareSlope P Q p)
    (twoClusterSquareCurvature P Q p) (r - 1 / 4) (r + 1 / 4) m r (2 / 5) (by norm_num)
    hmcc hrcc (fun u _ => twoClusterSquareSlope_hasDerivAt P Q p hp01 u) (fun v hv => by simpa only [neg_div] using hcurv v hv) hcrit
  have hBzero : bernoulliSquareSlope p r = 0 := by
    rw [bernoulliSquareSlope_formula]
    have he : Real.sin r = 0 := by
      dsimp [r]
      simpa only [zero_add, Real.sin_zero] using Real.sin_add_int_mul_two_pi 0 j
    rw [he, mul_zero]
  have hcenter := manuscript_twoCluster_square_slope_difference P Q p ε hp01 hεsmall hP hQ r
  rw [hBzero, sub_zero] at hcenter
  have hcenterB := (effective_cluster_frequency_budget _ T r hs0 hT hsT (hrange r hrcc)).2.2
  have hshift : |m - r| ≤ 8 * averageNoiseVariance P Q p * T ^ 2 := by
    nlinarith only [hdist, hcenter, hcenterB, mul_nonneg hs0 (sq_nonneg T)]
  refine ⟨m, hm, hcrit, hshift, ?_⟩
  intro u hu n
  have hquad := quadratic_upper_with_curvature (twoClusterSquare P Q p) (twoClusterSquareSlope P Q p)
    (twoClusterSquareCurvature P Q p) (r - 1 / 4) (r + 1 / 4) m u (2 / 5) (by norm_num)
    hmcc hu (fun v _ => twoClusterSquare_hasDerivAt P Q p hp01 v)
    (fun v _ => twoClusterSquareSlope_hasDerivAt P Q p hp01 v) (fun v hv => by simpa only [neg_div] using hcurv v hv) hcrit
  have hmnorm := norm_charFun_le_one (μ := twoClusterMeasure P Q p) m
  have hm1 : twoClusterSquare P Q p m ≤ 1 := by
    unfold twoClusterSquare
    nlinarith [norm_nonneg (charFun (twoClusterMeasure P Q p) m)]
  have hpoint : ‖charFun (twoClusterMeasure P Q p) u‖ ^ 2 ≤ 1 - (1 / 5) * (u - m) ^ 2 := by
    change twoClusterSquare P Q p u ≤ _
    linarith
  have h := norm_pow_gaussian_of_quadratic_bound (charFun (twoClusterMeasure P Q p) u) (u - m) (1 / 5) hpoint n
  convert h using 1
  congr 1
  ring

end BerryEsseen
