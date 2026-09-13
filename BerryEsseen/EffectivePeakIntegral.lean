import BerryEsseen.EffectiveClusterPeaks
import BerryEsseen.EffectiveGaussianTail
import BerryEsseen.AnnularIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem gaussian_linear_integral_Ioi (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2)) = 1 / (2 * b) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -Real.exp (-b * y ^ 2) / (2 * b))
      (x * Real.exp (-b * x ^ 2)) x := by
    convert (((((hasDerivAt_pow 2 x).const_mul (-b)).exp).neg).div_const (2 * b)) using 1
    dsimp only [Pi.neg_apply, Pi.sub_apply, id_eq]
    field_simp
    ring
  have hi : Integrable (fun x : ℝ => x * Real.exp (-b * x ^ 2)) := by
    simpa only [pow_one] using gaussian_nat_pow_integrable 1 b hb
  have ht : Tendsto (fun x : ℝ => -Real.exp (-b * x ^ 2) / (2 * b)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, neg_zero, zero_div] using
      ((gaussian_polynomial_tendsto_zero 0 b hb).neg.div_const (2 * b))
  simpa only [zero_pow (by omega : 2 ≠ 0), mul_zero, Real.exp_zero, zero_sub, neg_div, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (fun x _ => hd x) hi.integrableOn ht

theorem gaussian_abs_linear_integral (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, |x| * Real.exp (-b * x ^ 2)) = 1 / b := by
  have he : (fun x : ℝ => |x| * Real.exp (-b * x ^ 2)) =
      (fun x : ℝ => |x| * Real.exp (-b * |x| ^ 2)) := by
    funext x
    rw [sq_abs]
  rw [he, integral_comp_abs (f := fun x : ℝ => x * Real.exp (-b * x ^ 2)), gaussian_linear_integral_Ioi b hb]
  field_simp

def effectivePeakGaussian (n : ℕ) (m u : ℝ) : ℝ := Real.exp (-(n : ℝ) * (u - m) ^ 2 / 10)

theorem effectivePeakGaussian_integrable (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    Integrable (effectivePeakGaussian n m) := by
  have h := (integrable_exp_neg_mul_sq (by positivity : 0 < (n : ℝ) / 10)).comp_sub_right m
  convert h using 1
  funext u
  unfold effectivePeakGaussian
  congr 1
  ring

theorem effectivePeakGaussian_first_integrable (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    Integrable (fun u => |u - m| * effectivePeakGaussian n m u) := by
  have h := (gaussian_abs_pow_integrable 1 ((n : ℝ) / 10) (by positivity)).comp_sub_right m
  convert h using 1
  funext u
  simp only [pow_one, effectivePeakGaussian]
  congr 2
  ring

theorem effectivePeakGaussian_first_integral (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    (∫ u, |u - m| * effectivePeakGaussian n m u) = 10 / (n : ℝ) := by
  have he : (fun u => |u - m| * effectivePeakGaussian n m u) =
      (fun u => |u - m| * Real.exp (-((n : ℝ) / 10) * (u - m) ^ 2)) := by
    funext u
    unfold effectivePeakGaussian
    congr 2
    ring
  rw [he, integral_sub_right_eq_self (fun x : ℝ => |x| * Real.exp (-((n : ℝ) / 10) * x ^ 2)) m, gaussian_abs_linear_integral _ (by positivity)]
  field_simp

theorem effectivePeakGaussian_integral_le (n : ℕ) (hn : 1 ≤ n) (m : ℝ) :
    (∫ u, effectivePeakGaussian n m u) ≤ 6 / Real.sqrt (n : ℝ) := by
  have he : effectivePeakGaussian n m =
      (fun u => Real.exp (-((n : ℝ) / 10) * (u - m) ^ 2)) := by
    funext u
    unfold effectivePeakGaussian
    congr 1
    ring
  rw [he, integral_sub_right_eq_self (fun x : ℝ => Real.exp (-((n : ℝ) / 10) * x ^ 2)) m, integral_gaussian]
  rw [show Real.pi / ((n : ℝ) / 10) = (10 * Real.pi) / n by ring, Real.sqrt_div (by positivity)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith [Real.pi_lt_d2]

def rawUnitJitterIntegrand (μ : Measure ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  |Real.sinc (u / 2)| * ‖charFun μ u‖ ^ n / |u|

theorem rawUnitJitterIntegrand_nonneg (μ : Measure ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ rawUnitJitterIntegrand μ n u := by unfold rawUnitJitterIntegrand; positivity

theorem rawUnitJitterIntegrand_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measurable (rawUnitJitterIntegrand μ n) := by unfold rawUnitJitterIntegrand; fun_prop

theorem int_cast_abs_ge_one (j : ℤ) (hj : j ≠ 0) : (1 : ℝ) ≤ |(j : ℝ)| := by
  rcases lt_or_gt_of_ne hj with hn | hp
  · rw [abs_of_neg (by exact_mod_cast hn)]
    exact_mod_cast (by omega : (1 : ℤ) ≤ -j)
  · rw [abs_of_pos (by exact_mod_cast hp)]
    exact_mod_cast (by omega : (1 : ℤ) ≤ j)

theorem resonance_interval_abs_lower (j : ℤ) (hj : j ≠ 0) (u : ℝ)
    (hu : u ∈ Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4)) :
    5 * |(j : ℝ)| ≤ |u| := by
  have hdist : |(j : ℝ) * (2 * Real.pi) - u| ≤ 1 / 4 :=
    abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have h := abs_sub_le ((j : ℝ) * (2 * Real.pi)) u 0
  simp only [sub_zero, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h
  have hπ := mul_le_mul_of_nonneg_left Real.pi_gt_three.le (abs_nonneg (j : ℝ))
  linarith [int_cast_abs_ge_one j hj]

theorem unitJitter_resonance_zero (j : ℤ) (hj : j ≠ 0) :
    Real.sinc (((j : ℝ) * (2 * Real.pi)) / 2) = 0 := by
  rw [show ((j : ℝ) * (2 * Real.pi)) / 2 = (j : ℝ) * Real.pi by ring]
  rw [Real.sinc_of_ne_zero (mul_ne_zero (by exact_mod_cast hj) Real.pi_ne_zero), Real.sin_int_mul_pi, zero_div]

theorem unitJitter_peak_pointwise (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (j : ℤ) (hj : j ≠ 0) (m d : ℝ) (hd : 0 ≤ d)
    (hshift : |m - (j : ℝ) * (2 * Real.pi)| ≤ d)
    (u : ℝ) (hu : u ∈ Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4))
    (hpeak : ‖charFun μ u‖ ^ n ≤ effectivePeakGaussian n m u) :
    rawUnitJitterIntegrand μ n u ≤ (1 / (20 * |(j : ℝ)|)) * (|u - m| + d) * effectivePeakGaussian n m u := by
  have hjpos : 0 < |(j : ℝ)| := lt_of_lt_of_le (by norm_num) (int_cast_abs_ge_one j hj)
  have hH := spanJitter_multiplier_lipschitz 1 u ((j : ℝ) * (2 * Real.pi)) (by norm_num)
  simp only [one_mul, unitJitter_resonance_zero j hj, sub_zero] at hH
  have htri := abs_sub_le u m ((j : ℝ) * (2 * Real.pi))
  have hH' : |Real.sinc (u / 2)| ≤ (1 / 4) * (|u - m| + d) := by linarith
  have hnum := mul_le_mul hH' hpeak (pow_nonneg (norm_nonneg _) _) (by positivity)
  unfold rawUnitJitterIntegrand
  calc
    _ ≤ ((1 / 4) * (|u - m| + d) * effectivePeakGaussian n m u) / |u| :=
      div_le_div_of_nonneg_right hnum (abs_nonneg u)
    _ ≤ ((1 / 4) * (|u - m| + d) * effectivePeakGaussian n m u) / (5 * |(j : ℝ)|) :=
      div_le_div_of_nonneg_left (by unfold effectivePeakGaussian; positivity) (by positivity)
        (resonance_interval_abs_lower j hj u hu)
    _ = _ := by ring

theorem unitJitter_peak_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (j : ℤ) (hj : j ≠ 0) (m d : ℝ) (hd : 0 ≤ d)
    (hshift : |m - (j : ℝ) * (2 * Real.pi)| ≤ d)
    (hpeak : ∀ u ∈ Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4),
      ‖charFun μ u‖ ^ n ≤ effectivePeakGaussian n m u) :
    IntegrableOn (rawUnitJitterIntegrand μ n)
      (Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4)) ∧
    (∫ u in Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4), rawUnitJitterIntegrand μ n u) ≤
      (1 / (20 * |(j : ℝ)|)) * (10 / (n : ℝ) + 6 * d / Real.sqrt (n : ℝ)) := by
  let K := Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4)
  let C := 1 / (20 * |(j : ℝ)|)
  let g := fun u => C * (|u - m| + d) * effectivePeakGaussian n m u
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : Integrable g := by
    convert ((effectivePeakGaussian_first_integrable n hn m).add ((effectivePeakGaussian_integrable n hn m).const_mul d)).const_mul C using 1
    funext u
    dsimp only [g, Pi.add_apply]
    ring
  have hnonneg (u : ℝ) : 0 ≤ g u := by dsimp [g, effectivePeakGaussian]; positivity
  have hle : ∀ᵐ u ∂volume.restrict K, rawUnitJitterIntegrand μ n u ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact unitJitter_peak_pointwise μ n j hj m d hd hshift u hu (hpeak u hu)
  have hi : IntegrableOn (rawUnitJitterIntegrand μ n) K := by
    apply hg.integrableOn.mono' (rawUnitJitterIntegrand_measurable μ n).aestronglyMeasurable
    filter_upwards [hle] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rawUnitJitterIntegrand_nonneg μ n u)] using hu
  refine ⟨hi, ?_⟩
  have hfull : (∫ u, g u) = C * (10 / (n : ℝ) + d * (∫ u, effectivePeakGaussian n m u)) := by
    have he : g = fun u => C * (|u - m| * effectivePeakGaussian n m u + d * effectivePeakGaussian n m u) := by funext u; dsimp [g]; ring
    rw [he, integral_const_mul, integral_add (effectivePeakGaussian_first_integrable n hn m)
      ((effectivePeakGaussian_integrable n hn m).const_mul d), integral_const_mul, effectivePeakGaussian_first_integral n hn m]
  calc
    _ ≤ ∫ u in K, g u := integral_mono_ae hi hg.integrableOn hle
    _ ≤ ∫ u, g u := setIntegral_le_integral hg (ae_of_all _ hnonneg)
    _ = C * (10 / (n : ℝ) + d * (∫ u, effectivePeakGaussian n m u)) := hfull
    _ ≤ C * (10 / (n : ℝ) + 6 * d / Real.sqrt (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have h := mul_le_mul_of_nonneg_left (effectivePeakGaussian_integral_le n hn m) hd
      rw [show d * (6 / Real.sqrt (n : ℝ)) = 6 * d / Real.sqrt (n : ℝ) by ring] at h
      linarith only [h]

theorem effective_cluster_peak_integral (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (j : ℤ) (hj0 : j ≠ 0) (hj : |(j : ℝ) * (2 * Real.pi)| ≤ T + 1 / 4)
    (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (rawUnitJitterIntegrand (twoClusterMeasure P Q p) n)
      (Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4)) ∧
    (∫ u in Icc ((j : ℝ) * (2 * Real.pi) - 1 / 4) ((j : ℝ) * (2 * Real.pi) + 1 / 4),
      rawUnitJitterIntegrand (twoClusterMeasure P Q p) n u) ≤
        1 / (2 * |(j : ℝ)| * (n : ℝ)) +
          12 * averageNoiseVariance P Q p * T ^ 2 / (5 * |(j : ℝ)| * Real.sqrt (n : ℝ)) := by
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  letI := twoClusterMeasure_probability P Q p hp01
  obtain ⟨m, hm, hcrit, hshift, hpeak⟩ := effective_cluster_peak P Q p ε T hp hε hT hεT hP hQ j hj
  have hd : 0 ≤ 8 * averageNoiseVariance P Q p * T ^ 2 := by
    have hs := averageNoiseVariance_nonneg P Q p hp01
    positivity
  have hi := unitJitter_peak_integral (twoClusterMeasure P Q p) n hn j hj0 m
    (8 * averageNoiseVariance P Q p * T ^ 2) hd hshift (fun u hu => hpeak u hu n)
  refine ⟨hi.1, ?_⟩
  convert hi.2 using 1 <;> ring

end BerryEsseen
