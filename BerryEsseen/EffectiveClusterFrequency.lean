import BerryEsseen.EffectivePeakIntegral
import BerryEsseen.EffectiveClusterGap
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def positiveResonanceLabels (T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (Nat.floor T)).filter (fun k => (k : ℝ) * (2 * Real.pi) ≤ T + 1 / 4)

def resonanceCell (k : ℕ) : Set ℝ := Icc ((k : ℝ) * (2 * Real.pi) - 1 / 4) ((k : ℝ) * (2 * Real.pi) + 1 / 4)

theorem positiveResonanceLabels_properties (T : ℝ) (k : ℕ) (hk : k ∈ positiveResonanceLabels T) :
    1 ≤ k ∧ k ≤ Nat.floor T ∧ (k : ℝ) * (2 * Real.pi) ≤ T + 1 / 4 := by
  classical
  simpa only [positiveResonanceLabels, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hk

theorem positiveResonanceLabels_cover (T u : ℝ) (hu : u ∈ Icc (1 / 2) T)
    (j : ℤ) (hj : |u - (j : ℝ) * (2 * Real.pi)| < 1 / 4) :
    ∃ k ∈ positiveResonanceLabels T, u ∈ resonanceCell k := by
  classical
  have hd := abs_lt.mp hj
  have hjr : 0 < (j : ℝ) := by
    have hr : 0 < (j : ℝ) * (2 * Real.pi) := by linarith [hu.1]
    exact (mul_pos_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).mp hr
  have hjZ : 0 < j := by exact_mod_cast hjr
  let k := j.toNat
  have hkcast : (k : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjZ.le
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkr : (k : ℝ) * (2 * Real.pi) ≤ T + 1 / 4 := by rw [hkcast]; linarith [hu.2]
  have hkT : (k : ℝ) ≤ T := by
    have hπ := mul_le_mul_of_nonneg_left Real.pi_gt_three.le (Nat.cast_nonneg k)
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  refine ⟨k, ?_, ?_⟩
  · simp only [positiveResonanceLabels, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hk1, Nat.le_floor hkT⟩, hkr⟩
  · unfold resonanceCell
    rw [hkcast]
    constructor <;> linarith

theorem positiveResonanceLabels_harmonic (T : ℝ) (hT : 1 ≤ T) :
    (∑ k ∈ positiveResonanceLabels T, (k : ℝ)⁻¹) ≤ 1 + Real.log T := by
  classical
  have hs : positiveResonanceLabels T ⊆ Finset.Icc 1 (Nat.floor T) := by
    unfold positiveResonanceLabels
    exact Finset.filter_subset _ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => (k : ℝ)⁻¹) hs (fun k _ _ => inv_nonneg.mpr (Nat.cast_nonneg k))
  have hh := harmonic_floor_le_one_add_log T hT
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  exact h.trans hh

theorem positiveResonanceLabels_sum_budget (T s : ℝ) (hT : 1 ≤ T) (hs : 0 ≤ s)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ positiveResonanceLabels T,
      (1 / (2 * (k : ℝ) * (n : ℝ)) + 12 * s * T ^ 2 / (5 * (k : ℝ) * Real.sqrt (n : ℝ)))) ≤
      (1 / (2 * (n : ℝ)) + 12 * s * T ^ 2 / (5 * Real.sqrt (n : ℝ))) * (1 + Real.log T) := by
  classical
  have he (k : ℕ) : 1 / (2 * (k : ℝ) * (n : ℝ)) + 12 * s * T ^ 2 / (5 * (k : ℝ) * Real.sqrt (n : ℝ)) =
      (1 / (2 * (n : ℝ)) + 12 * s * T ^ 2 / (5 * Real.sqrt (n : ℝ))) * (k : ℝ)⁻¹ := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (positiveResonanceLabels_harmonic T hT) (by positivity)

theorem inverse_interval_integral (a T : ℝ) (ha : 0 < a) (haT : a ≤ T) :
    (∫ u in Icc a T, (u : ℝ)⁻¹) = Real.log (T / a) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haT]
  exact integral_inv (by rw [uIcc_of_le haT]; simp only [mem_Icc, not_and]; intro h; linarith)

theorem effective_cluster_positive_frequency_integral (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (rawUnitJitterIntegrand (twoClusterMeasure P Q p) n) (Icc (1 / 2) T) ∧
    (∫ u in Icc (1 / 2) T, rawUnitJitterIntegrand (twoClusterMeasure P Q p) n u) ≤
      Real.exp (-(n : ℝ) / 200) * Real.log (2 * T) +
      (1 / (2 * (n : ℝ)) + 12 * averageNoiseVariance P Q p * T ^ 2 / (5 * Real.sqrt (n : ℝ))) * (1 + Real.log T) := by
  classical
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  letI := twoClusterMeasure_probability P Q p hp01
  let f := rawUnitJitterIntegrand (twoClusterMeasure P Q p) n
  let K : Set ℝ := Icc (1 / 2) T
  let J := positiveResonanceLabels T
  let E := Real.exp (-(n : ℝ) / 200)
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  let back : ℝ → ℝ := K.indicator (fun u : ℝ => u⁻¹)
  let peak : ℕ → ℝ → ℝ := fun k => (resonanceCell k).indicator f
  let g : ℝ → ℝ := fun u => E * back u + ∑ k ∈ J, peak k u
  have hfn (u : ℝ) : 0 ≤ f u := rawUnitJitterIntegrand_nonneg _ _ _
  have hpn (k : ℕ) (u : ℝ) : 0 ≤ peak k u := by
    dsimp [peak]
    by_cases hu : u ∈ resonanceCell k
    · rw [indicator_of_mem hu]
      exact hfn u
    · rw [indicator_of_notMem hu]
  have hbn (u : ℝ) : 0 ≤ back u := by
    dsimp [back]
    by_cases hu : u ∈ K
    · rw [indicator_of_mem hu]
      exact inv_nonneg.mpr (by have h := hu.1; change (1 / 2 : ℝ) ≤ u at h; linarith)
    · rw [indicator_of_notMem hu]
  have hgn (u : ℝ) : 0 ≤ g u := add_nonneg (mul_nonneg hEn (hbn u))
    (Finset.sum_nonneg (fun k _ => hpn k u))
  have hkb (k : ℕ) (hk : k ∈ J) : IntegrableOn f (resonanceCell k) ∧
      (∫ u in resonanceCell k, f u) ≤ 1 / (2 * (k : ℝ) * (n : ℝ)) +
        12 * averageNoiseVariance P Q p * T ^ 2 / (5 * (k : ℝ) * Real.sqrt (n : ℝ)) := by
    have hkprops := positiveResonanceLabels_properties T k hk
    have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hkr : |((k : ℤ) : ℝ) * (2 * Real.pi)| ≤ T + 1 / 4 := by
      simpa only [Int.cast_natCast, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) * (2 * Real.pi))] using hkprops.2.2
    have hi := effective_cluster_peak_integral P Q p ε T hp hε hT hεT hP hQ (k : ℤ) hkZ hkr n hn
    simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k), resonanceCell, f] using hi
  have hpi (k : ℕ) (hk : k ∈ J) : Integrable (peak k) :=
    (hkb k hk).1.integrable_indicator measurableSet_Icc
  have hbi : Integrable back := (inverse_interval_integrable (1 / 2) T (by norm_num)).integrable_indicator measurableSet_Icc
  have hgi : Integrable g := (hbi.const_mul E).add (integrable_finset_sum J hpi)
  have hdom (u : ℝ) : K.indicator f u ≤ g u := by
    by_cases hu : u ∈ K
    · rw [indicator_of_mem hu]
      by_cases haway : ∀ j : ℤ, 1 / 4 ≤ |u - (j : ℝ) * (2 * Real.pi)|
      · have hu0 : 0 < u := by have h := hu.1; change (1 / 2 : ℝ) ≤ u at h; linarith
        have hpw := effective_cluster_spectral_power P Q p ε T hp hε hT hεT hP hQ u
          (by rw [abs_of_pos hu0]; exact hu.2) haway n
        have hmul := mul_le_mul (Real.abs_sinc_le_one (u / 2)) hpw
          (pow_nonneg (norm_nonneg _) _) (by norm_num : (0 : ℝ) ≤ 1)
        have hf : f u ≤ E * back u := by
          dsimp only [f, rawUnitJitterIntegrand, back]
          rw [indicator_of_mem hu, abs_of_pos hu0]
          have hdiv := div_le_div_of_nonneg_right hmul hu0.le
          simpa only [one_mul, div_eq_mul_inv] using hdiv
        exact hf.trans (by dsimp [g]; linarith [Finset.sum_nonneg (fun k (_ : k ∈ J) => hpn k u)])
      · push_neg at haway
        obtain ⟨j, hj⟩ := haway
        obtain ⟨k, hk, huk⟩ := positiveResonanceLabels_cover T u hu j hj
        have hsingle := Finset.single_le_sum (fun i (_ : i ∈ J) => hpn i u) hk
        have hpk : peak k u = f u := indicator_of_mem huk _
        rw [hpk] at hsingle
        exact hsingle.trans (by dsimp [g]; linarith [mul_nonneg hEn (hbn u)])
    · rw [indicator_of_notMem hu]
      exact hgn u
  have hind : Integrable (K.indicator f) := by
    apply hgi.mono' ((rawUnitJitterIntegrand_measurable _ n).indicator measurableSet_Icc).aestronglyMeasurable
    apply ae_of_all
    intro u
    have hnonneg : 0 ≤ K.indicator f u := by
      by_cases hu : u ∈ K
      · rw [indicator_of_mem hu]; exact hfn u
      · rw [indicator_of_notMem hu]
    change ‖K.indicator f u‖ ≤ g u
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hdom u
  have hi : IntegrableOn f K := (integrable_indicator_iff measurableSet_Icc).mp hind
  refine ⟨hi, ?_⟩
  have hback : (∫ u, back u) = Real.log (2 * T) := by
    rw [show back = K.indicator (fun u : ℝ => u⁻¹) by rfl, integral_indicator measurableSet_Icc]
    rw [inverse_interval_integral (1 / 2) T (by norm_num) (by linarith), show T / (1 / 2) = 2 * T by ring]
  have hpeaks : (∑ k ∈ J, ∫ u, peak k u) ≤
      (1 / (2 * (n : ℝ)) + 12 * averageNoiseVariance P Q p * T ^ 2 / (5 * Real.sqrt (n : ℝ))) * (1 + Real.log T) := by
    apply le_trans (Finset.sum_le_sum (fun k hk => ?_))
      (positiveResonanceLabels_sum_budget T _ (by linarith) (averageNoiseVariance_nonneg P Q p hp01) n hn)
    rw [show peak k = (resonanceCell k).indicator f by rfl, integral_indicator (show MeasurableSet (resonanceCell k) from measurableSet_Icc)]
    exact (hkb k hk).2
  have hfull := integral_mono hind hgi hdom
  rw [integral_indicator measurableSet_Icc] at hfull
  have hgint : (∫ u, g u) = E * Real.log (2 * T) + ∑ k ∈ J, ∫ u, peak k u := by
    rw [show g = fun u => E * back u + ∑ k ∈ J, peak k u by rfl,
      integral_add (hbi.const_mul E) (integrable_finset_sum J hpi), integral_const_mul,
      hback, integral_finset_sum J hpi]
  rw [hgint] at hfull
  exact hfull.trans (by linarith only [hpeaks])

theorem rawUnitJitterIntegrand_even (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (u : ℝ) :
    rawUnitJitterIntegrand μ n (-u) = rawUnitJitterIntegrand μ n u := by
  simp only [rawUnitJitterIntegrand, neg_div, Real.sinc_neg, charFun_neg, Complex.norm_conj, abs_neg]

theorem even_annular_integral_and_integrability (f : ℝ → ℝ) (hf : ∀ u, f (-u) = f u)
    (a T : ℝ) (ha : 0 < a) (hi : IntegrableOn f (Icc a T)) :
    IntegrableOn f (abs ⁻¹' Icc a T) ∧
    (∫ u in abs ⁻¹' Icc a T, f u) = 2 * (∫ u in Icc a T, f u) := by
  have hK : MeasurableSet (abs ⁻¹' Icc a T) := measurableSet_Icc.preimage measurable_abs
  have habs (u : ℝ) : f |u| = f u := by
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, hf]
  have he : (abs ⁻¹' Icc a T).indicator f = fun u => (Icc a T).indicator f |u| := by
    funext u
    by_cases hu : |u| ∈ Icc a T
    · rw [indicator_of_mem (show u ∈ abs ⁻¹' Icc a T from hu), indicator_of_mem hu, habs]
    · rw [indicator_of_notMem (show u ∉ abs ⁻¹' Icc a T from hu), indicator_of_notMem hu]
  have hind := integrable_comp_abs_of_integrable _ (hi.integrable_indicator measurableSet_Icc)
  rw [← he] at hind
  refine ⟨(integrable_indicator_iff hK).mp hind, ?_⟩
  rw [← integral_indicator hK, he, integral_comp_abs]
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  rw [show Icc a T ∩ Ioi 0 = Icc a T from inter_eq_left.mpr (fun u hu => ha.trans_le hu.1)]

theorem effective_cluster_high_frequency_integral (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (rawUnitJitterIntegrand (twoClusterMeasure P Q p) n) (abs ⁻¹' Icc (1 / 2) T) ∧
    (∫ u in abs ⁻¹' Icc (1 / 2) T, rawUnitJitterIntegrand (twoClusterMeasure P Q p) n u) ≤
      (1 / (n : ℝ) + 5 * averageNoiseVariance P Q p * T ^ 2 / Real.sqrt (n : ℝ)) * (1 + Real.log T) +
        2 * Real.log (2 * T) * Real.exp (-(n : ℝ) / 200) := by
  have hp01 : p ∈ Icc 0 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  letI := twoClusterMeasure_probability P Q p hp01
  have hpos := effective_cluster_positive_frequency_integral P Q p ε T hp hε hT hεT hP hQ n hn
  have heven := even_annular_integral_and_integrability (rawUnitJitterIntegrand (twoClusterMeasure P Q p) n)
    (rawUnitJitterIntegrand_even _ n) (1 / 2) T (by norm_num) hpos.1
  refine ⟨heven.1, ?_⟩
  rw [heven.2]
  have hs0 := averageNoiseVariance_nonneg P Q p hp01
  have hlog : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg (show 1 ≤ T by linarith)]
  have hc : 2 * (1 / (2 * (n : ℝ)) + 12 * averageNoiseVariance P Q p * T ^ 2 / (5 * Real.sqrt (n : ℝ))) ≤
      1 / (n : ℝ) + 5 * averageNoiseVariance P Q p * T ^ 2 / Real.sqrt (n : ℝ) := by
    apply sub_nonneg.mp
    convert (show 0 ≤ averageNoiseVariance P Q p * T ^ 2 / (5 * Real.sqrt (n : ℝ)) by positivity) using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hc hlog
  nlinarith only [hpos.2, hmul]

end BerryEsseen
