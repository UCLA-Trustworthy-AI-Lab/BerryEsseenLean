import BerryEsseen.GlobalResonanceLabels

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem global_positive_frequency_integral (P : StandardizedLaw) (h T d g₀ : ℝ)
    (hh : h ∈ Ioc 0 5) (hT : 10 ≤ T) (hd : 0 ≤ d)
    (hgap : ∀ u : ℝ, |u| ≤ T →
      1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) → ‖charFun P.measure u‖ ≤ 1 - g₀)
    (hpeaks : ∀ j : ℤ, j ≠ 0 → |(j : ℝ) * (2 * Real.pi / h)| ≤ T + 1 / 1000 →
      ∃ m : ℝ, |m - (j : ℝ) * (2 * Real.pi / h)| ≤ d ∧
        ∀ u ∈ globalResonanceCell h j, ∀ n : ℕ, ‖charFun P.measure u‖ ^ n ≤ globalPeakGaussian n m u)
    (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (rawJitterFourierIntegrand P n h) (Icc (1 / 2) T) ∧
    (∫ u in Icc (1 / 2) T, rawJitterFourierIntegrand P n h u) ≤
      Real.exp (-(n : ℝ) * g₀) * Real.log (2 * T) +
      6 * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) * (1 + Real.log T) := by
  classical
  have hh0 := hh.1
  let f := rawJitterFourierIntegrand P n h
  let K : Set ℝ := Icc (1 / 2) T
  let J := globalPositiveResonanceLabels h T
  let E := Real.exp (-(n : ℝ) * g₀)
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  let back : ℝ → ℝ := K.indicator (fun u : ℝ => u⁻¹)
  let peak : ℕ → ℝ → ℝ := fun k => (globalResonanceCell h (k : ℤ)).indicator f
  let g : ℝ → ℝ := fun u => E * back u + ∑ k ∈ J, peak k u
  have hfn (u : ℝ) : 0 ≤ f u := rawJitterFourierIntegrand_nonneg P n h _
  have hpn (k : ℕ) (u : ℝ) : 0 ≤ peak k u := by
    dsimp [peak]
    by_cases hu : u ∈ globalResonanceCell h (k : ℤ)
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
  have hkb (k : ℕ) (hk : k ∈ J) : IntegrableOn f (globalResonanceCell h (k : ℤ)) ∧
      (∫ u in globalResonanceCell h (k : ℤ), f u) ≤ (6 / (k : ℝ)) * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) := by
    have hkprops := globalPositiveResonanceLabels_properties h T k hk
    have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hkr : |((k : ℤ) : ℝ) * (2 * Real.pi / h)| ≤ T + 1 / 1000 := by
      simpa only [Int.cast_natCast, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) * (2 * Real.pi / h))] using hkprops.2.2
    obtain ⟨m, hshift, henv⟩ := hpeaks (k : ℤ) hkZ hkr
    have hi := globalJitter_peak_integral P h hh n hn (k : ℤ) hkZ m d hd hshift (fun u hu => henv u hu n)
    simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k), f] using hi
  have hpi (k : ℕ) (hk : k ∈ J) : Integrable (peak k) :=
    (hkb k hk).1.integrable_indicator measurableSet_Icc
  have hbi : Integrable back := (inverse_interval_integrable (1 / 2) T (by norm_num)).integrable_indicator measurableSet_Icc
  have hgi : Integrable g := (hbi.const_mul E).add (integrable_finset_sum J hpi)
  have hdom (u : ℝ) : K.indicator f u ≤ g u := by
    by_cases hu : u ∈ K
    · rw [indicator_of_mem hu]
      by_cases haway : ∀ j : ℤ, 1 / 1000 ≤ |u - (j : ℝ) * (2 * Real.pi / h)|
      · have hu0 : 0 < u := by have h := hu.1; change (1 / 2 : ℝ) ≤ u at h; linarith
        have hpw : ‖charFun P.measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * g₀) := by
          have hs := hgap u (by rw [abs_of_pos hu0]; exact hu.2) (global_nonresonance_distance h u haway)
          have hcf : ‖charFun P.measure u‖ ≤ Real.exp (-g₀) := by linarith [Real.add_one_le_exp (-g₀)]
          have hp := pow_le_pow_left₀ (norm_nonneg _) hcf n
          rw [← Real.exp_nat_mul] at hp
          convert hp using 1 <;> congr 1 <;> ring
        have hmul := mul_le_mul (Real.abs_sinc_le_one (h * u / 2)) hpw
          (pow_nonneg (norm_nonneg _) _) (by norm_num : (0 : ℝ) ≤ 1)
        have hf : f u ≤ E * back u := by
          dsimp only [f, rawJitterFourierIntegrand, back]
          rw [indicator_of_mem hu, abs_of_pos hu0]
          have hdiv := div_le_div_of_nonneg_right hmul hu0.le
          simpa only [one_mul, div_eq_mul_inv] using hdiv
        exact hf.trans (by dsimp [g]; linarith [Finset.sum_nonneg (fun k (_ : k ∈ J) => hpn k u)])
      · push_neg at haway
        obtain ⟨j, hj⟩ := haway
        obtain ⟨k, hk, huk⟩ := globalPositiveResonanceLabels_cover h T u hh hu j hj
        have hsingle := Finset.single_le_sum (fun i (_ : i ∈ J) => hpn i u) hk
        have hpk : peak k u = f u := indicator_of_mem huk _
        rw [hpk] at hsingle
        exact hsingle.trans (by dsimp [g]; linarith [mul_nonneg hEn (hbn u)])
    · rw [indicator_of_notMem hu]
      exact hgn u
  have hind : Integrable (K.indicator f) := by
    apply hgi.mono' ((rawJitterFourierIntegrand_measurable P n h).indicator measurableSet_Icc).aestronglyMeasurable
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
  have hsumpeaks : (∑ k ∈ J, ∫ u, peak k u) ≤
      6 * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) * (1 + Real.log T) := by
    calc
      _ ≤ ∑ k ∈ J, (6 / (k : ℝ)) * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [show peak k = (globalResonanceCell h (k : ℤ)).indicator f by rfl,
          integral_indicator (show MeasurableSet (globalResonanceCell h (k : ℤ)) from measurableSet_Icc)]
        exact (hkb k hk).2
      _ = 6 * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) * (∑ k ∈ J, (k : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (globalPositiveResonanceLabels_harmonic h T (by linarith)) (by positivity)
  have hfull := integral_mono hind hgi hdom
  rw [integral_indicator measurableSet_Icc] at hfull
  have hgint : (∫ u, g u) = E * Real.log (2 * T) + ∑ k ∈ J, ∫ u, peak k u := by
    rw [show g = fun u => E * back u + ∑ k ∈ J, peak k u by rfl,
      integral_add (hbi.const_mul E) (integrable_finset_sum J hpi), integral_const_mul,
      hback, integral_finset_sum J hpi]
  rw [hgint] at hfull
  exact hfull.trans (by linarith only [hsumpeaks])

theorem rawJitterFourierIntegrand_even (P : StandardizedLaw) (n : ℕ) (h u : ℝ) :
    rawJitterFourierIntegrand P n h (-u) = rawJitterFourierIntegrand P n h u := by
  simp only [rawJitterFourierIntegrand, mul_neg, neg_div, Real.sinc_neg,
    charFun_neg, Complex.norm_conj, abs_neg]

theorem global_high_frequency_integral (P : StandardizedLaw) (h T d g₀ : ℝ)
    (hh : h ∈ Ioc 0 5) (hT : 10 ≤ T) (hd : 0 ≤ d)
    (hgap : ∀ u : ℝ, |u| ≤ T →
      1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) → ‖charFun P.measure u‖ ≤ 1 - g₀)
    (hpeaks : ∀ j : ℤ, j ≠ 0 → |(j : ℝ) * (2 * Real.pi / h)| ≤ T + 1 / 1000 →
      ∃ m : ℝ, |m - (j : ℝ) * (2 * Real.pi / h)| ≤ d ∧
        ∀ u ∈ globalResonanceCell h j, ∀ n : ℕ, ‖charFun P.measure u‖ ^ n ≤ globalPeakGaussian n m u)
    (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (rawJitterFourierIntegrand P n h) (abs ⁻¹' Icc (1 / 2) T) ∧
    (∫ u in abs ⁻¹' Icc (1 / 2) T, rawJitterFourierIntegrand P n h u) ≤
      2 * Real.log (2 * T) * Real.exp (-(n : ℝ) * g₀) +
      12 * (1 + Real.log T) * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) := by
  have hpos := global_positive_frequency_integral P h T d g₀ hh hT hd hgap hpeaks n hn
  have heven := even_annular_integral_and_integrability (rawJitterFourierIntegrand P n h)
    (rawJitterFourierIntegrand_even P n h) (1 / 2) T (by norm_num) hpos.1
  refine ⟨heven.1, ?_⟩
  rw [heven.2]
  nlinarith only [hpos.2]

end BerryEsseen
