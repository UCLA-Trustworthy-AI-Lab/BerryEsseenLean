import BerryEsseen.GlobalFrequencyIntegral
import BerryEsseen.GlobalJitterLowFrequency
import BerryEsseen.ClusterSmoothing

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def globalFourierBudget (n : ℕ) (d T g : ℝ) : ℝ :=
  11 / (n : ℝ) + 12 * (1 + Real.log T) * (1 / (n : ℝ) + d / Real.sqrt (n : ℝ)) +
    2 * Real.log (2 * T) * Real.exp (-(n : ℝ) * g) + 5 * Real.exp (-(n : ℝ) / 8)

theorem normalized_jitterFourierError_bound (P : StandardizedLaw) (h : ℝ) (hh : 0 ≤ h)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    jitterFourierError P n h t ≤
      rawJitterFourierIntegrand P n h (t / Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) +
        edgeworthTailIntegrand n (signedThirdMoment P) t := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hnorm : ‖charFun (normalizedJitteredSumLaw P n h) t‖ / |t| =
      rawJitterFourierIntegrand P n h (t / Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) := by
    rw [charFun_normalizedJitteredSumLaw P n h hh, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
    unfold rawJitterFourierIntegrand
    rw [abs_div, abs_of_pos hr]
    field_simp
  have htri := div_le_div_of_nonneg_right
    (norm_sub_le (charFun (normalizedJitteredSumLaw P n h) t) (edgeworthChar n (signedThirdMoment P) t)) (abs_nonneg t)
  rw [add_div, hnorm] at htri
  exact htri

theorem global_fourier_integral (P : StandardizedLaw) (h T d g : ℝ)
    (hh : h ∈ Ioc 0 5) (hT : 10 ≤ T) (hd : 0 ≤ d)
    (hβ : thirdMoment P ≤ 1.84) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 6)
    (hgap : ∀ u : ℝ, |u| ≤ T →
      1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) → ‖charFun P.measure u‖ ≤ 1 - g)
    (hpeaks : ∀ j : ℤ, j ≠ 0 → |(j : ℝ) * (2 * Real.pi / h)| ≤ T + 1 / 1000 →
      ∃ m : ℝ, |m - (j : ℝ) * (2 * Real.pi / h)| ≤ d ∧
        ∀ u ∈ globalResonanceCell h j, ∀ n : ℕ, ‖charFun P.measure u‖ ^ n ≤ globalPeakGaussian n m u)
    (n : ℕ) (hn : 2 ≤ n) :
    let L := Real.sqrt (n : ℝ) * T
    IntegrableOn (jitterFourierError P n h) (Icc (-L) L) ∧
      (∫ t in Icc (-L) L, jitterFourierError P n h t) ≤ globalFourierBudget n d T g := by
  let r := Real.sqrt (n : ℝ)
  let L := r * T
  let A := effectiveLowFrequencyRange n
  let B : Set ℝ := abs ⁻¹' Icc (r * (1 / 2)) (r * T)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hn1 : 1 ≤ n := by omega
  have hlowi := effectiveJitterLowFrequencyIntegral_integrable P hβ hb n hn h hh.1.le
  have hlow := globalJitterLowFrequencyIntegral_bound P hβ hb n hn h hh.1.le
    (by nlinarith [hh.1, hh.2])
  have hraw := global_high_frequency_integral P h T d g hh hT hd hgap hpeaks n hn1
  have hscaled := scaled_annular_integral (rawJitterFourierIntegrand P n h) (1 / 2) T r hr hraw.1
  have hB : MeasurableSet B := measurableSet_Icc.preimage measurable_abs
  have hBsub : B ⊆ {t : ℝ | r / 2 ≤ |t|} := by
    intro t ht
    have h := ht.1
    change r * (1 / 2) ≤ |t| at h
    change r / 2 ≤ |t|
    linarith
  have htaili := edgeworthTailIntegrand_integrable_tail n (signedThirdMoment P) (r / 2) (by positivity)
  have htailiB := htaili.mono_set hBsub
  have hpoint (t : ℝ) : jitterFourierError P n h t ≤
      rawJitterFourierIntegrand P n h (t / r) / r + edgeworthTailIntegrand n (signedThirdMoment P) t :=
    normalized_jitterFourierError_bound P h hh.1.le n hn1 t
  have hhighi : IntegrableOn (jitterFourierError P n h) B := by
    apply (hscaled.1.add htailiB).mono' (jitterFourierError_measurable P n h).aestronglyMeasurable
    exact ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (jitterFourierError_nonneg P n h t)]
      exact hpoint t)
  have htail := effective_edgeworth_gaussian_tail n hn (signedThirdMoment P) ((signedThirdMoment_abs_le P).trans hβ)
  have hhigh : (∫ t in B, jitterFourierError P n h t) ≤
      2 * Real.log (2 * T) * Real.exp (-(n : ℝ) * g) +
      12 * (1 + Real.log T) * (1 / (n : ℝ) + d / r) + 5 * Real.exp (-(n : ℝ) / 8) := by
    calc
      _ ≤ ∫ t in B, (rawJitterFourierIntegrand P n h (t / r) / r +
          edgeworthTailIntegrand n (signedThirdMoment P) t) :=
        integral_mono hhighi (hscaled.1.add htailiB) hpoint
      _ = (∫ u in abs ⁻¹' Icc (1 / 2) T, rawJitterFourierIntegrand P n h u) +
          ∫ t in B, edgeworthTailIntegrand n (signedThirdMoment P) t := by
        rw [integral_add hscaled.1 htailiB, hscaled.2]
      _ ≤ (∫ u in abs ⁻¹' Icc (1 / 2) T, rawJitterFourierIntegrand P n h u) +
          ∫ t in {t : ℝ | r / 2 ≤ |t|}, edgeworthTailIntegrand n (signedThirdMoment P) t := by
        apply add_le_add le_rfl
        exact setIntegral_mono_set htaili (ae_of_all _ (edgeworthTailIntegrand_nonneg n (signedThirdMoment P)))
          (ae_of_all _ (fun t ht => hBsub ht))
      _ ≤ _ := add_le_add hraw.2 htail
  have hcover : Icc (-L) L ⊆ A ∪ B := by
    intro t ht
    have hab : |t| ≤ L := abs_le.mpr ht
    by_cases hlow : |t| ≤ r / 2
    · exact Or.inl (abs_le.mp hlow)
    · exact Or.inr ⟨by change r * (1 / 2) ≤ |t|; linarith, hab⟩
  have hfulli : IntegrableOn (jitterFourierError P n h) (Icc (-L) L) :=
    (hlowi.union hhighi).mono_set hcover
  have hfull := integral_le_add_of_cover (jitterFourierError P n h) (Icc (-L) L) A B
    measurableSet_Icc measurableSet_Icc hB (jitterFourierError_nonneg P n h) hlowi hhighi hcover
  refine ⟨hfulli, ?_⟩
  change (∫ t in Icc (-L) L, jitterFourierError P n h t) ≤ _
  unfold globalFourierBudget
  linarith only [hfull, hlow, hhigh]

end BerryEsseen
