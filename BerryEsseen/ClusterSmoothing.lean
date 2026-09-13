import BerryEsseen.AffineFourier
import BerryEsseen.EffectiveClusterParameters
import BerryEsseen.EffectiveClusterTail

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- The original raw-frequency cut `|u| = 1 / 2`, transported by `t = d * u`.
The two closed pieces only meet at the two endpoints of the low-frequency interval. -/
theorem effective_cluster_frequency_partition (d T : ℝ) (hd : 0 < d) (hT : 1 / 2 ≤ T) :
    Icc (-(d * T)) (d * T) =
      Icc (-(d / 2)) (d / 2) ∪ abs ⁻¹' Icc (d * (1 / 2)) (d * T) := by
  have hcut : d / 2 ≤ d * T := by nlinarith
  ext t
  constructor
  · intro ht
    have hab : |t| ≤ d * T := abs_le.mpr ht
    by_cases hlow : |t| ≤ d / 2
    · exact Or.inl (abs_le.mp hlow)
    · exact Or.inr ⟨by linarith, hab⟩
  · rintro (ht | ht)
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact abs_le.mp ht.2

theorem effective_cluster_frequency_partition_aeDisjoint (d T : ℝ) :
    AEDisjoint volume (Icc (-(d / 2)) (d / 2))
      (abs ⁻¹' Icc (d * (1 / 2)) (d * T)) := by
  change volume (Icc (-(d / 2)) (d / 2) ∩
    (abs ⁻¹' Icc (d * (1 / 2)) (d * T))) = 0
  apply measure_mono_null (t := ({d / 2, -(d / 2)} : Set ℝ))
  · intro t ht
    have hle : |t| ≤ d / 2 := abs_le.mpr ht.1
    have heq : |t| = d / 2 := by have h := ht.2.1; linarith
    rcases le_total 0 t with hpos | hneg
    · have hx : t = d / 2 := by rwa [abs_of_nonneg hpos] at heq
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inl hx
    · have hx : t = -(d / 2) := by rw [abs_of_nonpos hneg] at heq; linarith
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr hx
  · exact (Set.toFinite ({d / 2, -(d / 2)} : Set ℝ)).measure_zero volume

/-- Exact low/high-frequency decomposition, rather than an upper bound from an
overlapping cover. The only common points have Lebesgue measure zero. -/
theorem effective_cluster_frequency_integral_partition (f : ℝ → ℝ) (d T : ℝ)
    (hd : 0 < d) (hT : 1 / 2 ≤ T)
    (hlow : IntegrableOn f (Icc (-(d / 2)) (d / 2)))
    (hhigh : IntegrableOn f (abs ⁻¹' Icc (d * (1 / 2)) (d * T))) :
    IntegrableOn f (Icc (-(d * T)) (d * T)) ∧
      (∫ t in Icc (-(d * T)) (d * T), f t) =
        (∫ t in Icc (-(d / 2)) (d / 2), f t) +
          ∫ t in abs ⁻¹' Icc (d * (1 / 2)) (d * T), f t := by
  rw [effective_cluster_frequency_partition d T hd hT]
  exact ⟨hlow.union hhigh,
    integral_union_ae (effective_cluster_frequency_partition_aeDisjoint d T)
      (measurableSet_Icc.preimage measurable_abs).nullMeasurableSet hlow hhigh⟩

theorem affine_jitterFourierError_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ) (hP : P.measure = standardizedMeasure μ m σ)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    jitterFourierError P n σ⁻¹ t ≤
      rawUnitJitterIntegrand μ n (t / (σ * Real.sqrt (n : ℝ))) / (σ * Real.sqrt (n : ℝ)) +
        edgeworthTailIntegrand n (signedThirdMoment P) t := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hnorm : ‖charFun (normalizedJitteredSumLaw P n σ⁻¹) t‖ / |t| =
      rawUnitJitterIntegrand μ n (t / (σ * Real.sqrt (n : ℝ))) / (σ * Real.sqrt (n : ℝ)) := by
    rw [charFun_normalizedJitteredSumLaw P n σ⁻¹ (inv_pos.mpr hσ).le, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, hP, charFun_standardizedMeasure_norm]
    rw [show σ⁻¹ * (t / Real.sqrt (n : ℝ)) / 2 = (t / (σ * Real.sqrt (n : ℝ))) / 2 by ring,
      show (t / Real.sqrt (n : ℝ)) / σ = t / (σ * Real.sqrt (n : ℝ)) by ring]
    unfold rawUnitJitterIntegrand
    rw [abs_div, abs_of_pos (mul_pos hσ hr)]
    field_simp
  have h := div_le_div_of_nonneg_right
    (norm_sub_le (charFun (normalizedJitteredSumLaw P n σ⁻¹) t) (edgeworthChar n (signedThirdMoment P) t)) (abs_nonneg t)
  rw [add_div, hnorm] at h
  exact h

theorem effective_cluster_fourier_integral (P Q : CenteredFourthLaw) (p ε T : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hp01 : p ∈ Ioo 0 1)
    (hε : 0 ≤ ε) (hT : 10 ≤ T) (hεT : ε ≤ (100 * T)⁻¹)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 2 ≤ n) :
    let Z := standardizedTwoClusterLaw P Q p hp01
    let σ := Real.sqrt (clusterVariance P Q p)
    let L := σ * Real.sqrt (n : ℝ) * T
    IntegrableOn (jitterFourierError Z n σ⁻¹) (Icc (-L) L) ∧
    (∫ t in Icc (-L) L, jitterFourierError Z n σ⁻¹ t) ≤
      7 / (n : ℝ) +
      (1 / (n : ℝ) + 5 * averageNoiseVariance P Q p * T ^ 2 / Real.sqrt (n : ℝ)) * (1 + Real.log T) +
      2 * Real.log (2 * T) * Real.exp (-(n : ℝ) / 200) + 20 * Real.exp (-3 * (n : ℝ) / 100) := by
  let Z := standardizedTwoClusterLaw P Q p hp01
  let σ := Real.sqrt (clusterVariance P Q p)
  let r := Real.sqrt (n : ℝ)
  let d := σ * r
  let L := d * T
  let A := Icc (-(d / 2)) (d / 2)
  let B : Set ℝ := abs ⁻¹' Icc (d * (1 / 2)) (d * T)
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  letI := twoClusterMeasure_probability P Q p hpcc
  have hεb : ε ∈ Icc 0 0.001 := ⟨hε, effective_noise_amplitude_bound ε T hε hT hεT⟩
  have hsb := effective_cluster_scale_bounds P Q p ε hp hεb hP hQ
  have hσ : 0 < σ := by have h := hsb.1.1; change (0.48 : ℝ) ≤ σ at h; linarith
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hd : 0 < d := mul_pos hσ hr
  have hn1 : 1 ≤ n := by omega
  have hβ : thirdMoment Z ≤ 1.84 := effective_standardized_cluster_moment P Q p ε hp hεb hP hQ hp01
  have hb : ∀ᵐ x ∂Z.measure, |x| ≤ 6 := by
    filter_upwards [effective_standardized_cluster_bound P Q p ε hp hεb hP hQ hp01] with x hx
    linarith
  have hlowFulli := effectiveJitterLowFrequencyIntegral_integrable Z hβ hb n hn σ⁻¹ (inv_pos.mpr hσ).le
  have hlowFull := effectiveJitterLowFrequencyIntegral_bound Z hβ hb n hn σ⁻¹ (inv_pos.mpr hσ).le hsb.2
  have hAsub : A ⊆ effectiveLowFrequencyRange n := by
    have hdr : d ≤ r := by
      have h := mul_le_mul_of_nonneg_right hsb.1.2 hr.le
      simpa only [one_mul] using h
    intro t ht
    change -(r / 2) ≤ t ∧ t ≤ r / 2
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlowi : IntegrableOn (jitterFourierError Z n σ⁻¹) A := hlowFulli.mono_set hAsub
  have hlow : (∫ t in A, jitterFourierError Z n σ⁻¹ t) ≤ 7 / (n : ℝ) := by
    exact (setIntegral_mono_set hlowFulli
      (ae_of_all _ (jitterFourierError_nonneg Z n σ⁻¹))
      (ae_of_all _ (fun t ht => hAsub ht))).trans hlowFull
  have hraw := effective_cluster_high_frequency_integral P Q p ε T hp hε hT hεT hP hQ n hn1
  have hscaled := scaled_annular_integral (rawUnitJitterIntegrand (twoClusterMeasure P Q p) n) (1 / 2) T d hd hraw.1
  have hB : MeasurableSet B := measurableSet_Icc.preimage measurable_abs
  have hBsub : B ⊆ {t : ℝ | d / 2 ≤ |t|} := by
    intro t ht
    have h := ht.1
    change d * (1 / 2) ≤ |t| at h
    change d / 2 ≤ |t|
    linarith
  have htaili := edgeworthTailIntegrand_integrable_tail n (signedThirdMoment Z) (d / 2) (by positivity)
  have htailiB := htaili.mono_set hBsub
  have hpoint (t : ℝ) : jitterFourierError Z n σ⁻¹ t ≤
      rawUnitJitterIntegrand (twoClusterMeasure P Q p) n (t / d) / d + edgeworthTailIntegrand n (signedThirdMoment Z) t :=
    affine_jitterFourierError_bound (twoClusterMeasure P Q p) Z p σ hσ rfl n hn1 t
  have hhighi : IntegrableOn (jitterFourierError Z n σ⁻¹) B := by
    apply (hscaled.1.add htailiB).mono' (jitterFourierError_measurable Z n σ⁻¹).aestronglyMeasurable
    exact ae_of_all _ (fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (jitterFourierError_nonneg Z n σ⁻¹ t)]; exact hpoint t)
  have hκ : |signedThirdMoment Z| ≤ 1.84 := (signedThirdMoment_abs_le Z).trans hβ
  have hσ2 : (0.24 : ℝ) ≤ σ ^ 2 := by
    dsimp [σ]
    rw [Real.sq_sqrt (clusterVariance_pos P Q p hp01).le]
    exact (effective_cluster_variance_bounds P Q p ε hp hεb hP hQ).1
  have htail := effective_cluster_gaussian_tail n hn (signedThirdMoment Z) σ hκ hsb.1.1 hsb.1.2 hσ2
  have hhigh : (∫ t in B, jitterFourierError Z n σ⁻¹ t) ≤
      (1 / (n : ℝ) + 5 * averageNoiseVariance P Q p * T ^ 2 / r) * (1 + Real.log T) +
        2 * Real.log (2 * T) * Real.exp (-(n : ℝ) / 200) + 20 * Real.exp (-3 * (n : ℝ) / 100) := by
    calc
      _ ≤ ∫ t in B, (rawUnitJitterIntegrand (twoClusterMeasure P Q p) n (t / d) / d +
          edgeworthTailIntegrand n (signedThirdMoment Z) t) :=
        integral_mono hhighi (hscaled.1.add htailiB) hpoint
      _ = (∫ u in abs ⁻¹' Icc (1 / 2) T, rawUnitJitterIntegrand (twoClusterMeasure P Q p) n u) +
          ∫ t in B, edgeworthTailIntegrand n (signedThirdMoment Z) t := by
        rw [integral_add hscaled.1 htailiB, hscaled.2]
      _ ≤ (∫ u in abs ⁻¹' Icc (1 / 2) T, rawUnitJitterIntegrand (twoClusterMeasure P Q p) n u) +
          ∫ t in {t : ℝ | d / 2 ≤ |t|}, edgeworthTailIntegrand n (signedThirdMoment Z) t := by
        apply add_le_add le_rfl
        exact setIntegral_mono_set htaili (ae_of_all _ (edgeworthTailIntegrand_nonneg n (signedThirdMoment Z)))
          (ae_of_all _ (fun t ht => hBsub ht))
      _ ≤ _ := add_le_add hraw.2 htail
  have hsplit := effective_cluster_frequency_integral_partition
    (jitterFourierError Z n σ⁻¹) d T hd (by linarith) hlowi hhighi
  refine ⟨hsplit.1, ?_⟩
  change (∫ t in Icc (-L) L, jitterFourierError Z n σ⁻¹ t) ≤ _
  linarith only [hsplit.2, hlow, hhigh]

end BerryEsseen
