import BerryEsseen.SmoothingApplicationMoments
import BerryEsseen.JitterFourierIntegrability
import BerryEsseen.EdgeworthDensityFourier

/-! The actual uniform CDF expansion for the bounded extremizer class.
The smoothing interface is instantiated by the manuscript's proved Lemma 2.1.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def jitterCDFError (P : StandardizedLaw) (n : ℕ) (h x : ℝ) : ℝ :=
  ((normalizedJitteredSumLaw P n h) (Iic x)).toReal - edgeworthCDF n (signedThirdMoment P) x

theorem actual_jitter_smoothing_bound (S : PublishedSignedSmoothing)
    (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (h : ℝ) (hh : 0 ≤ h) (L : ℝ) (hL : 0 < L) (x : ℝ) :
    |jitterCDFError P n h x| ≤ (1 / 4) *
      (∫ t in Icc (-L) L, jitterFourierError P n h t) + (24) * (7 * phi0) / L := by
  have hg : ∀ x, |edgeworthDensity n (signedThirdMoment P) x| ≤ 7 * phi0 := by
    intro x
    simpa only [show (1 + 3 * 2 : ℝ) = 7 by norm_num] using edgeworthDensity_uniform_bound n (by omega) (signedThirdMoment P) 2
      ((signedThirdMoment_abs_le P).trans hβ) x
  have hi : IntegrableOn (fun t => ‖charFun (normalizedJitteredSumLaw P n h) t -
      densityFourier (edgeworthDensity n (signedThirdMoment P)) t‖ / |t|) (Icc (-L) L) := by
    simpa only [edgeworthDensity_fourier, jitterFourierError] using
      jitterFourierError_integrableOn P n hn hβ hb h hh L
  have hbnd := S.bound (normalizedJitteredSumLaw P n h) (normalizedJitteredSumLaw_probability P n h)
    (normalizedJitteredSumLaw_first_integrable P n h)
    (edgeworthDensity n (signedThirdMoment P)) (edgeworthDensity_integrable _ _) (edgeworthDensity_first_integrable _ _) (edgeworthDensity_mass_one _ _)
    (7 * phi0) L (mul_pos (by norm_num) phi0_pos) hL hg hi x
  simpa only [← edgeworthCDF_cumulative, edgeworthDensity_fourier, jitterCDFError, jitterFourierError] using hbnd

theorem bounded_jitter_uniform_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : 0 ≤ h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0) :
    TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  let C := (24) * (7 * phi0)
  have htail : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨T, hT, hTC⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (htail.eventually (gt_mem_nhds (by linarith : 0 < ε / 2)))).exists
  have hI := (bounded_compact_jitterFourier_tendsto_zero W P Q hw hβ hb n hn hn2 h hh hzero T hT.le).const_mul (1 / 4)
  simp only [mul_zero] at hI
  filter_upwards [hI.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hj
  intro x
  have hnpos : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by have := hn2 j; omega)
  have hs : 0 < Real.sqrt (n j : ℝ) := Real.sqrt_pos.2 hnpos
  have hsm := actual_jitter_smoothing_bound S (P j) (n j) (hn2 j) (hβ j) (hb j) h hh
    (T * Real.sqrt (n j : ℝ)) (mul_pos hT hs) x
  have hbnd := mul_le_mul_of_nonneg_left hsm hs.le
  have he : Real.sqrt (n j : ℝ) * ((1 / 4) *
      (∫ t in Icc (-(T * Real.sqrt (n j : ℝ))) (T * Real.sqrt (n j : ℝ)),
        jitterFourierError (P j) (n j) h t) + C / (T * Real.sqrt (n j : ℝ))) =
      (1 / 4) * (Real.sqrt (n j : ℝ) *
        ∫ t in Icc (-T * Real.sqrt (n j : ℝ)) (T * Real.sqrt (n j : ℝ)),
          jitterFourierError (P j) (n j) h t) + C / T := by
    rw [neg_mul]
    field_simp [hs.ne', hT.ne']
    <;> ring
  change Real.sqrt (n j : ℝ) * |jitterCDFError (P j) (n j) h x| ≤ _ at hbnd
  rw [he] at hbnd
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_mul, abs_of_pos hs]
  linarith

theorem exists_maximal_span_bounded_jitter_expansion (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j) :
    ∃ h : ℝ, 0 ≤ h ∧ (0 < h → IsLatticeSpan Q.measure h) ∧
      (∀ d, IsLatticeSpan Q.measure d → d ≤ h) ∧
      TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
        (fun _ => 0) atTop := by
  obtain ⟨h, hh, hspan, hmax, hz⟩ := manuscript_exists_span_and_resonance_multiplier Q
  refine ⟨h, hh, hspan, hmax, bounded_jitter_uniform_expansion W S P Q hw hβ hb n hn hn2 h hh ?_⟩
  intro r hr hres
  exact hz r hr ((mem_resonanceSubgroup_iff Q.measure r).1 hres)

end BerryEsseen
