import BerryEsseen.ManuscriptLatticeAtoms

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem conditional_integral_real (μ : Measure ℝ) (s : Set ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂ProbabilityTheory.cond μ s) = (∫ x in s, f x ∂μ) / μ.real s := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul, Measure.real]
  ring

theorem conditional_integrable_real (μ : Measure ℝ) (s : Set ℝ)
    (hs : μ s ≠ 0) (f : ℝ → ℝ) (hf : Integrable f μ) :
    Integrable f (ProbabilityTheory.cond μ s) :=
  hf.restrict.smul_measure (by simpa using hs)

theorem raw_centered_variance_formula (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h1 : Integrable (fun x : ℝ => x) μ) (h2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    rawStdDev μ ^ 2 = (∫ x, x ^ 2 ∂μ) - rawMean μ ^ 2 := by
  have hnonneg : 0 ≤ ∫ x, (x - rawMean μ) ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  rw [rawStdDev, Real.sq_sqrt hnonneg]
  have he : (fun x : ℝ => (x - rawMean μ) ^ 2) =
      (fun x : ℝ => x ^ 2 - 2 * rawMean μ * x + rawMean μ ^ 2) := by funext x; ring
  rw [he]
  have hi : Integrable (fun x : ℝ => x ^ 2 - 2 * rawMean μ * x) μ :=
    h2.sub (h1.const_mul (2 * rawMean μ))
  rw [integral_add hi (integrable_const _), integral_sub h2 (h1.const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change _ - 2 * rawMean μ * rawMean μ + rawMean μ ^ 2 = _
  ring

theorem outside_moment_comparison (P : StandardizedLaw) (s : Set ℝ) (hs : MeasurableSet s)
    (hx : ∀ᵐ x ∂P.measure, x ∈ sᶜ → 1 ≤ |x|) :
    P.measure.real sᶜ ≤ ∫ x in sᶜ, |x| ∂P.measure ∧
      (∫ x in sᶜ, |x| ∂P.measure) ≤ ∫ x in sᶜ, x ^ 2 ∂P.measure ∧
      |∫ x in sᶜ, x ∂P.measure| ≤ ∫ x in sᶜ, |x| ∂P.measure := by
  have hax : ∀ᵐ x ∂P.measure.restrict sᶜ, 1 ≤ |x| := by
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem hs.compl] with x hx hxs
    exact hx hxs
  refine ⟨?_, ?_, ?_⟩
  · have h := integral_mono_ae (integrable_const (1 : ℝ)) P.first_integrable.abs.restrict hax
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using h
  · apply integral_mono_ae P.first_integrable.abs.restrict P.second_integrable.restrict
    filter_upwards [hax] with x hx
    nlinarith [sq_abs x]
  · simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x : ℝ => x) (μ := P.measure.restrict sᶜ)

theorem conditional_small_outside_moments (P : StandardizedLaw) (s : Set ℝ)
    (hs : MeasurableSet s) (δ : ℝ) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hr : P.measure.real sᶜ ≤ δ)
    (hfirst : |∫ x in sᶜ, x ∂P.measure| ≤ δ)
    (hsecond : (∫ x in sᶜ, x ^ 2 ∂P.measure) ≤ δ) :
    P.measure s ≠ 0 ∧
      |rawMean (ProbabilityTheory.cond P.measure s)| ≤ 2 * δ ∧
      |rawStdDev (ProbabilityTheory.cond P.measure s) ^ 2 - 1| ≤ 5 * δ := by
  have hmass : P.measure.real s = 1 - P.measure.real sᶜ := by
    rw [probReal_compl_eq_one_sub hs]
    ring
  have hmasslo : 1 / 2 ≤ P.measure.real s := by
    rw [hmass]
    linarith [hδ.2]
  have hmasspos : 0 < P.measure.real s := by linarith
  have hsnonzero : P.measure s ≠ 0 := by
    intro he
    have hz : P.measure.real s = 0 := by simp [Measure.real, he]
    linarith
  let ν := ProbabilityTheory.cond P.measure s
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hsnonzero
  have hν1 : Integrable (fun x : ℝ => x) ν := conditional_integrable_real _ _ hsnonzero _ P.first_integrable
  have hν2 : Integrable (fun x : ℝ => x ^ 2) ν := conditional_integrable_real _ _ hsnonzero _ P.second_integrable
  have hm : rawMean ν = -(∫ x in sᶜ, x ∂P.measure) / P.measure.real s := by
    rw [rawMean, conditional_integral_real]
    have hi := integral_add_compl hs P.first_integrable
    rw [P.mean_zero] at hi
    congr 1
    linarith only [hi]
  have h2 : (∫ x, x ^ 2 ∂ν) = (1 - ∫ x in sᶜ, x ^ 2 ∂P.measure) / P.measure.real s := by
    rw [conditional_integral_real]
    have hi := integral_add_compl hs P.second_integrable
    rw [P.second_one] at hi
    congr 1
    linarith only [hi]
  have hmabs : |rawMean ν| ≤ 2 * δ := by
    rw [hm, abs_div, abs_neg, abs_of_pos hmasspos]
    apply (div_le_iff₀ hmasspos).mpr
    nlinarith [hδ.1]
  refine ⟨hsnonzero, hmabs, ?_⟩
  have hs20 : 0 ≤ ∫ x in sᶜ, x ^ 2 ∂P.measure := integral_nonneg (fun _ => sq_nonneg _)
  have hr0 : 0 ≤ P.measure.real sᶜ := measureReal_nonneg
  have h2err : |(∫ x, x ^ 2 ∂ν) - 1| ≤ 2 * δ := by
    rw [h2, abs_le]
    constructor
    · have hh : (1 - 2 * δ) * P.measure.real s ≤ 1 - ∫ x in sᶜ, x ^ 2 ∂P.measure := by
        rw [hmass]
        nlinarith [hδ.1, hδ.2]
      have hg := (le_div_iff₀ hmasspos).mpr hh
      linarith
    · have hh : 1 - ∫ x in sᶜ, x ^ 2 ∂P.measure ≤ (1 + 2 * δ) * P.measure.real s := by
        rw [hmass]
        nlinarith [hδ.1, hδ.2]
      have hg := (div_le_iff₀ hmasspos).mpr hh
      linarith
  have hm2 : rawMean ν ^ 2 ≤ 4 * δ ^ 2 := by
    have hp := mul_self_le_mul_self (abs_nonneg (rawMean ν)) hmabs
    nlinarith [sq_abs (rawMean ν)]
  change |rawStdDev ν ^ 2 - 1| ≤ 5 * δ
  rw [raw_centered_variance_formula ν hν1 hν2, abs_le]
  have h2lo := (abs_le.mp h2err).1
  have h2hi := (abs_le.mp h2err).2
  constructor <;> nlinarith [hδ.1, hδ.2, sq_nonneg (rawMean ν)]

theorem effective_lattice_conditioning (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧
      (∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) ∧
      P.measure {-a, b} ≠ 0 ∧
      P.measure.real ({-a, b}ᶜ : Set ℝ) ≤ δ ∧
      (∫ x in ({-a, b}ᶜ : Set ℝ), |x| ∂P.measure) ≤ δ ∧
      (∫ x in ({-a, b}ᶜ : Set ℝ), x ^ 2 ∂P.measure) ≤ δ ∧
      |rawMean (ProbabilityTheory.cond P.measure {-a, b})| ≤ 2 * δ ∧
      |rawStdDev (ProbabilityTheory.cond P.measure {-a, b}) ^ 2 - 1| ≤ 5 * δ := by
  obtain ⟨a, b, ha, hb, hab, hgeom, hnegative, hpositive, hmaximal, hs2⟩ :=
    manuscript_effective_lattice_bracket P h δ hlat hβ hκ hD hδ
  have hset : MeasurableSet ({-a, b} : Set ℝ) := (measurableSet_singleton b).insert (-a)
  rw [integral_indicator hset.compl] at hs2
  have hh := (effective_lattice_span_bounds P h δ hβ hD hδ).1
  have hout : ∀ᵐ x ∂P.measure, x ∈ ({-a, b}ᶜ : Set ℝ) → 1 ≤ |x| := by
    filter_upwards [hgeom] with x hx
    intro hs
    have hne : x ≠ -a ∧ x ≠ b := by simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using hs
    rcases hx with hx | hx | hx | hx
    · exact False.elim (hne.1 hx)
    · exact False.elim (hne.2 hx)
    · rw [abs_of_neg (by linarith : x < 0)]
      linarith
    · exact (show 1 ≤ x by linarith).trans (le_abs_self x)
  have hcomp := outside_moment_comparison P {-a, b} hset hout
  have hs1 := hcomp.2.1.trans hs2
  have hr := hcomp.1.trans hs1
  have hc := conditional_small_outside_moments P {-a, b} hset δ ⟨hD.1.trans hD.2, hδ⟩
    hr (hcomp.2.2.trans hs1) hs2
  exact ⟨a, b, ha, hb, hab, hgeom, hc.1, hr, hs1, hs2, hc.2.1, hc.2.2⟩

end BerryEsseen
