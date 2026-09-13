import BerryEsseen.AffineLatticeSpan

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem raw_maximal_span_integer_multiple (μ : Measure ℝ) (Z : StandardizedLaw)
    (m σ h₀ : ℝ) (hσ : 0 < σ) (hmap : Z.measure = standardizedMeasure μ m σ)
    (hlat : IsLatticeSpan μ h₀) :
    ∃ (h : ℝ) (k : ℤ), IsLatticeSpan μ h ∧
      (∀ d : ℝ, IsLatticeSpan μ d → d ≤ h) ∧
      IsMaximalSpan Z (h / σ) ∧ 1 ≤ k ∧ h = (k : ℝ) * h₀ := by
  have hstd : IsLatticeSpan Z.measure (h₀ / σ) := by
    rw [hmap]
    exact latticeSpan_standardized μ m σ h₀ hσ hlat
  obtain ⟨d, k, hd, hdmax, hk, he, hgen⟩ := maximal_span_integer_multiple Z (h₀ / σ) hstd
  have hinv := inverse_standardized_representation μ Z m σ hσ hmap
  have hraw : IsLatticeSpan μ (σ * d) := by
    rw [hinv]
    exact latticeSpan_affine_map Z.measure σ m d hσ hd
  refine ⟨σ * d, k, hraw, ?_, ?_, hk, ?_⟩
  · intro h' hh'
    have hs : IsLatticeSpan Z.measure (h' / σ) := by
      rw [hmap]
      exact latticeSpan_standardized μ m σ h' hσ hh'
    have hm := (div_le_iff₀ hσ).mp (hdmax.2.2 (h' / σ) hs)
    nlinarith only [hm]
  · simpa only [mul_div_cancel_left₀ d hσ.ne'] using hdmax
  · rw [he]
    field_simp

theorem effective_raw_maximal_span (E : PublishedEsseenMoment)
    (μ : Measure ℝ) (Z : StandardizedLaw) (m σ h₀ : ℝ)
    (hσ : σ ∈ Icc 0.99 1.01) (hmap : Z.measure = standardizedMeasure μ m σ)
    (hβ : thirdMoment Z < 2) (hlo : Real.pi / 500 ≤ h₀) (hlat : IsLatticeSpan μ h₀) :
    ∃ (h : ℝ) (k : ℤ), Real.pi / 500 ≤ h ∧ h ≤ 5 ∧ IsLatticeSpan μ h ∧
      (∀ d : ℝ, IsLatticeSpan μ d → d ≤ h) ∧
      IsMaximalSpan Z (h / σ) ∧ 1 ≤ k ∧ h = (k : ℝ) * h₀ := by
  have hσpos : 0 < σ := by linarith [hσ.1]
  obtain ⟨h, k, hh, hmax, hzmax, hk, he⟩ :=
    raw_maximal_span_integer_multiple μ Z m σ h₀ hσpos hmap hlat
  have hbound := esseen_absolute_moment_bound E Z (h / σ) hzmax
  have hprod : cStar * thirdMoment Z ≤ 14 := by
    have h := mul_le_mul cStar_effective_bounds.2.le hβ.le (thirdMoment_pos Z).le (by norm_num : (0 : ℝ) ≤ 7)
    linarith
  have hd : h / σ ≤ 14 / 3 := by linarith [abs_nonneg (signedThirdMoment Z)]
  have hu : h ≤ 5 := by
    have hm := (div_le_iff₀ hσpos).mp hd
    nlinarith only [hm, hσ.2]
  exact ⟨h, k, hlo.trans (hmax h₀ hlat), hu, hh, hmax, hzmax, hk, he⟩

end BerryEsseen
