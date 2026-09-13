import BerryEsseen.WassersteinMoments
import BerryEsseen.PublishedEsseenMoment
import BerryEsseen.ManuscriptResonanceGeometry

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem support_map_inverse_subset (μ : Measure ℝ) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Continuous g) (hinv : ∀ x, g (f x) = x) :
    (μ.map f).support ⊆ g ⁻¹' μ.support := by
  apply Measure.support_subset_of_isClosed (μ.isClosed_support.preimage hg)
  apply (ae_map_iff hf.aemeasurable (μ.isClosed_support.measurableSet.preimage hg.measurable)).mpr
  filter_upwards [μ.support_mem_ae] with x hx
  change g (f x) ∈ μ.support
  rwa [hinv x]

theorem latticeSpan_affine_map (μ : Measure ℝ) (c m h : ℝ) (hc : 0 < c)
    (hlat : IsLatticeSpan μ h) : IsLatticeSpan (μ.map (fun x => c * x + m)) (c * h) := by
  obtain ⟨hh, a, ha⟩ := hlat
  refine ⟨mul_pos hc hh, c * a + m, ?_⟩
  intro y hy
  have hs := support_map_inverse_subset μ (fun x => c * x + m) (fun x => (x - m) / c)
    (by fun_prop) (by fun_prop) (fun x => by field_simp; ring)
  obtain ⟨k, hk⟩ := ha ((y - m) / c) (hs hy)
  refine ⟨k, ?_⟩
  have he := (div_eq_iff hc.ne').mp hk
  nlinarith only [he]

theorem latticeSpan_standardized (μ : Measure ℝ) (m σ h : ℝ) (hσ : 0 < σ)
    (hlat : IsLatticeSpan μ h) : IsLatticeSpan (standardizedMeasure μ m σ) (h / σ) := by
  have hmap := latticeSpan_affine_map μ σ⁻¹ (-m / σ) h (inv_pos.mpr hσ) hlat
  have he : (fun x : ℝ => σ⁻¹ * x + -m / σ) = fun x => (x - m) / σ := by
    funext x
    field_simp
    ring
  rw [he, show σ⁻¹ * h = h / σ by ring] at hmap
  exact hmap

theorem maximal_span_integer_multiple (P : StandardizedLaw) (h₀ : ℝ)
    (hlat : IsLatticeSpan P.measure h₀) :
    ∃ (h : ℝ) (k : ℤ), IsLatticeSpan P.measure h ∧ IsMaximalSpan P h ∧
      1 ≤ k ∧ h = (k : ℝ) * h₀ ∧
      resonanceSubgroup P.measure = AddSubgroup.zmultiples (2 * Real.pi / h) := by
  rcases manuscript_lattice_span_dichotomy P with ⟨hbot, hnone⟩ | ⟨h, hh, hmax, hgen⟩
  · exact False.elim (hnone h₀ hlat)
  · have hres := latticeSpan_gives_resonance P.measure h₀ hlat
    rw [hgen, AddSubgroup.mem_zmultiples_iff] at hres
    obtain ⟨k, hk⟩ := hres
    rw [zsmul_eq_mul] at hk
    have hkpos : 0 < (k : ℝ) := by
      have hp : 0 < (k : ℝ) * (2 * Real.pi / h) := by rw [hk]; exact div_pos Real.two_pi_pos hlat.1
      exact (mul_pos_iff_of_pos_right (div_pos Real.two_pi_pos hh.1)).mp hp
    have hki : (0 : ℤ) < k := by exact_mod_cast hkpos
    refine ⟨h, k, hh, ⟨hh.1.le, fun _ => hh, hmax⟩, by omega, ?_, hgen⟩
    have hEq : (k : ℝ) * (2 * Real.pi) * h₀ = (2 * Real.pi) * h := by
      exact (div_eq_div_iff hh.1.ne' hlat.1.ne').mp
        (show (k : ℝ) * (2 * Real.pi) / h = (2 * Real.pi) / h₀ by simpa [mul_div_assoc] using hk)
    nlinarith only [hEq, Real.pi_pos]

end BerryEsseen
