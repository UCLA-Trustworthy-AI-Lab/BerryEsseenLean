import BerryEsseen.NearLatticeFrequency
import BerryEsseen.PhaseConcentration

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem effective_near_lattice (H : ClassicalBerryEsseenBounds) (S : PublishedSignedSmoothing)
    (P : StandardizedLaw) (n : ℕ) (hn : 1024 ≤ n) (hsupp : P.measure.support ⊆ Icc (-6) 6)
    (hviol : ¬ BoundAt P n) :
    ∃ a h : ℝ, Real.pi / 500 ≤ h ∧ h ≤ 4 * Real.pi ∧
      Integrable (fun x => Metric.infDist x (affineLattice a h) ^ 2) P.measure ∧
      (∫ x, Metric.infDist x (affineLattice a h) ^ 2 ∂P.measure) ≤
        2 * Real.pi ^ 2 * Real.log (n : ℝ) / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  rw [BoundAt_iff_normalized P n hn1] at hviol
  push_neg at hviol
  obtain ⟨x, hx⟩ := hviol
  have hβ : thirdMoment P ≤ 1.84 :=
    ((normalized_violation_momentCutoff H P n hn1 x hx).trans momentCutoff_bounds.2).le
  have hb : ∀ᵐ y ∂P.measure, |y| ≤ 6 := by
    filter_upwards [P.measure.support_mem_ae] with y hy
    exact abs_le.mpr (hsupp hy)
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_large_characteristic_of_violation S P n hn hβ hb x hx
  have hδ : 0 ≤ Real.log (n : ℝ) / (n : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) (Nat.cast_nonneg n)
  obtain ⟨a, h, hlow, hupp, hi, hbound⟩ := near_lattice_of_large_characteristic P.measure u
    (Real.log (n : ℝ) / (n : ℝ)) hu1 hu2 hδ hu3.le
  refine ⟨a, h, hlow, hupp, hi, ?_⟩
  convert hbound using 1 <;> ring

end BerryEsseen
