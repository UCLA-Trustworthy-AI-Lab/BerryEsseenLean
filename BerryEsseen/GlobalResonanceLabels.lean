import BerryEsseen.GlobalPeakIntegral
import BerryEsseen.EffectiveClusterFrequency

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def globalPositiveResonanceLabels (h T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (Nat.floor T)).filter (fun k => (k : ℝ) * (2 * Real.pi / h) ≤ T + 1 / 1000)

theorem globalPositiveResonanceLabels_properties (h T : ℝ) (k : ℕ)
    (hk : k ∈ globalPositiveResonanceLabels h T) :
    1 ≤ k ∧ k ≤ Nat.floor T ∧ (k : ℝ) * (2 * Real.pi / h) ≤ T + 1 / 1000 := by
  classical
  simpa only [globalPositiveResonanceLabels, Finset.mem_filter, Finset.mem_Icc, and_assoc] using hk

theorem globalPositiveResonanceLabels_cover (h T u : ℝ) (hh : h ∈ Ioc 0 5)
    (hu : u ∈ Icc (1 / 2) T) (j : ℤ)
    (hj : |u - (j : ℝ) * (2 * Real.pi / h)| < 1 / 1000) :
    ∃ k ∈ globalPositiveResonanceLabels h T, u ∈ globalResonanceCell h (k : ℤ) := by
  classical
  have hh0 := hh.1
  have hd := abs_lt.mp hj
  have hjr : 0 < (j : ℝ) := by
    have hr : 0 < (j : ℝ) * (2 * Real.pi / h) := by linarith [hu.1]
    exact (mul_pos_iff_of_pos_right (by positivity : 0 < 2 * Real.pi / h)).mp hr
  have hjZ : 0 < j := by exact_mod_cast hjr
  let k := j.toNat
  have hkcast : (k : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hjZ.le
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hkr : (k : ℝ) * (2 * Real.pi / h) ≤ T + 1 / 1000 := by rw [hkcast]; linarith [hu.2]
  have hkT : (k : ℝ) ≤ T := by
    have hω := mul_le_mul_of_nonneg_left (global_resonance_frequency_lower h hh) (Nat.cast_nonneg k)
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  refine ⟨k, ?_, ?_⟩
  · simp only [globalPositiveResonanceLabels, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hk1, Nat.le_floor hkT⟩, hkr⟩
  · unfold globalResonanceCell
    rw [Int.cast_natCast, hkcast]
    constructor <;> linarith

theorem globalPositiveResonanceLabels_harmonic (h T : ℝ) (hT : 1 ≤ T) :
    (∑ k ∈ globalPositiveResonanceLabels h T, (k : ℝ)⁻¹) ≤ 1 + Real.log T := by
  classical
  have hs : globalPositiveResonanceLabels h T ⊆ Finset.Icc 1 (Nat.floor T) := Finset.filter_subset _ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => (k : ℝ)⁻¹) hs
    (fun k _ _ => inv_nonneg.mpr (Nat.cast_nonneg k))
  have hh := harmonic_floor_le_one_add_log T hT
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  exact hsum.trans hh

theorem global_nonresonance_distance (h u : ℝ)
    (haway : ∀ j : ℤ, 1 / 1000 ≤ |u - (j : ℝ) * (2 * Real.pi / h)|) :
    1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) := by
  apply (Metric.le_infDist (Set.range_nonempty _)).mpr
  rintro y ⟨j, rfl⟩
  simpa only [Real.dist_eq, zero_add, mul_comm (2 * Real.pi / h)] using haway j

end BerryEsseen
