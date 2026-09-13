import BerryEsseen.ManuscriptCayleyBezoutBound
import BerryEsseen.FiniteLatticeLabels

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Triangle inequality in R/(2πZ), with integer coefficients and their actual
L1 budget. The comparison lattice point is the sum of the rounded phases. -/
theorem manuscript_circular_residual_integer_sum {ι : Type*} (F : Finset ι)
    (c : ι → ℤ) (v : ι → ℝ) :
    |circularResidual (∑ i ∈ F, (c i : ℝ) * v i)| ≤
      ∑ i ∈ F, |(c i : ℝ)| * |circularResidual (v i)| := by
  classical
  let k : ℤ := ∑ i ∈ F, c i * round (v i / (2 * Real.pi))
  have hn := latticeRound_nearest 0 (2 * Real.pi) (∑ i ∈ F, (c i : ℝ) * v i)
    (by positivity) k
  have hl : (∑ i ∈ F, (c i : ℝ) * v i) -
      latticeRound 0 (2 * Real.pi) (∑ i ∈ F, (c i : ℝ) * v i) =
      circularResidual (∑ i ∈ F, (c i : ℝ) * v i) := by
    simp only [latticeRound, circularResidual, sub_zero, zero_add]
    ring
  have hr : (∑ i ∈ F, (c i : ℝ) * v i) - (0 + 2 * Real.pi * (k : ℝ)) =
      ∑ i ∈ F, (c i : ℝ) * circularResidual (v i) := by
    dsimp only [k]
    push_cast
    rw [zero_add, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [circularResidual]
    ring
  rw [hl, hr] at hn
  apply hn.trans
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (f := fun i => (c i : ℝ) * circularResidual (v i)) (s := F)

theorem manuscript_bezout_circular_bound (D : Finset ℕ) (c : ℕ → ℤ)
    (heq : (∑ d ∈ D, c d * (d : ℤ)) = 1)
    (hL : (∑ d ∈ D, |c d|) ≤ 4000) (v C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ d ∈ D, |circularResidual ((d : ℝ) * v)| ≤ C) :
    |circularResidual v| ≤ 4000 * C := by
  have heqR : (∑ d ∈ D, (c d : ℝ) * (d : ℝ)) = 1 := by exact_mod_cast heq
  have hsum : (∑ d ∈ D, (c d : ℝ) * ((d : ℝ) * v)) = v := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, heqR, one_mul]
  have htri := manuscript_circular_residual_integer_sum D c (fun d => (d : ℝ) * v)
  rw [hsum] at htri
  have hsumB : (∑ d ∈ D, |(c d : ℝ)| * |circularResidual ((d : ℝ) * v)|) ≤
      (∑ d ∈ D, |(c d : ℝ)|) * C := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hb d hd) (abs_nonneg _))
  have hLR : (∑ d ∈ D, |(c d : ℝ)|) ≤ (4000 : ℝ) := by exact_mod_cast hL
  exact htri.trans (hsumB.trans (mul_le_mul_of_nonneg_right hLR hC))

theorem manuscript_resonance_distance_residual (h u : ℝ) (hh : 0 < h) :
    Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) ≤ |circularResidual (h * u)| / h := by
  let k : ℤ := round (h * u / (2 * Real.pi))
  have hm : (0 + (2 * Real.pi / h) * (k : ℝ)) ∈ affineLattice 0 (2 * Real.pi / h) := ⟨k, rfl⟩
  have hd := Metric.infDist_le_dist_of_mem (x := u) hm
  have he : u - (0 + (2 * Real.pi / h) * (k : ℝ)) = circularResidual (h * u) / h := by
    dsimp [circularResidual, k]
    field_simp
    ring
  simpa only [Real.dist_eq, he, abs_div, abs_of_pos hh] using hd

end BerryEsseen
