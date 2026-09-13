import BerryEsseen.EffectiveGlobalDerivatives
import BerryEsseen.EffectivePeakCalculus

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_characteristic_peak_of_cell_curvature (P : StandardizedLaw) (r δ : ℝ)
    (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hslope : |characteristicSquareSlope P r| ≤ δ)
    (hcell : ∀ u ∈ Icc (r - 1 / 1000) (r + 1 / 1000), characteristicSquareCurvature P u ≤ -1) :
    ∃ m ∈ Ioo (r - 1 / 1000) (r + 1 / 1000),
      characteristicSquareSlope P m = 0 ∧ |m - r| ≤ δ ∧
      IsMaxOn (characteristicSquare P) (Icc (r - 1 / 1000) (r + 1 / 1000)) m ∧
      (∀ v ∈ Icc (r - 1 / 1000) (r + 1 / 1000), characteristicSquareSlope P v = 0 → v = m) ∧
      ∀ u ∈ Icc (r - 1 / 1000) (r + 1 / 1000), ∀ n : ℕ,
        ‖charFun P.measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * (u - m) ^ 2 / 4) := by
  let L := r - 1 / 1000
  let R := r + 1 / 1000
  have hr : r ∈ Icc L R := ⟨by dsimp [L]; linarith, by dsimp [R]; linarith⟩
  have hLR : L < R := by dsimp [L, R]; linarith
  have hcurv (u : ℝ) (hu : u ∈ Icc L R) : characteristicSquareCurvature P u ≤ -1 := hcell u hu
  let g : ℝ → ℝ := fun u => characteristicSquareSlope P u + u
  have hg (u : ℝ) : HasDerivAt g (characteristicSquareCurvature P u + 1) u :=
    (characteristicSquareSlope_hasDerivAt P u).add (hasDerivAt_id u)
  have hmono : AntitoneOn g (Icc L R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc L R)
    · exact fun u _ => (hg u).continuousAt.continuousWithinAt
    · exact fun u _ => (hg u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hg u).deriv]
      linarith [hcurv u (interior_subset hu)]
  have hL : 0 < characteristicSquareSlope P L := by
    have h := hmono ⟨le_rfl, hLR.le⟩ hr hr.1
    dsimp only [g, L] at h ⊢
    linarith [(abs_le.mp hslope).1, hδ.2]
  have hR : characteristicSquareSlope P R < 0 := by
    have h := hmono hr ⟨hLR.le, le_rfl⟩ hr.2
    dsimp only [g, R] at h ⊢
    linarith [(abs_le.mp hslope).2, hδ.2]
  obtain ⟨m, hm, hcrit⟩ := exists_interior_critical_point (characteristicSquareSlope P)
    (characteristicSquareCurvature P) L R hLR (fun u _ => characteristicSquareSlope_hasDerivAt P u) hL hR
  have hmcc : m ∈ Icc L R := ⟨hm.1.le, hm.2.le⟩
  have hdist := critical_point_distance_of_curvature (characteristicSquareSlope P)
    (characteristicSquareCurvature P) L R m r 1 (by norm_num) hmcc hr
    (fun u _ => characteristicSquareSlope_hasDerivAt P u) hcurv hcrit
  have hquad (u : ℝ) (hu : u ∈ Icc L R) := quadratic_upper_at_critical_point
    (characteristicSquare P) (characteristicSquareSlope P) (characteristicSquareCurvature P)
    L R m u hmcc hu (fun u _ => characteristicSquare_hasDerivAt P u)
    (fun u _ => characteristicSquareSlope_hasDerivAt P u) hcurv hcrit
  have hmax : IsMaxOn (characteristicSquare P) (Icc L R) m := by
    intro u hu
    have h := hquad u hu
    change characteristicSquare P u ≤ characteristicSquare P m
    nlinarith [sq_nonneg (u - m)]
  refine ⟨m, hm, hcrit, by linarith, hmax, ?_, ?_⟩
  · intro v hv hvzero
    have h := critical_point_distance_of_curvature (characteristicSquareSlope P)
      (characteristicSquareCurvature P) L R m v 1 (by norm_num) hmcc hv
      (fun u _ => characteristicSquareSlope_hasDerivAt P u) hcurv hcrit
    rw [hvzero, abs_zero, one_mul] at h
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))).symm
  · intro u hu n
    exact characteristic_peak_envelope P L R m hm hmax hcurv u hu n

def globalResonanceCell (h : ℝ) (j : ℤ) : Set ℝ :=
  Icc ((j : ℝ) * (2 * Real.pi / h) - 1 / 1000) ((j : ℝ) * (2 * Real.pi / h) + 1 / 1000)

theorem effective_global_peak (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ 6) (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hβ : thirdMoment P ≤ 2)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (h : ℝ) (hlat : IsLatticeSpan Q h) (j : ℤ)
    (hj : |(j : ℝ) * (2 * Real.pi / h)| ≤ appendixGlobalCutoff + 1 / 1000) :
    ∃ m ∈ interior (globalResonanceCell h j),
      characteristicSquareSlope P m = 0 ∧
      |m - (j : ℝ) * (2 * Real.pi / h)| ≤ appendixDerivativeError ∧
      IsMaxOn (characteristicSquare P) (globalResonanceCell h j) m ∧
      (∀ v ∈ globalResonanceCell h j, characteristicSquareSlope P v = 0 → v = m) ∧
      ∀ u ∈ globalResonanceCell h j, ∀ n : ℕ,
        ‖charFun P.measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * (u - m) ^ 2 / 4) := by
  have hd := effective_global_resonance_derivatives K P Q hP hQ hW hv
    ((j : ℝ) * (2 * Real.pi / h)) (lattice_integer_resonance Q h hlat j) (by linarith)
  have hcell (u : ℝ) (hu : u ∈ globalResonanceCell h j) :
      characteristicSquareCurvature P u ≤ -1 := by
    apply manuscript_global_cell_curvature K P Q hP hQ hW hv
      ((j : ℝ) * (2 * Real.pi / h)) u (lattice_integer_resonance Q h hlat j) hj
    apply abs_le.mpr
    dsimp [globalResonanceCell] at hu
    constructor <;> linarith [hu.1, hu.2]
  have hp := manuscript_characteristic_peak_of_cell_curvature P
    ((j : ℝ) * (2 * Real.pi / h)) appendixDerivativeError
    ⟨appendix_derivative_error_small.1.le, appendix_derivative_error_small.2⟩ hd.1 hcell
  simpa only [globalResonanceCell, interior_Icc] using hp

end BerryEsseen
