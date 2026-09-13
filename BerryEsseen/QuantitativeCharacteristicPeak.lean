import BerryEsseen.EffectivePeakCalculus

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem quantitative_characteristic_peak (P : StandardizedLaw) (r δ : ℝ)
    (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6)) (hβ : thirdMoment P ≤ 2)
    (hslope : |characteristicSquareSlope P r| ≤ δ)
    (hcenter : characteristicSquareCurvature P r ≤ -1.9) :
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
  have hlocal (u : ℝ) (hu : u ∈ Icc L R) : |u - r| ≤ 1 / 1000 :=
    abs_le.mpr ⟨by dsimp [L] at hu; linarith [hu.1], by dsimp [R] at hu; linarith [hu.2]⟩
  have hcurv (u : ℝ) (hu : u ∈ Icc L R) : characteristicSquareCurvature P u ≤ -1 := by
    have h := (characteristicSquareCurvature_lipschitz P 2 hβ).dist_le_mul u r
    simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] at h
    linarith [hlocal u hu, (abs_le.mp h).2]
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

end BerryEsseen
