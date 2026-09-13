import BerryEsseen.MovingPeaks

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

theorem quadratic_upper_with_curvature (f f₁ f₂ : ℝ → ℝ) (L R m u c : ℝ)
    (hc : 0 < c) (hm : m ∈ Icc L R) (hu : u ∈ Icc L R)
    (h₁ : ∀ x ∈ Icc L R, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc L R, HasDerivAt f₁ (f₂ x) x)
    (hcurv : ∀ x ∈ Icc L R, f₂ x ≤ -c) (hcrit : f₁ m = 0) :
    f u ≤ f m - c * (u - m) ^ 2 / 2 := by
  have h := quadratic_upper_at_critical_point (fun x => f x / c) (fun x => f₁ x / c)
    (fun x => f₂ x / c) L R m u hm hu
    (fun x hx => (h₁ x hx).div_const c) (fun x hx => (h₂ x hx).div_const c)
    (fun x hx => (div_le_iff₀ hc).mpr (by simpa only [neg_one_mul] using hcurv x hx))
    (by simp only [hcrit, zero_div])
  have hmul := mul_le_mul_of_nonneg_right h hc.le
  have hc0 : c ≠ 0 := hc.ne'
  field_simp at hmul
  nlinarith only [hmul]

theorem critical_point_distance_of_curvature (f₁ f₂ : ℝ → ℝ) (L R m r c : ℝ)
    (hc : 0 < c) (hm : m ∈ Icc L R) (hr : r ∈ Icc L R)
    (h₂ : ∀ x ∈ Icc L R, HasDerivAt f₁ (f₂ x) x)
    (hcurv : ∀ x ∈ Icc L R, f₂ x ≤ -c) (hcrit : f₁ m = 0) :
    c * |m - r| ≤ |f₁ r| := by
  let g : ℝ → ℝ := fun x => f₁ x + c * x
  have hg (x : ℝ) (hx : x ∈ Icc L R) : HasDerivAt g (f₂ x + c) x := by
    convert (h₂ x hx).add ((hasDerivAt_id x).const_mul c) using 1
    simp
  have hmono : AntitoneOn g (Icc L R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc L R)
    · exact fun x hx => (hg x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hg x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hg x (interior_subset hx)).deriv]
      linarith [hcurv x (interior_subset hx)]
  rcases le_total m r with hmr | hrm
  · have h := hmono hm hr hmr
    dsimp only [g] at h
    rw [hcrit, zero_add] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hmr)]
    linarith [neg_le_abs (f₁ r)]
  · have h := hmono hr hm hrm
    dsimp only [g] at h
    rw [hcrit, zero_add] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hrm)]
    linarith [le_abs_self (f₁ r)]

theorem exists_interior_critical_point (f₁ f₂ : ℝ → ℝ) (L R : ℝ) (hLR : L < R)
    (h₂ : ∀ x ∈ Icc L R, HasDerivAt f₁ (f₂ x) x)
    (hL : 0 < f₁ L) (hR : f₁ R < 0) :
    ∃ m ∈ Ioo L R, f₁ m = 0 := by
  have hc : ContinuousOn f₁ (Icc L R) := fun x hx => (h₂ x hx).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hzero⟩ := intermediate_value_Icc' hLR.le hc ⟨hR.le, hL.le⟩
  have hmL : m ≠ L := by intro he; rw [he] at hzero; linarith
  have hmR : m ≠ R := by intro he; rw [he] at hzero; linarith
  exact ⟨m, ⟨lt_of_le_of_ne hm.1 hmL.symm, lt_of_le_of_ne hm.2 hmR⟩, hzero⟩

theorem norm_pow_gaussian_of_quadratic_bound (z : ℂ) (d c : ℝ)
    (h : ‖z‖ ^ 2 ≤ 1 - c * d ^ 2) (n : ℕ) :
    ‖z‖ ^ n ≤ Real.exp (-(n : ℝ) * c * d ^ 2 / 2) := by
  have he := Real.add_one_le_exp (-c * d ^ 2)
  have heq : Real.exp (-c * d ^ 2 / 2) ^ 2 = Real.exp (-c * d ^ 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hn : ‖z‖ ≤ Real.exp (-c * d ^ 2 / 2) := by
    nlinarith [norm_nonneg z, Real.exp_pos (-c * d ^ 2 / 2)]
  have hp := pow_le_pow_left₀ (norm_nonneg z) hn n
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

end BerryEsseen
