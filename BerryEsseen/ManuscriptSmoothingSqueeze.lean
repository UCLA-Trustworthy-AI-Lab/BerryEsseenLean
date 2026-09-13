import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The two one-sided averaging inequalities in the manuscript's smoothing proof.
These are proved for actual integrals, with a genuine probability measure. -/
noncomputable section
open MeasureTheory Set Filter
namespace BerryEsseen

theorem manuscript_cdf_difference_growth (F G : ℝ → ℝ)
    (hF : Monotone F) (M : ℝ) (hG : ∀ x y, |G x - G y| ≤ M * |x - y|)
    (x y : ℝ) (hxy : x ≤ y) :
    (F x - G x) - M * (y - x) ≤ F y - G y := by
  have hg := hG y x
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hg
  linarith [hF hxy, le_abs_self (G y - G x)]

theorem manuscript_smoothing_lower_integral
    (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (d : ℝ → ℝ) (M Dm a L x : ℝ) (_hM : 0 ≤ M) (hL : 0 < L)
    (hd : ∀ y, -Dm ≤ d y)
    (hg : ∀ y z, y ≤ z → d y - M * (z - y) ≤ d z)
    (hi : Integrable (fun z => d (x + (a - z) / L)) κ)
    (hm : Integrable (fun z : ℝ => max (a - z) 0) κ) :
    (1 - κ.real (Ioi a)) * d x - κ.real (Ioi a) * Dm -
      (M / L) * (∫ z, max (a - z) 0 ∂κ) ≤
        ∫ z, d (x + (a - z) / L) ∂κ := by
  let b : ℝ → ℝ := (Iic a).indicator (fun _ => d x + Dm)
  have hb : Integrable b κ := (integrable_const _).indicator measurableSet_Iic
  have hpoint : ∀ z, b z - Dm - (M / L) * max (a - z) 0 ≤
      d (x + (a - z) / L) := by
    intro z
    by_cases hz : z ≤ a
    · have hstep : x ≤ x + (a - z) / L := by
        have : 0 ≤ (a - z) / L := div_nonneg (sub_nonneg.mpr hz) hL.le
        linarith
      have hh := hg x (x + (a - z) / L) hstep
      simp only [b, indicator_apply, mem_Iic, if_pos hz, max_eq_left (sub_nonneg.mpr hz)]
      convert hh using 1; ring
    · have hneg : a - z ≤ 0 := by linarith
      simp only [b, indicator_apply, mem_Iic, if_neg hz, max_eq_right hneg, mul_zero,
        sub_zero, zero_sub]
      exact hd _
  have hbc : Integrable (fun z => b z - Dm) κ := hb.sub (integrable_const _)
  have hmc : Integrable (fun z => (M / L) * max (a - z) 0) κ := hm.const_mul _
  have h := integral_mono_ae (hbc.sub hmc) hi
    (Eventually.of_forall hpoint)
  change (∫ z, b z - Dm - (M / L) * max (a - z) 0 ∂κ) ≤ _ at h
  have ht : κ.real (Iic a) = 1 - κ.real (Ioi a) := by
    simpa only [compl_Ioi] using probReal_compl_eq_one_sub (μ := κ) measurableSet_Ioi
  have he : (∫ z, b z - Dm - (M / L) * max (a - z) 0 ∂κ) =
      (1 - κ.real (Ioi a)) * d x - κ.real (Ioi a) * Dm -
        (M / L) * (∫ z, max (a - z) 0 ∂κ) := by
    rw [integral_sub hbc hmc,
      integral_sub hb (integrable_const _), integral_const_mul]
    dsimp [b]
    rw [integral_indicator_const _ measurableSet_Iic, integral_const,
      probReal_univ, one_smul, smul_eq_mul, ht]
    ring
  rwa [he] at h

theorem manuscript_smoothing_upper_integral
    (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (d : ℝ → ℝ) (M Dp a L x : ℝ) (_hM : 0 ≤ M) (hL : 0 < L)
    (hd : ∀ y, d y ≤ Dp)
    (hg : ∀ y z, y ≤ z → d y - M * (z - y) ≤ d z)
    (hi : Integrable (fun z => d (x - (a + z) / L)) κ)
    (hm : Integrable (fun z : ℝ => max (a + z) 0) κ) :
    (∫ z, d (x - (a + z) / L) ∂κ) ≤
      (1 - κ.real (Iio (-a))) * d x + κ.real (Iio (-a)) * Dp +
        (M / L) * (∫ z, max (a + z) 0 ∂κ) := by
  let b : ℝ → ℝ := (Ici (-a)).indicator (fun _ => d x - Dp)
  have hb : Integrable b κ := (integrable_const _).indicator measurableSet_Ici
  have hpoint : ∀ z, d (x - (a + z) / L) ≤
      b z + Dp + (M / L) * max (a + z) 0 := by
    intro z
    by_cases hz : -a ≤ z
    · have hstep : x - (a + z) / L ≤ x := by
        have : 0 ≤ (a + z) / L := div_nonneg (by linarith) hL.le
        linarith
      have hh := hg (x - (a + z) / L) x hstep
      simp only [b, indicator_apply, mem_Ici, if_pos hz,
        max_eq_left (by linarith : 0 ≤ a + z)]
      have heq : M * (x - (x - (a + z) / L)) = (M / L) * (a + z) := by ring
      rw [heq] at hh
      linarith
    · have hneg : a + z ≤ 0 := by linarith
      simp only [b, indicator_apply, mem_Ici, if_neg hz, max_eq_right hneg, mul_zero,
        add_zero, zero_add]
      exact hd _
  have hbc : Integrable (fun z => b z + Dp) κ := hb.add (integrable_const _)
  have hmc : Integrable (fun z => (M / L) * max (a + z) 0) κ := hm.const_mul _
  have h := integral_mono_ae hi (hbc.add hmc)
    (Eventually.of_forall hpoint)
  change _ ≤ (∫ z, b z + Dp + (M / L) * max (a + z) 0 ∂κ) at h
  have ht : κ.real (Ici (-a)) = 1 - κ.real (Iio (-a)) := by
    simpa only [compl_Iio] using probReal_compl_eq_one_sub (μ := κ) measurableSet_Iio
  have he : (∫ z, b z + Dp + (M / L) * max (a + z) 0 ∂κ) =
      (1 - κ.real (Iio (-a))) * d x + κ.real (Iio (-a)) * Dp +
        (M / L) * (∫ z, max (a + z) 0 ∂κ) := by
    rw [integral_add hbc hmc,
      integral_add hb (integrable_const _), integral_const_mul]
    dsimp [b]
    rw [integral_indicator_const _ measurableSet_Ici, integral_const,
      probReal_univ, one_smul, smul_eq_mul, ht]
    ring
  rwa [he] at h

theorem manuscript_smoothing_combine (Dp Dm ε R B : ℝ)
    (hε0 : 0 ≤ ε)
    (hpos : (1 - ε) * Dp - ε * Dm ≤ R + B)
    (hneg : (1 - ε) * Dm - ε * Dp ≤ R + B) :
    (1 - 2 * ε) * max Dp Dm ≤ R + B := by
  rcases le_total Dp Dm with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr h)]
  · rw [max_eq_left h]
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr h)]

theorem manuscript_smoothing_constants (ε Ca : ℝ) (_hε0 : 0 ≤ ε)
    (hε : ε < 1 / 8) (hCa : Ca < 18) :
    (1 / (2 * Real.pi * (1 - 2 * ε)) ≤ (1 : ℝ) / 4) ∧
      Ca / (1 - 2 * ε) ≤ 24 := by
  have hden : 0 < 1 - 2 * ε := by linarith
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    nlinarith [Real.pi_gt_three]
  · rw [div_le_iff₀ hden]
    linarith

theorem manuscript_smoothing_take_sup (d : ℝ → ℝ) (D ε R B : ℝ)
    (hd : ∀ x, |d x| ≤ D) (hε : ε < 1)
    (hpos : ∀ x, (1 - ε) * d x - ε * sSup (range (fun y => -d y)) ≤ R + B)
    (hneg : ∀ x, (1 - ε) * (-d x) - ε * sSup (range d) ≤ R + B)
    (hε0 : 0 ≤ ε) :
    (1 - 2 * ε) * sSup (range (fun x => |d x|)) ≤ R + B := by
  have hbpos : BddAbove (range d) := ⟨D, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (hd x)⟩
  have hbneg : BddAbove (range (fun y => -d y)) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact (neg_le_abs _).trans (hd x)⟩
  have hbabs : BddAbove (range (fun x => |d x|)) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact hd x⟩
  have hcp : (1 - ε) * sSup (range d) - ε * sSup (range (fun y => -d y)) ≤ R + B := by
    have hbound : sSup (range d) ≤
        (R + B + ε * sSup (range (fun y => -d y))) / (1 - ε) := by
      apply csSup_le (range_nonempty d)
      rintro _ ⟨x, rfl⟩
      rw [le_div_iff₀ (by linarith : 0 < 1 - ε)]
      nlinarith [hpos x]
    have hh := (le_div_iff₀ (by linarith : 0 < 1 - ε)).mp hbound
    nlinarith
  have hcn : (1 - ε) * sSup (range (fun y => -d y)) - ε * sSup (range d) ≤ R + B := by
    have hbound : sSup (range (fun y => -d y)) ≤
        (R + B + ε * sSup (range d)) / (1 - ε) := by
      apply csSup_le (range_nonempty (fun y => -d y))
      rintro _ ⟨x, rfl⟩
      rw [le_div_iff₀ (by linarith : 0 < 1 - ε)]
      nlinarith [hneg x]
    have hh := (le_div_iff₀ (by linarith : 0 < 1 - ε)).mp hbound
    nlinarith
  have heq : sSup (range (fun x => |d x|)) =
      max (sSup (range d)) (sSup (range (fun y => -d y))) := by
    apply le_antisymm
    · apply csSup_le (range_nonempty _)
      rintro _ ⟨x, rfl⟩
      change |d x| ≤ max (sSup (range d)) (sSup (range (fun y => -d y)))
      rw [abs_eq_max_neg]
      exact max_le_max (le_csSup hbpos (mem_range_self x))
        (le_csSup hbneg (mem_range_self x))
    · apply max_le
      · apply csSup_le (range_nonempty _)
        rintro _ ⟨x, rfl⟩
        exact (le_abs_self _).trans (le_csSup hbabs (mem_range_self x))
      · apply csSup_le (range_nonempty _)
        rintro _ ⟨x, rfl⟩
        exact (neg_le_abs _).trans (le_csSup hbabs (mem_range_self x))
  rw [heq]
  exact manuscript_smoothing_combine _ _ ε R B hε0 hcp hcn

theorem manuscript_smoothing_final_constants (D I M L ε Ca : ℝ)
    (hI : 0 ≤ I) (hM : 0 ≤ M) (hL : 0 < L)
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 8) (hCa : Ca < 18)
    (hbound : (1 - 2 * ε) * D ≤ (1 / (2 * Real.pi)) * I + (M / L) * Ca) :
    D ≤ (1 / 4) * I + 24 * M / L := by
  have hden : 0 < 1 - 2 * ε := by linarith
  have hc := manuscript_smoothing_constants ε Ca hε0 hε hCa
  have hdiv : D ≤ ((1 / (2 * Real.pi)) * I + (M / L) * Ca) / (1 - 2 * ε) := by
    rw [le_div_iff₀ hden]
    nlinarith [hbound]
  calc
    D ≤ _ := hdiv
    _ = (1 / (2 * Real.pi * (1 - 2 * ε))) * I +
        (Ca / (1 - 2 * ε)) * (M / L) := by
      field_simp [ne_of_gt hden, Real.pi_ne_zero, hL.ne']
    _ ≤ (1 / 4) * I + 24 * (M / L) :=
      add_le_add (mul_le_mul_of_nonneg_right hc.1 hI)
        (mul_le_mul_of_nonneg_right hc.2 (div_nonneg hM hL.le))
    _ = (1 / 4) * I + 24 * M / L := by ring

end BerryEsseen
