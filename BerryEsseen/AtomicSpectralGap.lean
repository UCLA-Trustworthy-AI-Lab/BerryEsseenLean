import BerryEsseen.CharacteristicConditioning
import BerryEsseen.ManuscriptIndependentCopy

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem integral_nonnegative_atom_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hi : Integrable f μ) (hf : ∀ x, 0 ≤ f x) (x τ : ℝ)
    (hτ : τ ≤ μ.real {x}) : τ * f x ≤ ∫ y, f y ∂μ := by
  have hs := setIntegral_le_integral (s := ({x} : Set ℝ)) hi (ae_of_all _ hf)
  rw [integral_singleton, smul_eq_mul] at hs
  exact (mul_le_mul_of_nonneg_right hτ (hf x)).trans hs

theorem two_atoms_characteristic_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (τ x y u : ℝ) (hτ : 0 ≤ τ) (hx : τ ≤ μ.real {x}) (hy : τ ≤ μ.real {y}) :
    τ * ‖realPhase u x - realPhase u y‖ ^ 2 ≤ 8 * (1 - ‖charFun μ u‖) := by
  let c := Complex.exp ((Complex.arg (charFun μ u) : ℂ) * Complex.I)
  have hc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hi := phase_squared_deviation_integrable μ u c hc
  have hid : (∫ z, ‖realPhase u z - c‖ ^ 2 ∂μ) = 2 * (1 - ‖charFun μ u‖) :=
    phase_concentration_identity μ u
  have hpoint (z : ℝ) (hz : τ ≤ μ.real {z}) :
      τ * ‖realPhase u z - c‖ ^ 2 ≤ 2 * (1 - ‖charFun μ u‖) := by
    rw [← hid]
    exact integral_nonnegative_atom_lower μ _ hi (fun w => sq_nonneg _) z τ hz
  have htri := dist_triangle (realPhase u x) c (realPhase u y)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev c (realPhase u y)] at htri
  have hsq := mul_self_le_mul_self (norm_nonneg (realPhase u x - realPhase u y)) htri
  have hquad : ‖realPhase u x - realPhase u y‖ ^ 2 ≤
      2 * ‖realPhase u x - c‖ ^ 2 + 2 * ‖realPhase u y - c‖ ^ 2 := by
    nlinarith only [hsq, sq_nonneg (‖realPhase u x - c‖ - ‖realPhase u y - c‖)]
  have hmul := mul_le_mul_of_nonneg_left hquad hτ
  nlinarith only [hmul, hpoint x hx, hpoint y hy]

/-- A finitely supported actual probability integral is its weighted
finite sum. No lower bound on the atoms is needed for this identity. -/
theorem manuscript_finite_support_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (hs : μ.support ⊆ (F : Set ℝ))
    (f : ℝ → ℝ) (hi : Integrable f μ) :
    (∫ x, f x ∂μ) = ∑ x ∈ F, μ.real {x} * f x := by
  have hF : ∀ᵐ x ∂μ, x ∈ (F : Set ℝ) := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hs hx
  have hr := Measure.restrict_eq_self_of_ae_mem hF
  have he := integral_finset F f hi.integrableOn
  rw [hr] at he
  simpa only [smul_eq_mul] using he

/-- The exact finite double-cosine identity in the manuscript. Its proof
uses the difference of two independent samples and the actual atom masses. -/
theorem manuscript_finite_cosine_square_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (hs : μ.support ⊆ (F : Set ℝ)) (u : ℝ) :
    1 - ‖charFun μ u‖ ^ 2 =
      ∑ x ∈ F, ∑ y ∈ F, μ.real {x} * μ.real {y} * (1 - Real.cos (u * (x - y))) := by
  have hi : Integrable (fun xy : ℝ × ℝ => Real.cos (u * (xy.1 - xy.2))) (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun xy => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u * (xy.1 - xy.2)))
  have hix (x : ℝ) : Integrable (fun y => Real.cos (u * (x - y))) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (u * (x - y)))
  have hcos : (∑ x ∈ F, μ.real {x} * (∑ y ∈ F, μ.real {y} * Real.cos (u * (x - y)))) =
      ‖charFun μ u‖ ^ 2 := by
    have h := manuscriptDifferenceLaw_cos μ u
    rw [manuscriptDifferenceLaw, integral_map (by fun_prop) (by fun_prop), integral_prod _ hi] at h
    rw [manuscript_finite_support_integral μ F hs _ hi.integral_prod_left] at h
    simpa only [manuscript_finite_support_integral μ F hs _ (hix _)] using h
  have hmass : (∑ x ∈ F, μ.real {x}) = 1 := by
    have h := manuscript_finite_support_integral μ F hs (fun _ => 1) (integrable_const _)
    simpa only [integral_const, probReal_univ, one_smul, mul_one] using h.symm
  symm
  calc
    _ = ∑ x ∈ F, μ.real {x} *
        ((∑ y ∈ F, μ.real {y}) - ∑ y ∈ F, μ.real {y} * Real.cos (u * (x - y))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = (∑ x ∈ F, μ.real {x}) -
        ∑ x ∈ F, μ.real {x} * (∑ y ∈ F, μ.real {y} * Real.cos (u * (x - y))) := by
      simp only [hmass, mul_sub, mul_one, Finset.sum_sub_distrib]
    _ = _ := by rw [hmass, hcos]

theorem manuscript_phase_difference_square (u x y : ℝ) :
    ‖realPhase u x - realPhase u y‖ ^ 2 = 2 * (1 - Real.cos (u * (x - y))) := by
  have he := realPhase_difference_chord u x (u * y)
  have hy : realPhase 1 (u * y) = realPhase u y := by simp [realPhase]
  rw [hy] at he
  rw [← he, Complex.norm_sub_one_sq_eq_of_norm_eq_one (realPhase_norm _ _)]
  simp only [realPhase, one_mul, Complex.exp_ofReal_mul_I_re]
  rw [show u * x - u * y = u * (x - y) by ring]

/-- Preserve the two symmetric atom pairs in the exact finite double
sum. This is the manuscript's quadratic tau bound, not the older
concentration-around-one-phase estimate. -/
theorem manuscript_finite_two_atoms_square_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ x y u : ℝ) (hτ : 0 ≤ τ)
    (hs : μ.support ⊆ (F : Set ℝ)) (hxF : x ∈ F) (hyF : y ∈ F)
    (hatom : ∀ z ∈ F, τ ≤ μ.real {z}) :
    τ ^ 2 * ‖realPhase u x - realPhase u y‖ ^ 2 ≤ 1 - ‖charFun μ u‖ ^ 2 := by
  classical
  let w : ℝ → ℝ → ℝ := fun a b => μ.real {a} * μ.real {b} * (1 - Real.cos (u * (a - b)))
  have hw (a b : ℝ) : 0 ≤ w a b := by
    exact mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) (sub_nonneg.mpr (Real.cos_le_one _))
  have hid : (∑ a ∈ F, ∑ b ∈ F, w a b) = 1 - ‖charFun μ u‖ ^ 2 :=
    (manuscript_finite_cosine_square_identity μ F hs u).symm
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    rw [← hid]
    exact Finset.sum_nonneg (fun a ha => Finset.sum_nonneg (fun b hb => hw a b))
  · have hpair : w x y + w y x ≤ ∑ a ∈ F, ∑ b ∈ F, w a b := by
      have hx := Finset.single_le_sum (fun b hb => hw x b) hyF
      have hy := Finset.single_le_sum (fun b hb => hw y b) hxF
      have hout : (∑ a ∈ ({x, y} : Finset ℝ), ∑ b ∈ F, w a b) ≤ ∑ a ∈ F, ∑ b ∈ F, w a b := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl <;> assumption
        · intro a ha hnot
          exact Finset.sum_nonneg (fun b hb => hw a b)
      rw [Finset.sum_pair hxy] at hout
      linarith
    have hphase : w x y + w y x = μ.real {x} * μ.real {y} * ‖realPhase u x - realPhase u y‖ ^ 2 := by
      rw [manuscript_phase_difference_square]
      have he : Real.cos (u * (y - x)) = Real.cos (u * (x - y)) := by
        rw [show u * (y - x) = -(u * (x - y)) by ring, Real.cos_neg]
      dsimp only [w]
      rw [he]
      ring
    have hmass := mul_le_mul (hatom x hxF) (hatom y hyF) hτ measureReal_nonneg
    have hh := mul_le_mul_of_nonneg_right hmass (sq_nonneg ‖realPhase u x - realPhase u y‖)
    rw [hphase, hid] at hpair
    apply le_trans ?_ hpair
    simpa only [pow_two] using hh

end BerryEsseen
