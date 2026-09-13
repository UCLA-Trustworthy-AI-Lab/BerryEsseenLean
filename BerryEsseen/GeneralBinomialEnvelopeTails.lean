import BerryEsseen.GeneralBinomialMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem binomial_envelopes_absolute_bound (p z : ℝ) (hp : p ∈ Icc 0 1) :
    |binomialUpperEnvelope p z| ≤ standardNormalDensity z * (4 + z ^ 2) / 3 ∧
    |binomialLowerEnvelope p z| ≤ standardNormalDensity z * (4 + z ^ 2) / 3 := by
  have hτ : 1 / 2 ≤ p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hden : 0 < 6 * (p ^ 2 + (1 - p) ^ 2) := by linarith only [hτ]
  have hf0 := (standardNormalDensity_pos z).le
  have hfac0 : 0 ≤ standardNormalDensity z / (6 * (p ^ 2 + (1 - p) ^ 2)) := div_nonneg hf0 hden.le
  have hfac : standardNormalDensity z / (6 * (p ^ 2 + (1 - p) ^ 2)) ≤ standardNormalDensity z / 3 :=
    div_le_div_of_nonneg_left hf0 (by norm_num) (by linarith only [hτ])
  have hd : |1 - 2 * p| ≤ 1 := abs_le.mpr ⟨by linarith only [hp.2], by linarith only [hp.1]⟩
  have hds : |(1 - 2 * p) * z ^ 2| ≤ z ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
    exact (mul_le_mul_of_nonneg_right hd (sq_nonneg z)).trans_eq (one_mul _)
  have hu : |3 + (1 - 2 * p) - (1 - 2 * p) * z ^ 2| ≤ 4 + z ^ 2 := by
    rcases abs_le.mp hd with ⟨hdlo, hdhi⟩
    rcases abs_le.mp hds with ⟨hslo, hshi⟩
    exact abs_le.mpr ⟨by linarith only [hdlo, hshi, sq_nonneg z], by linarith only [hdhi, hslo]⟩
  have hl : |3 - (1 - 2 * p) + (1 - 2 * p) * z ^ 2| ≤ 4 + z ^ 2 := by
    rcases abs_le.mp hd with ⟨hdlo, hdhi⟩
    rcases abs_le.mp hds with ⟨hslo, hshi⟩
    exact abs_le.mpr ⟨by linarith only [hdhi, hslo, sq_nonneg z], by linarith only [hdlo, hshi]⟩
  have hU := mul_le_mul hfac hu (abs_nonneg _) (by positivity : 0 ≤ standardNormalDensity z / 3)
  have hL := mul_le_mul hfac hl (abs_nonneg _) (by positivity : 0 ≤ standardNormalDensity z / 3)
  unfold binomialUpperEnvelope binomialLowerEnvelope
  rw [abs_mul, abs_of_nonneg hfac0, abs_mul, abs_of_nonneg hfac0]
  constructor
  · convert hU using 1 <;> ring
  · convert hL using 1 <;> ring

theorem gaussian_quadratic_rational_bound (z : ℝ) :
    standardNormalDensity z * (4 + z ^ 2) / 3 ≤ 3 / (1 + z ^ 2) := by
  have hden : 0 < 1 + z ^ 2 := by positivity
  have he := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ z ^ 2 / 2)
  have hphi := mul_le_mul_of_nonneg_right phi0_lt_two_fifths.le
    (by positivity : 0 ≤ (4 + z ^ 2) * (1 + z ^ 2))
  rw [standardNormalDensity_formula, show -z ^ 2 / 2 = -(z ^ 2 / 2) by ring, Real.exp_neg]
  apply (le_div_iff₀ hden).mpr
  have hid : phi0 * (Real.exp (z ^ 2 / 2))⁻¹ * (4 + z ^ 2) / 3 * (1 + z ^ 2) =
      (phi0 * ((4 + z ^ 2) * (1 + z ^ 2))) / (3 * Real.exp (z ^ 2 / 2)) := by ring
  rw [hid]
  apply (div_le_iff₀ (mul_pos (by norm_num) (Real.exp_pos _))).mpr
  nlinarith only [he, hphi, sq_nonneg z, sq_nonneg (z ^ 2)]

theorem binomial_envelopes_rational_tail (p z : ℝ) (hp : p ∈ Icc 0 1) :
    |binomialUpperEnvelope p z| ≤ 3 / (1 + z ^ 2) ∧
    |binomialLowerEnvelope p z| ≤ 3 / (1 + z ^ 2) := by
  have h := binomial_envelopes_absolute_bound p z hp
  exact ⟨h.1.trans (gaussian_quadratic_rational_bound z), h.2.trans (gaussian_quadratic_rational_bound z)⟩

theorem binomial_envelopes_uniform_tail :
    ∀ ε > 0, ∃ M ≥ 0, ∀ p ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, M ≤ |z| →
      |binomialUpperEnvelope p z| < ε ∧ |binomialLowerEnvelope p z| < ε := by
  intro ε hε
  refine ⟨3 / ε + 1, by positivity, ?_⟩
  intro p hp z hz
  have hM : (1 : ℝ) ≤ |z| := by linarith [div_pos (by norm_num : (0 : ℝ) < 3) hε]
  have hsq : |z| ≤ z ^ 2 := by
    nlinarith only [mul_nonneg (abs_nonneg z) (sub_nonneg.mpr hM), sq_abs z]
  have hscale := (div_le_iff₀ hε).mp (show 3 / ε ≤ |z| - 1 by linarith only [hz])
  have hmul := mul_le_mul_of_nonneg_right hsq hε.le
  have hrat : 3 / (1 + z ^ 2) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < 1 + z ^ 2)).mpr
    nlinarith only [hscale, hmul, hε]
  have hb := binomial_envelopes_rational_tail p z hp
  exact ⟨hb.1.trans_lt hrat, hb.2.trans_lt hrat⟩

end BerryEsseen
