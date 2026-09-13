import BerryEsseen.EffectiveGaussianTail

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem effective_cluster_gaussian_tail (n : ℕ) (hn : 2 ≤ n) (κ σ : ℝ)
    (hκ : |κ| ≤ 1.84) (hσ : (0.48 : ℝ) ≤ σ) (hσ1 : σ ≤ 1) (hσ2 : (0.24 : ℝ) ≤ σ ^ 2) :
    (∫ t in {t : ℝ | σ * Real.sqrt (n : ℝ) / 2 ≤ |t|}, edgeworthTailIntegrand n κ t) ≤
      20 * Real.exp (-3 * (n : ℝ) / 100) := by
  let r := Real.sqrt (n : ℝ)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hσ0 : 0 < σ := by linarith
  have h := edgeworth_tail_integral_bound n κ (σ * r / 2) (by positivity)
  have hex : -(σ * r / 2) ^ 2 / 2 = -σ ^ 2 * (n : ℝ) / 8 := by rw [← hr2]; ring
  rw [hex] at h
  have he : 2 * (Real.exp (-σ ^ 2 * (n : ℝ) / 8) / (σ * r / 2) ^ 2 +
      (|κ| / (6 * r)) * ((σ * r / 2 + 1 / (σ * r / 2)) * Real.exp (-σ ^ 2 * (n : ℝ) / 8))) =
      (8 / (σ ^ 2 * (n : ℝ)) + |κ| * (σ / 6 + 2 / (3 * σ * (n : ℝ)))) * Real.exp (-σ ^ 2 * (n : ℝ) / 8) := by
    rw [← hr2]
    field_simp
    <;> ring
  change _ ≤ 2 * (Real.exp (-σ ^ 2 * (n : ℝ) / 8) / (σ * r / 2) ^ 2 +
      (|κ| / (6 * r)) * ((σ * r / 2 + 1 / (σ * r / 2)) * Real.exp (-σ ^ 2 * (n : ℝ) / 8))) at h
  rw [he] at h
  have hvn := mul_le_mul hσ2 hn2 (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ σ ^ 2)
  have hσn := mul_le_mul hσ hn2 (by norm_num : (0 : ℝ) ≤ 2) hσ0.le
  have h8 : 8 / (σ ^ 2 * (n : ℝ)) ≤ 17 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hvn])
  have h2 : 2 / (3 * σ * (n : ℝ)) ≤ 3 / 4 := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hσn])
  have hbracket : σ / 6 + 2 / (3 * σ * (n : ℝ)) ≤ 1 := by linarith
  have hp := mul_le_mul hκ hbracket (by positivity : 0 ≤ σ / 6 + 2 / (3 * σ * (n : ℝ))) (by norm_num : (0 : ℝ) ≤ 1.84)
  have hc : 8 / (σ ^ 2 * (n : ℝ)) + |κ| * (σ / 6 + 2 / (3 * σ * (n : ℝ))) ≤ 20 := by linarith
  have hexp : Real.exp (-σ ^ 2 * (n : ℝ) / 8) ≤ Real.exp (-3 * (n : ℝ) / 100) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hσ2 hn0.le
    nlinarith only [h]
  exact h.trans (mul_le_mul hc hexp (Real.exp_pos _).le (by norm_num))

end BerryEsseen
