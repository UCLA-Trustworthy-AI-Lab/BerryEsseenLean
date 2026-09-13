import BerryEsseen.EffectiveGlobalJitter
import BerryEsseen.BoundedJitterEnvelopes

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def rawLatticeMomentDeficit (μ : Measure ℝ) (h : ℝ) : ℝ :=
  cStar * rawThirdAbsoluteMoment μ - |∫ x, (x - rawMean μ) ^ 3 ∂μ| - 3 * h * rawStdDev μ ^ 2

theorem envelope_implies_small_lattice_deficit (P : StandardizedLaw) (h z ε : ℝ)
    (hh : 0 ≤ h) (hε : 0 ≤ ε)
    (he : cE * thirdMoment P < edgeworthEnvelope h (signedThirdMoment P) z + ε) :
    latticeMomentDeficit P h ≤ 16 * ε := by
  have hb := (le_abs_self (edgeworthEnvelope h (signedThirdMoment P) z)).trans
    (edgeworthEnvelope_abs_bound h (signedThirdMoment P) z)
  rw [abs_of_nonneg hh] at hb
  rw [cE_eq] at he
  unfold latticeMomentDeficit
  have hprod := mul_le_mul_of_nonneg_right (show (3 / 8 : ℝ) ≤ phi0 by linarith [phi0_effective_lower])
    (show 0 ≤ 16 * ε by positivity)
  by_contra hbad
  have hD : 16 * ε < cStar * thirdMoment P - |signedThirdMoment P| - 3 * h := lt_of_not_ge hbad
  have hm := mul_lt_mul_of_pos_left hD phi0_pos
  nlinarith only [he, hb, hm, hprod]

theorem raw_signedThirdMoment_of_standardization (μ : Measure ℝ) (Z : StandardizedLaw)
    (m σ : ℝ) (hσ : 0 < σ) (hmap : Z.measure = standardizedMeasure μ m σ) :
    (∫ x, (x - rawMean μ) ^ 3 ∂μ) = σ ^ 3 * signedThirdMoment Z := by
  have hm := (raw_moments_of_standardized_representation μ Z m σ hσ hmap).1
  have hinv := inverse_standardized_representation μ Z m σ hσ hmap
  rw [hm, hinv, integral_map (by fun_prop) (by fun_prop)]
  simp only [add_sub_cancel_right, mul_pow]
  exact integral_const_mul _ _

theorem rawLatticeMomentDeficit_standardization (μ : Measure ℝ) (Z : StandardizedLaw)
    (h : ℝ) (hσ : 0 < rawStdDev μ)
    (hmap : Z.measure = standardizedMeasure μ (rawMean μ) (rawStdDev μ)) :
    rawLatticeMomentDeficit μ h = rawStdDev μ ^ 3 * latticeMomentDeficit Z (h / rawStdDev μ) := by
  have hρ := (raw_moments_of_standardized_representation μ Z (rawMean μ) (rawStdDev μ) hσ hmap).2.2
  have hκ := raw_signedThirdMoment_of_standardization μ Z (rawMean μ) (rawStdDev μ) hσ hmap
  unfold rawLatticeMomentDeficit latticeMomentDeficit
  rw [hρ, hκ, abs_mul, abs_of_pos (pow_pos hσ 3)]
  field_simp
  <;> ring

theorem raw_lattice_deficit_perturbation (P : StandardizedLaw) (Q : Measure ℝ) (h τ : ℝ)
    (hh : h ∈ Icc 0 5) (hτ : 0 ≤ τ)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * τ)
    (hthird : |rawThirdAbsoluteMoment Q - thirdMoment P| +
      |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 2 * (10 : ℝ) ^ 9 * τ) :
    rawLatticeMomentDeficit Q h ≤ latticeMomentDeficit P h + (10 : ℝ) ^ 12 * τ := by
  have hr : rawThirdAbsoluteMoment Q - thirdMoment P ≤ |rawThirdAbsoluteMoment Q - thirdMoment P| := le_abs_self _
  have hκ := abs_abs_sub_abs_le_abs_sub (∫ x, (x - rawMean Q) ^ 3 ∂Q) (signedThirdMoment P)
  have hκ' := (abs_le.mp hκ).1
  have hv' := (abs_le.mp hv).1
  have hc0 : 0 ≤ cStar := le_of_lt (lt_trans zero_lt_one cStar_gt_one)
  have hρ1 := mul_le_mul_of_nonneg_left hr hc0
  have hρ2 := mul_le_mul_of_nonneg_right cStar_effective_bounds.2.le (abs_nonneg (rawThirdAbsoluteMoment Q - thirdMoment P))
  have hvar := mul_le_mul_of_nonneg_left hv' (show 0 ≤ 3 * h by linarith [hh.1])
  have hhτ := mul_le_mul_of_nonneg_right hh.2 hτ
  unfold rawLatticeMomentDeficit latticeMomentDeficit
  nlinarith only [hρ1, hρ2, hκ', hvar, hhτ, hthird,
    abs_nonneg (rawThirdAbsoluteMoment Q - thirdMoment P),
    abs_nonneg ((∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P)]

theorem appendix_standardized_deficit_budget :
    2 * (16 * Real.exp (-18 * appendixA) + (10 : ℝ) ^ 12 * appendixRetention) ≤ Real.exp (-16 * appendixA) := by
  have h1 := exponential_relative_sixteenth 32 (18 * appendixA) (16 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth (2 * (10 : ℝ) ^ 12) (100 * appendixA) (16 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(18 * appendixA) = -18 * appendixA by ring,
    show -(16 * appendixA) = -16 * appendixA by ring] at h1
  rw [show -(100 * appendixA) = -100 * appendixA by ring,
    show -(16 * appendixA) = -16 * appendixA by ring] at h2
  unfold appendixRetention
  nlinarith only [h1, h2, Real.exp_pos (-16 * appendixA)]

theorem effective_standardized_lattice_deficit (E : PublishedEsseenMoment)
    (P : StandardizedLaw) (Q : Measure ℝ) (Z : StandardizedLaw) (h : ℝ)
    (hh : h ∈ Icc 0 5) (hσ : rawStdDev Q ∈ Icc 0.99 1.01)
    (hmap : Z.measure = standardizedMeasure Q (rawMean Q) (rawStdDev Q))
    (hmax : IsMaximalSpan Z (h / rawStdDev Q))
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (hthird : |rawThirdAbsoluteMoment Q - thirdMoment P| +
      |(∫ x, (x - rawMean Q) ^ 3 ∂Q) - signedThirdMoment P| ≤ 2 * (10 : ℝ) ^ 9 * appendixRetention)
    (hD : latticeMomentDeficit P h ≤ 16 * Real.exp (-18 * appendixA)) :
    latticeMomentDeficit Z (h / rawStdDev Q) ∈ Icc 0 (Real.exp (-16 * appendixA)) := by
  have hσ0 : 0 < rawStdDev Q := by linarith [hσ.1]
  have hnonneg : 0 ≤ latticeMomentDeficit Z (h / rawStdDev Q) := by
    have h := esseen_absolute_moment_bound E Z (h / rawStdDev Q) hmax
    unfold latticeMomentDeficit
    linarith
  have hraw := raw_lattice_deficit_perturbation P Q h appendixRetention hh appendix_retention_bounds.1.le hv hthird
  rw [rawLatticeMomentDeficit_standardization Q Z h hσ0 hmap] at hraw
  have hσ3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.99) hσ.1 3
  have hσ3' : (1 / 2 : ℝ) ≤ rawStdDev Q ^ 3 := by nlinarith only [hσ3]
  have hprod := mul_le_mul_of_nonneg_right hσ3' hnonneg
  refine ⟨hnonneg, ?_⟩
  nlinarith only [hraw, hD, hprod, appendix_standardized_deficit_budget]

end BerryEsseen
