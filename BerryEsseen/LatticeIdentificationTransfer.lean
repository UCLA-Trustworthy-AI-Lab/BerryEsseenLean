import BerryEsseen.LatticeDeficitTransfer
import BerryEsseen.ManuscriptLatticeCouplings

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem hE_le_three : hE ≤ 3 := by
  have hs : 0.48 ≤ sigmaE := by
    simpa only [sigmaE, qE] using (effective_binomial_parameters pE ⟨pE_bounds.1.le, pE_bounds.2.le⟩).2.1
  unfold hE
  apply (div_le_iff₀ sigmaE_pos).mpr
  linarith

theorem appendix_identification_deficit_small : Real.exp (-16 * appendixA) ≤ 1 / (10 : ℝ) ^ 6 := by
  have h := exponential_sixteenth_bound ((10 : ℝ) ^ 6) (16 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(16 * appendixA) = -16 * appendixA by ring] at h
  linarith

theorem appendix_identification_deficit_sqrt : Real.sqrt (Real.exp (-16 * appendixA)) = Real.exp (-8 * appendixA) := by
  have he : Real.exp (-16 * appendixA) = Real.exp (-8 * appendixA) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, Real.sqrt_sq (Real.exp_pos _).le]

theorem appendix_lattice_identification_budget :
    2000 * Real.exp (-8 * appendixA) + (10 : ℝ) ^ 10 * appendixRetention ≤ Real.exp (-7 * appendixA) := by
  have h1 := exponential_relative_sixteenth 2000 (8 * appendixA) (7 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth ((10 : ℝ) ^ 10) (100 * appendixA) (7 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(8 * appendixA) = -8 * appendixA by ring,
    show -(7 * appendixA) = -7 * appendixA by ring] at h1
  rw [show -(100 * appendixA) = -100 * appendixA by ring,
    show -(7 * appendixA) = -7 * appendixA by ring] at h2
  unfold appendixRetention
  nlinarith only [h1, h2, Real.exp_pos (-7 * appendixA)]

theorem effective_lattice_identification_transfer (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (Q : Measure ℝ) [IsProbabilityMeasure Q] (Z : StandardizedLaw) (h : ℝ)
    (hQ : ∀ᵐ x ∂Q, |x| ≤ 13)
    (hW : wassersteinOne P.measure Q ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hm : |rawMean Q| ≤ (10 : ℝ) ^ 5 * appendixRetention)
    (hv : |rawStdDev Q ^ 2 - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention)
    (hσ : rawStdDev Q ∈ Icc 0.99 1.01)
    (hmap : Z.measure = standardizedMeasure Q (rawMean Q) (rawStdDev Q))
    (hZsupp : Z.measure.support ⊆ Icc (-15) 15) (hZβ : thirdMoment Z ≤ 2)
    (hZlat : IsLatticeSpan Z.measure (h / rawStdDev Q))
    (hD : latticeMomentDeficit Z (h / rawStdDev Q) ∈ Icc 0 (Real.exp (-16 * appendixA))) :
    ∃ ε ∈ ({-1, 1} : Set ℝ),
      wassersteinOne P.measure (esseenLaw.measure.map (fun x => ε * x)) ≤ Real.exp (-7 * appendixA) ∧
      |h - hE| ≤ Real.exp (-7 * appendixA) := by
  have hσ0 : 0 < rawStdDev Q := by linarith [hσ.1]
  obtain ⟨ε, hε, hdist, hspan⟩ := effective_lattice_stability K Z (h / rawStdDev Q) (Real.exp (-16 * appendixA))
    hZsupp hZlat hZβ hD appendix_identification_deficit_small
  rw [appendix_identification_deficit_sqrt] at hdist hspan
  have hσdiff : |rawStdDev Q - 1| ≤ (10 : ℝ) ^ 9 * appendixRetention := by
    have he : |rawStdDev Q - 1| * (rawStdDev Q + 1) = |rawStdDev Q ^ 2 - 1| := by
      rw [← abs_of_pos (show 0 < rawStdDev Q + 1 by linarith), ← abs_mul]
      congr 1
      ring
    have hp := mul_nonneg hσ0.le (abs_nonneg (rawStdDev Q - 1))
    nlinarith only [he, hp, hv]
  have hQZ := (manuscript_wasserstein_affine_standardized_actual Q Z
    (rawMean Q) (rawStdDev Q) hσ0 hmap).2
  let ν := esseenLaw.measure.map (fun x => ε * x)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have hνi : Integrable (fun x : ℝ => x) ν := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    simpa only [Function.comp_def] using esseenLaw.first_integrable.const_mul ε
  have hQi := real_function_integrable_of_abs_le Q (fun x : ℝ => x) 13 measurable_id hQ
  have ht1 := wassersteinOne_triangle K P.measure Q Z.measure P.first_integrable hQi Z.first_integrable
  have ht2 := wassersteinOne_triangle K P.measure Z.measure ν P.first_integrable Z.first_integrable hνi
  have hwfinal : wassersteinOne P.measure ν ≤ 2000 * Real.exp (-8 * appendixA) + (10 : ℝ) ^ 10 * appendixRetention := by
    change wassersteinOne Z.measure ν ≤ _ at hdist
    nlinarith only [ht1, ht2, hW, hQZ, hdist, hm, hσdiff,
      appendix_retention_bounds.1, Real.exp_pos (-8 * appendixA)]
  have hspanfinal : |h - hE| ≤ 2000 * Real.exp (-8 * appendixA) + (10 : ℝ) ^ 10 * appendixRetention := by
    have he : h - hE = rawStdDev Q * (h / rawStdDev Q - hE) + (rawStdDev Q - 1) * hE := by
      field_simp
      <;> ring
    have htri := abs_add_le (rawStdDev Q * (h / rawStdDev Q - hE)) ((rawStdDev Q - 1) * hE)
    rw [← he, abs_mul, abs_mul, abs_of_pos hσ0, abs_of_pos hE_pos] at htri
    have h1 := mul_le_mul hσ.2 hspan (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1.01)
    have h2 := mul_le_mul hσdiff hE_le_three hE_pos.le (mul_nonneg (by norm_num) appendix_retention_bounds.1.le)
    nlinarith only [htri, h1, h2, appendix_retention_bounds.1, Real.exp_pos (-8 * appendixA)]
  exact ⟨ε, hε, hwfinal.trans appendix_lattice_identification_budget,
    hspanfinal.trans appendix_lattice_identification_budget⟩

end BerryEsseen
