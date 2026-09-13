import BerryEsseen.BernoulliWasserstein
import BerryEsseen.ManuscriptLatticeBernoulliCoupling
import BerryEsseen.ManuscriptLatticeReflection

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_lattice_affine_transport_budget (μ : Measure ℝ) (Z : StandardizedLaw)
    (m σ δ : ℝ) (hσ : 0 < σ) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hmap : Z.measure = standardizedMeasure μ m σ)
    (hm : |m| ≤ 2 * δ) (hv : |σ ^ 2 - 1| ≤ 5 * δ) :
    wassersteinOne μ Z.measure ≤ 2 * δ + 5 * δ / (1 + Real.sqrt (1 - 5 * δ)) ∧
      wassersteinOne μ Z.measure ≤ 10 * δ := by
  have hslo : Real.sqrt (1 - 5 * δ) ≤ σ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hσ.le, by linarith [(abs_le.mp hv).1]⟩
  have hd : 0 < 1 + Real.sqrt (1 - 5 * δ) := by positivity
  have he : |σ - 1| * (1 + σ) = |σ ^ 2 - 1| := by
    rw [← abs_of_pos (show 0 < 1 + σ by positivity), ← abs_mul]
    congr 1
    ring
  have hscale : |σ - 1| ≤ 5 * δ / (1 + Real.sqrt (1 - 5 * δ)) := by
    apply (le_div_iff₀ hd).mpr
    calc
      _ ≤ |σ - 1| * (1 + σ) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |σ ^ 2 - 1| := he
      _ ≤ 5 * δ := hv
  have hcost := (manuscript_wasserstein_affine_standardized_actual μ Z m σ hσ hmap).2
  have hcost' : wassersteinOne μ Z.measure ≤ 2 * δ + 5 * δ / (1 + Real.sqrt (1 - 5 * δ)) :=
    hcost.trans (add_le_add hm hscale)
  refine ⟨hcost', ?_⟩
  have hfrac : 5 * δ / (1 + Real.sqrt (1 - 5 * δ)) ≤ 5 * δ := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (show 0 ≤ 5 * δ by linarith [hδ.1]) (Real.sqrt_nonneg (1 - 5 * δ))]
  linarith [hδ.1]

theorem manuscript_effective_lattice_wasserstein_budget (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (h δ : ℝ) (hsupp : P.measure.support ⊆ Icc (-15) 15)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    wassersteinOne P.measure esseenLaw.measure ≤ 30 * δ + 96 * Real.sqrt δ := by
  obtain ⟨a, b, ha, hb, hab, hnz, hr, hm, hv, hσ, hp, hparam⟩ :=
    effective_lattice_conditional_parameter P h δ hlat hβ hκ hD hδ
  let ν := ProbabilityTheory.cond P.measure {-a, b}
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  have hν : Integrable (fun x : ℝ => x) ν := conditional_integrable_real _ _ hnz _ P.first_integrable
  let p := ν.real {b}
  have hp01 := (effective_binomial_parameters p hp).1
  let Z := standardizedBernoulliLaw p hp01
  have hh := effective_lattice_span_bounds P h δ hβ hD hδ
  have hδ0 := hD.1.trans hD.2
  have hx : ∀ᵐ x ∂P.measure, |x| ≤ 15 := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact abs_le.mpr (hsupp hx)
  have hy : ∀ᵐ x ∂ν, |x| ≤ 5 := by
    filter_upwards [conditional_pair_mem P.measure (-a) b] with x hx
    rcases hx with rfl | rfl
    · rw [abs_neg, abs_of_pos ha]
      linarith [hh.2]
    · rw [abs_of_pos hb]
      linarith [hh.2]
  have htruncate : wassersteinOne P.measure ν ≤ 20 * δ := by
    have h := manuscript_wasserstein_conditioning_actual P.measure {-a, b}
      ((measurableSet_singleton b).insert (-a)) hnz P.first_integrable 15 5 hx hy
    change wassersteinOne P.measure ν ≤ _ at h
    linarith
  have hrep := two_atoms_canonical_standardization ν (-a) b (by linarith) (conditional_pair_mem _ _ _) hσ
  have hstandardize : wassersteinOne ν Z.measure ≤ 10 * δ :=
    (manuscript_lattice_affine_transport_budget ν Z (rawMean ν) (rawStdDev ν) δ hσ
      ⟨hδ0, hδ⟩ hrep.1 hm hv).2
  have hBernoulli : wassersteinOne Z.measure esseenLaw.measure ≤ 96 * Real.sqrt δ := by
    have h := manuscript_standardizedBernoulli_wasserstein_actual p pE hp ⟨pE_bounds.1.le, pE_bounds.2.le⟩
    rw [standardizedBernoulli_pE] at h
    change wassersteinOne Z.measure esseenLaw.measure ≤ _ at h
    linarith
  have htri1 := wassersteinOne_triangle K P.measure ν Z.measure P.first_integrable hν Z.first_integrable
  have htri2 := wassersteinOne_triangle K P.measure Z.measure esseenLaw.measure
    P.first_integrable Z.first_integrable esseenLaw.first_integrable
  have hbudget : wassersteinOne P.measure esseenLaw.measure ≤ 30 * δ + 96 * Real.sqrt δ := by
    linarith
  exact hbudget

theorem effective_lattice_wasserstein_nonnegative (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (h δ : ℝ) (hsupp : P.measure.support ⊆ Icc (-15) 15)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    wassersteinOne P.measure esseenLaw.measure ≤ 1000 * Real.sqrt δ := by
  have hb := manuscript_effective_lattice_wasserstein_budget K P h δ hsupp hlat hβ hκ hD hδ
  apply hb.trans
  have hδ0 := hD.1.trans hD.2
  have hδroot : δ ≤ Real.sqrt δ := by nlinarith [Real.sq_sqrt hδ0, Real.sqrt_nonneg δ]
  nlinarith [Real.sqrt_nonneg δ]

/-- The full original quantitative lattice stability lemma, including actual
Wasserstein coupling cost and both choices of the reflection sign. -/
theorem effective_lattice_stability (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (h δ : ℝ) (hsupp : P.measure.support ⊆ Icc (-15) 15)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hD : latticeMomentDeficit P h ∈ Icc 0 δ) (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ ε ∈ ({-1, 1} : Set ℝ),
      wassersteinOne P.measure (esseenLaw.measure.map (fun x => ε * x)) ≤ 1000 * Real.sqrt δ ∧
      |h - hE| ≤ 1000 * Real.sqrt δ := by
  have hspan := effective_lattice_span_stability P h δ hlat hβ hD hδ
  by_cases hκ : 0 ≤ signedThirdMoment P
  · refine ⟨1, by simp, ?_, hspan⟩
    simp only [one_mul, Measure.map_id']
    exact effective_lattice_wasserstein_nonnegative K P h δ hsupp hlat hβ hκ hD hδ
  · refine ⟨-1, by simp, ?_, hspan⟩
    have hsupp' : (reflectedLaw P).measure.support ⊆ Icc (-15) 15 := by
      intro x hx
      have h := hsupp (reflected_support_subset P hx)
      constructor <;> linarith [h.1, h.2]
    have hW := effective_lattice_wasserstein_nonnegative K (reflectedLaw P) h δ hsupp'
      (reflected_lattice_span P h hlat) (by simpa only [reflectedLaw_thirdMoment] using hβ)
      (by rw [reflectedLaw_signedThirdMoment]; linarith)
      (by simpa only [latticeMomentDeficit_reflected] using hD) hδ
    have he := manuscript_wasserstein_reflected_actual (reflectedLaw P).measure esseenLaw.measure
    change wassersteinOne ((P.measure.map (fun x => -x)).map (fun x => -x))
      (esseenLaw.measure.map (fun x => -x)) = _ at he
    rw [reflected_measure_twice] at he
    simp only [neg_one_mul]
    rw [he]
    exact hW

end BerryEsseen
