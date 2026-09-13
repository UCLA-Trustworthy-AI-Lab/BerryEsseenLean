import BerryEsseen.LatticeRounding
import BerryEsseen.ManuscriptLatticeCouplings

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def latticeRoundingPoints (a h : ℝ) : Finset ℝ := by
  classical
  exact (latticeRoundingIndices a h).image (fun k : ℤ => a + h * (k : ℝ))

def latticeRoundedMeasure (P : StandardizedLaw) (a h : ℝ) : Measure ℝ := P.measure.map (latticeRound a h)

theorem latticeRoundedMeasure_probability (P : StandardizedLaw) (a h : ℝ) :
    IsProbabilityMeasure (latticeRoundedMeasure P a h) :=
  Measure.isProbabilityMeasure_map (latticeRound_measurable a h).aemeasurable

theorem latticeRoundingPoints_card (a h : ℝ) (hlower : Real.pi / 500 ≤ h) :
    (latticeRoundingPoints a h).card < 2000 := by
  classical
  exact Finset.card_image_le.trans_lt (latticeRoundingIndices_card a h hlower)

theorem latticeRoundingPoints_bounded (a h : ℝ) (hh : 0 < h) (hupper : h ≤ 4 * Real.pi)
    (y : ℝ) (hy : y ∈ latticeRoundingPoints a h) : |y| < 13 := by
  classical
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
  rw [latticeRoundingIndices, Finset.mem_Icc] at hk
  have hlo : (⌊(-6 - a) / h + 1 / 2⌋ : ℝ) ≤ k := by exact_mod_cast hk.1
  have hhi : (k : ℝ) ≤ ⌊(6 - a) / h + 1 / 2⌋ := by exact_mod_cast hk.2
  have hfloorlo := Int.lt_floor_add_one ((-6 - a) / h + 1 / 2)
  have hfloorhi := Int.floor_le ((6 - a) / h + 1 / 2)
  have hlk : (-6 - a) / h + 1 / 2 - 1 < k := by linarith
  have huk : (k : ℝ) ≤ (6 - a) / h + 1 / 2 := hhi.trans hfloorhi
  have hl := mul_lt_mul_of_pos_right hlk hh
  have hu := mul_le_mul_of_nonneg_right huk hh.le
  have hel : ((-6 - a) / h + 1 / 2 - 1) * h = -6 - a - h / 2 := by field_simp; ring
  have heu : ((6 - a) / h + 1 / 2) * h = 6 - a + h / 2 := by field_simp
  rw [hel] at hl
  rw [heu] at hu
  rw [abs_lt]
  constructor <;> nlinarith [Real.pi_lt_d2]

theorem latticeRoundedMeasure_support (P : StandardizedLaw) (a h : ℝ) (hh : 0 < h)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) :
    (latticeRoundedMeasure P a h).support ⊆ (latticeRoundingPoints a h : Set ℝ) := by
  classical
  apply Measure.support_subset_of_isClosed (latticeRoundingPoints a h).finite_toSet.isClosed
  change ∀ᵐ x ∂P.measure.map (latticeRound a h), x ∈ (latticeRoundingPoints a h : Set ℝ)
  apply (ae_map_iff (latticeRound_measurable a h).aemeasurable
    (latticeRoundingPoints a h).finite_toSet.measurableSet).mpr
  filter_upwards [P.measure.support_mem_ae] with x hx
  exact Finset.mem_image.mpr ⟨round ((x - a) / h),
    latticeRound_index_mem a h x hh (abs_le.mpr (hsupp hx)), rfl⟩

theorem latticeRoundedMeasure_span (P : StandardizedLaw) (a h : ℝ) (hh : 0 < h)
    (hsupp : P.measure.support ⊆ Icc (-6) 6) : IsLatticeSpan (latticeRoundedMeasure P a h) h := by
  classical
  refine ⟨hh, a, ?_⟩
  intro y hy
  have hmem := latticeRoundedMeasure_support P a h hh hsupp hy
  change y ∈ (latticeRoundingIndices a h).image (fun k : ℤ => a + h * (k : ℝ)) at hmem
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hmem
  exact ⟨k, by ring⟩

theorem wassersteinOne_symm (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    wassersteinOne μ ν = wassersteinOne ν μ := by
  have hle (ρ η : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure η]
      (hρ : Integrable (fun x : ℝ => x) ρ) (hη : Integrable (fun x : ℝ => x) η) :
      wassersteinOne ρ η ≤ wassersteinOne η ρ := by
    apply wassersteinOne_le_of_lipschitz K ρ η hρ hη
    intro f hf
    have h := lipschitz_integral_le_wassersteinOne K η ρ hη hρ (fun x => -f x) hf.neg
    simp only [integral_neg] at h
    linarith
  exact le_antisymm (hle μ ν hμ hν) (hle ν μ hν hμ)

theorem latticeRoundedMeasure_wasserstein (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (a h t : ℝ) (hh : 0 < h) (hupper : h ≤ 4 * Real.pi)
    (ht : 0 ≤ t) (hsupp : P.measure.support ⊆ Icc (-6) 6)
    (herror : (∫ x, Metric.infDist x (affineLattice a h) ^ 2 ∂P.measure) ≤ 2 * Real.pi ^ 2 * t) :
    wassersteinOne P.measure (latticeRoundedMeasure P a h) ≤ 5 * Real.sqrt t := by
  letI := latticeRoundedMeasure_probability P a h
  have hgi : Integrable (latticeRound a h) P.measure :=
    real_function_integrable_of_abs_le P.measure _ 13 (latticeRound_measurable a h) (by
      filter_upwards [P.measure.support_mem_ae] with x hx
      exact (latticeRound_bounded a h x hh hupper (abs_le.mpr (hsupp hx))).le)
  have hcost := manuscript_wasserstein_common_source P.measure id (latticeRound a h)
    measurable_id (latticeRound_measurable a h) (P.first_integrable.sub hgi).abs
  rw [Measure.map_id] at hcost
  apply hcost.trans
  exact latticeRound_mean_error P.measure a h t hh ht herror

theorem effective_finite_lattice_rounding (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (K : PublishedWassersteinDuality)
    (P : StandardizedLaw) (n : ℕ) (hn : 1024 ≤ n) (hsupp : P.measure.support ⊆ Icc (-6) 6)
    (hviol : ¬ BoundAt P n) :
    ∃ a h : ℝ, Real.pi / 500 ≤ h ∧ h ≤ 4 * Real.pi ∧
      IsProbabilityMeasure (latticeRoundedMeasure P a h) ∧
      (latticeRoundingPoints a h).card < 2000 ∧
      (latticeRoundedMeasure P a h).support ⊆ (latticeRoundingPoints a h : Set ℝ) ∧
      (∀ x ∈ latticeRoundingPoints a h, |x| < 13) ∧
      IsLatticeSpan (latticeRoundedMeasure P a h) h ∧
      (∫ x, |x - latticeRound a h x| ∂P.measure) ≤ 5 * Real.sqrt (Real.log (n : ℝ) / n) ∧
      wassersteinOne P.measure (latticeRoundedMeasure P a h) ≤ 5 * Real.sqrt (Real.log (n : ℝ) / n) := by
  obtain ⟨a, h, hlower, hupper, hi, herr⟩ := effective_near_lattice H S P n hn hsupp hviol
  have hh : 0 < h := (div_pos Real.pi_pos (by norm_num)).trans_le hlower
  have ht : 0 ≤ Real.log (n : ℝ) / (n : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (Nat.cast_nonneg n)
  have herr' : (∫ x, Metric.infDist x (affineLattice a h) ^ 2 ∂P.measure) ≤
      2 * Real.pi ^ 2 * (Real.log (n : ℝ) / n) := by convert herr using 1 <;> ring
  exact ⟨a, h, hlower, hupper, latticeRoundedMeasure_probability P a h,
    latticeRoundingPoints_card a h hlower, latticeRoundedMeasure_support P a h hh hsupp,
    latticeRoundingPoints_bounded a h hh hupper, latticeRoundedMeasure_span P a h hh hsupp,
    latticeRound_mean_error P.measure a h _ hh ht herr',
    latticeRoundedMeasure_wasserstein K P a h _ hh hupper ht hsupp herr'⟩

end BerryEsseen
