import BerryEsseen.IntervalConditioning
import BerryEsseen.AffineRigidity

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem bounded_two_cluster_affine_representation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b η : ℝ) (hη : 0 ≤ η) (hgap : 2 * η < b - a)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (a - η) (a + η) ∪ Icc (b - η) (b + η))
    (hp : μ.real (Ioi ((a + b) / 2)) ∈ Ioo 0 1) :
    ∃ (P Q : CenteredFourthLaw) (m d : ℝ), 0 < d ∧
      d ∈ Icc (b - a - 2 * η) (b - a + 2 * η) ∧
      (∀ᵐ x ∂P.measure, |x| ≤ 2 * η / d) ∧ (∀ᵐ x ∂Q.measure, |x| ≤ 2 * η / d) ∧
      standardizedMeasure μ m d = twoClusterMeasure P Q (μ.real (Ioi ((a + b) / 2))) := by
  let s := Ioi ((a + b) / 2)
  let p := μ.real s
  have hs : MeasurableSet s := measurableSet_Ioi
  have hpos : μ s ≠ 0 := by
    intro hz
    have h := hp.1
    change 0 < (μ s).toReal at h
    rw [hz, ENNReal.toReal_zero] at h
    exact lt_irrefl 0 h
  have hcomp : μ sᶜ ≠ 0 := by
    have hreal : 0 < μ.real sᶜ := by rw [probReal_compl_eq_one_sub hs]; exact sub_pos.2 hp.2
    intro hz
    change 0 < (μ sᶜ).toReal at hreal
    rw [hz, ENNReal.toReal_zero] at hreal
    exact lt_irrefl 0 hreal
  let μ0 := ProbabilityTheory.cond μ sᶜ
  let μ1 := ProbabilityTheory.cond μ s
  letI : IsProbabilityMeasure μ0 := cond_isProbabilityMeasure hcomp
  letI : IsProbabilityMeasure μ1 := cond_isProbabilityMeasure hpos
  have hb0 : ∀ᵐ x ∂μ0, x ∈ Icc (a - η) (a + η) := cond_two_intervals_lower μ a b η hgap hb
  have hb1 : ∀ᵐ x ∂μ1, x ∈ Icc (b - η) (b + η) := cond_two_intervals_upper μ a b η hgap hb
  let m0 := ∫ x, x ∂μ0
  let m1 := ∫ x, x ∂μ1
  let d := m1 - m0
  have hm0 : m0 ∈ Icc (a - η) (a + η) := integral_id_mem_interval μ0 _ _ hb0
  have hm1 : m1 ∈ Icc (b - η) (b + η) := integral_id_mem_interval μ1 _ _ hb1
  have hd : 0 < d := by dsimp only [d]; linarith [hm0.2, hm1.1]
  have hdb : d ∈ Icc (b - a - 2 * η) (b - a + 2 * η) := by
    constructor <;> dsimp only [d] <;> linarith [hm0.1, hm0.2, hm1.1, hm1.2]
  obtain ⟨P, hP, hPb⟩ := centered_interval_noise_exists μ0 (a - η) (a + η) d hb0 hd
  obtain ⟨Q, hQ, hQb⟩ := centered_interval_noise_exists μ1 (b - η) (b + η) d hb1 hd
  have haη : (a + η) - (a - η) = 2 * η := by ring
  have hbη : (b + η) - (b - η) = 2 * η := by ring
  rw [haη] at hPb
  rw [hbη] at hQb
  refine ⟨P, Q, m0, d, hd, hdb, hPb, hQb, ?_⟩
  have hmix : mixtureMeasure μ0 μ1 p = μ := conditioned_mixture_identity μ s hs hpos hcomp
  have hmap := congrArg (fun ν : Measure ℝ => ν.map (fun x => (x - m0) / d)) hmix
  dsimp only at hmap
  rw [mixtureMeasure, Measure.map_add _ _ (by fun_prop), Measure.map_smul, Measure.map_smul] at hmap
  have hupper : standardizedMeasure μ1 m0 d = Q.measure.map (fun x => 1 + x) := by
    rw [hQ]
    unfold standardizedMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    change (x - m0) / d = 1 + (x - m1) / d
    field_simp [hd.ne']
    dsimp only [d]
    ring
  change mixtureMeasure (standardizedMeasure μ0 m0 d) (standardizedMeasure μ1 m0 d) p =
    standardizedMeasure μ m0 d at hmap
  rw [← hP, hupper] at hmap
  exact hmap.symm

theorem standardized_two_cluster_representation (Z : StandardizedLaw) (a b η : ℝ)
    (hη : 0 ≤ η) (hgap : 2 * η < b - a)
    (hb : ∀ᵐ x ∂Z.measure, x ∈ Icc (a - η) (a + η) ∪ Icc (b - η) (b + η))
    (hp : Z.measure.real (Ioi ((a + b) / 2)) ∈ Ioo 0 1) :
    ∃ (P Q : CenteredFourthLaw) (d : ℝ), 0 < d ∧
      d ∈ Icc (b - a - 2 * η) (b - a + 2 * η) ∧
      (∀ᵐ x ∂P.measure, |x| ≤ 2 * η / d) ∧ (∀ᵐ x ∂Q.measure, |x| ≤ 2 * η / d) ∧
      standardizedTwoClusterLaw P Q (Z.measure.real (Ioi ((a + b) / 2))) hp = Z := by
  obtain ⟨P, Q, m, d, hd, hdb, hP, hQ, hrep⟩ := bounded_two_cluster_affine_representation Z.measure a b η hη hgap hb hp
  exact ⟨P, Q, d, hd, hdb, hP, hQ, standardizedTwoCluster_eq_of_affine_representation Z P Q _ hp m d hd hrep⟩

end BerryEsseen
