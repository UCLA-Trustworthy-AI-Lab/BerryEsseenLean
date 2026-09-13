import BerryEsseen.RawNormalization
import BerryEsseen.ClusterRepresentation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def appendixEtaStar : ℝ := Real.exp (-2 * appendixA)

theorem appendixEtaStar_bounds :
    appendixEtaStar ∈ Ioo 0 (1 / 4) ∧ appendixEtaStar ≤ 1 / 1000 ∧
      4 * appendixEtaStar ≤ Real.exp (-appendixA) := by
  have hε := appendix_noise_and_cutoff_bounds.1
  have hpos := Real.exp_pos (-appendixA)
  have he : appendixEtaStar = Real.exp (-appendixA) ^ 2 := by
    unfold appendixEtaStar
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [he]
  constructor
  · constructor
    · positivity
    · nlinarith
  · constructor <;> nlinarith

theorem pE_effective_interior : 41 / 100 < pE ∧ pE < 43 / 100 := by
  have hs := sqrt10_bounds
  unfold pE
  constructor <;> nlinarith [sqrt10_sq]

theorem effective_cluster_probability (p : ℝ) (hp : |p - pE| < appendixEtaStar) :
    p ∈ Icc (2 / 5) (9 / 20) := by
  have ha := (abs_lt.mp hp)
  have hη := appendixEtaStar_bounds.2.1
  have hE := pE_effective_interior
  constructor <;> linarith [ha.1, ha.2, hE.1, hE.2]

theorem upper_interval_mass_eq (μ : Measure ℝ) (η : ℝ) (hη : η < 1 / 2)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η)) :
    μ.real (Ioi (1 / 2)) = μ.real (Icc (1 - η) (1 + η)) := by
  apply measureReal_congr
  filter_upwards [hb] with x hx
  change (1 / 2 < x) = (1 - η ≤ x ∧ x ≤ 1 + η)
  apply propext
  rcases hx with hx | hx
  · constructor
    · intro h
      exfalso
      linarith [hx.2]
    · intro h
      linarith [h.1]
  · constructor
    · intro _
      exact hx
    · intro _
      linarith [hx.1]

theorem reflected_intervals_support (μ : Measure ℝ) (η : ℝ)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η)) :
    ∀ᵐ x ∂μ.map (fun y => 1 - y), x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η) := by
  apply (ae_map_iff (by fun_prop) (measurableSet_Icc.union measurableSet_Icc)).2
  filter_upwards [hb] with x hx
  rcases hx with hx | hx
  · right
    constructor <;> linarith [hx.1, hx.2]
  · left
    constructor <;> linarith [hx.1, hx.2]

theorem reflected_upper_interval_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : η < 1 / 2)
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-η) η ∪ Icc (1 - η) (1 + η)) :
    (μ.map (fun y => 1 - y)).real (Icc (1 - η) (1 + η)) =
      1 - μ.real (Icc (1 - η) (1 + η)) := by
  have he : (μ.map (fun y => 1 - y)).real (Icc (1 - η) (1 + η)) =
      μ.real (Icc (-η) η) := by
    unfold Measure.real
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
    congr 2
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he, ← probReal_compl_eq_one_sub measurableSet_Icc]
  apply measureReal_congr
  filter_upwards [hb] with x hx
  apply propext
  change (x ∈ Icc (-η) η) ↔ x ∉ Icc (1 - η) (1 + η)
  constructor
  · intro hlo hhi
    linarith [hlo.2, hhi.1]
  · intro hhi
    exact hx.resolve_right hhi

theorem effective_interval_standardization (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar) :
    ∃ (Z : StandardizedLaw) (m σ : ℝ), 0 < σ ∧
      Z.measure = standardizedMeasure μ m σ ∧
      ∀ n, appendixNStar ≤ n → sSup (range (normalizedDiscrepancy Z n)) < cE := by
  have hη := appendixEtaStar_bounds
  have hmass := upper_interval_mass_eq μ appendixEtaStar (by linarith [hη.1.2]) hb
  let p := μ.real (Ioi (1 / 2))
  have hpI : p ∈ Icc (2 / 5) (9 / 20) := by
    apply effective_cluster_probability
    simpa only [p, hmass] using hp
  have hp01 := (effective_binomial_parameters p hpI).1
  have hb' : ∀ᵐ x ∂μ, x ∈ Icc (0 - appendixEtaStar) (0 + appendixEtaStar) ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) := by simpa only [zero_sub, zero_add] using hb
  obtain ⟨P, Q, m, d, hd, hdb, hP, hQ, hrep⟩ :=
    bounded_two_cluster_affine_representation μ 0 1 appendixEtaStar hη.1.1.le
      (by linarith [hη.1.2]) hb' (by simpa [p] using hp01)
  have hdhalf : 1 / 2 ≤ d := by norm_num at hdb; linarith [hdb.1, hη.1.2]
  have hnoise : 2 * appendixEtaStar / d ≤ Real.exp (-appendixA) := by
    calc
      2 * appendixEtaStar / d ≤ 4 * appendixEtaStar := by
        apply (div_le_iff₀ hd).mpr
        nlinarith [hη.1.1]
      _ ≤ _ := hη.2.2
  have hPb := hP.mono (fun _ hx => hx.trans hnoise)
  have hQb := hQ.mono (fun _ hx => hx.trans hnoise)
  let Z := standardizedTwoClusterLaw P Q p hp01
  let σ := Real.sqrt (clusterVariance P Q p)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp01)
  refine ⟨Z, m + d * p, d * σ, mul_pos hd hσ, ?_, ?_⟩
  · change (standardizedTwoClusterLaw P Q p hp01).measure = _
    rw [standardizedTwoClusterLaw_measure]
    change standardizedMeasure (twoClusterMeasure P Q p) p σ = _
    have hrep' : standardizedMeasure μ m d = twoClusterMeasure P Q p := by simpa [p] using hrep
    rw [← hrep']
    unfold standardizedMeasure
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    change ((x - m) / d - p) / σ = (x - (m + d * p)) / (d * σ)
    field_simp [hd.ne', hσ.ne']
    <;> ring
  · intro n hn
    exact effective_cluster_stability S B I U P Q p hpI hPb hQb n hn

theorem effective_interval_stability (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ x ∂μ, x ∈ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar ∨
      |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)| < appendixEtaStar)
    (n : ℕ) (hn : appendixNStar ≤ n) : rawNormalizedConstant μ n < cE := by
  have hn1 : 1 ≤ n := by have h := (appendix_sample_size_bounds n hn).1; omega
  rcases hp with hp | hp
  · obtain ⟨Z, m, σ, hσ, hmap, hbound⟩ := effective_interval_standardization S B I U μ hb hp
    rw [rawNormalizedConstant_eq μ Z m σ hσ hmap n hn1]
    exact hbound n hn
  · let ν := μ.map (fun x => 1 - x)
    letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
    have hbν := reflected_intervals_support μ appendixEtaStar hb
    have hpν : |ν.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar := by
      rw [show ν = μ.map (fun x => 1 - x) from rfl,
        reflected_upper_interval_mass μ appendixEtaStar (by linarith [appendixEtaStar_bounds.1.2]) hb]
      have he : 1 - μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE =
          -(μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)) := by ring
      rw [he, abs_neg]
      exact hp
    obtain ⟨Z, m, σ, hσ, hmap, hbound⟩ := effective_interval_standardization S B I U ν hbν hpν
    have hmap' : (reflectedLaw Z).measure = standardizedMeasure μ (1 - m) σ := by
      change Z.measure.map (fun x => -x) = _
      rw [hmap]
      unfold standardizedMeasure
      change ((μ.map (fun x => 1 - x)).map (fun x => (x - m) / σ)).map (fun x => -x) = _
      rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      dsimp only [Function.comp_def]
      ring
    rw [rawNormalizedConstant_eq μ (reflectedLaw Z) (1 - m) σ hσ hmap' n hn1,
      normalizedDiscrepancy_sup_reflected Z n hn1]
    exact hbound n hn

theorem effective_interval_stability_support (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : μ.support ⊆ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar))
    (hp : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar ∨
      |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - (1 - pE)| < appendixEtaStar)
    (n : ℕ) (hn : appendixNStar ≤ n) : rawNormalizedConstant μ n < cE :=
  effective_interval_stability S B I U μ (by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hb hx) hp n hn

theorem two_interval_cluster_stability (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) (U : PublishedNonuniformBound) :
    ∃ η ∈ Ioo (0 : ℝ) (1 / 4), ∃ N : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      μ.support ⊆ Icc (-η) η ∪ Icc (1 - η) (1 + η) →
      (|μ.real (Icc (1 - η) (1 + η)) - pE| < η ∨
        |μ.real (Icc (1 - η) (1 + η)) - (1 - pE)| < η) →
      ∀ n, N ≤ n → rawNormalizedConstant μ n ≤ cE := by
  refine ⟨appendixEtaStar, appendixEtaStar_bounds.1, appendixNStar, ?_⟩
  intro μ hprob hb hp n hn
  letI := hprob
  exact (effective_interval_stability_support S B I U μ hb hp n hn).le

end BerryEsseen
