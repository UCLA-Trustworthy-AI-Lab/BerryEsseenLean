import BerryEsseen.EffectiveSelection
import BerryEsseen.EffectiveIntervals
import BerryEsseen.Attainment
import BerryEsseen.GlobalParameters

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The explicit-threshold proof below uses this precise support conclusion.
This is a proposition definition, not an assumption declared true. -/
def EffectiveConfinementInput : Prop :=
  ∀ (P : StandardizedLaw) (n : ℕ) (t : ℝ),
    appendixNConf ≤ n →
    signedRatio P (n - 1) t = extremalConstant n →
    cE < extremalConstant n →
    P.measure.support ⊆ Icc (-6) 6 →
    scaledDrop extremalConstant n ≤ 20 / Real.sqrt (n : ℝ) →
    let μ := P.measure.map (fun x => pE + sigmaE * x)
    μ.support ⊆ Icc (-appendixEtaStar / 2) (appendixEtaStar / 2) ∪
      Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2) ∧
    |μ.real (Ioi (1 / 2)) - pE| < appendixEtaStar

theorem explicitThreshold_eq_twice_conf : explicitThreshold = 2 * appendixNConf := by
  unfold explicitThreshold appendixNConf appendixA
  norm_num

theorem appendixNConf_ge_two : 2 ≤ appendixNConf := by
  have h := (appendix_sample_size_bounds appendixNConf
    (appendix_conf_sample_size appendixNConf le_rfl).1).1
  omega

theorem selected_drop_effective_bound (N n : ℕ) (hN : 4 ≤ N) (hn : 1 ≤ n)
    (hnN : n ≤ N)
    (hd : scaledDrop extremalConstant n ≤ 10 / Real.sqrt ((N - 2 : ℕ) : ℝ)) :
    scaledDrop extremalConstant n ≤ 20 / Real.sqrt (n : ℝ) := by
  have hr : 0 < Real.sqrt ((N - 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0 < N - 2 by omega))
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0 < n by omega))
  have hcast : (n : ℝ) ≤ 4 * ((N - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 4 * (N - 2) by omega)
  have hroot : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt ((N - 2 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),
      Real.sq_sqrt (Nat.cast_nonneg (N - 2))]
  exact hd.trans ((div_le_div_iff₀ hr hs).mpr (by linarith))

theorem esseen_affine_standardization (P : StandardizedLaw) :
    P.measure = standardizedMeasure (P.measure.map (fun x => pE + sigmaE * x)) pE sigmaE := by
  rw [standardizedMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun x : ℝ => (x - pE) / sigmaE) ∘ (fun x : ℝ => pE + sigmaE * x)) = id := by
    funext x
    dsimp only [Function.comp_def, id_eq]
    field_simp [sigmaE_pos.ne']
    <;> ring
  rw [he, Measure.map_id]

theorem confined_extremizer_impossible (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hn : appendixNConf ≤ n) (t : ℝ)
    (hatt : signedRatio P (n - 1) t = extremalConstant n)
    (hviol : cE < extremalConstant n)
    (hb : (P.measure.map (fun x => pE + sigmaE * x)).support ⊆
      Icc (-appendixEtaStar / 2) (appendixEtaStar / 2) ∪
        Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2))
    (hp : |(P.measure.map (fun x => pE + sigmaE * x)).real (Ioi (1 / 2)) - pE| < appendixEtaStar) :
    False := by
  let μ := P.measure.map (fun x => pE + sigmaE * x)
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hη := appendixEtaStar_bounds.1
  have hb' : μ.support ⊆ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) := by
    intro x hx
    rcases hb hx with hx | hx
    · left
      constructor <;> linarith [hx.1, hx.2]
    · right
      constructor <;> linarith [hx.1, hx.2]
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-appendixEtaStar) appendixEtaStar ∪
      Icc (1 - appendixEtaStar) (1 + appendixEtaStar) := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hb' hx
  have hp' : |μ.real (Icc (1 - appendixEtaStar) (1 + appendixEtaStar)) - pE| < appendixEtaStar := by
    rw [← upper_interval_mass_eq μ appendixEtaStar (by linarith [hη.2]) hae]
    exact hp
  have hNstar := (appendix_conf_sample_size n hn).1
  have hn1 : 1 ≤ n := by have := appendixNConf_ge_two.trans hn; omega
  have hs := effective_interval_stability_support S B I U μ hb' (Or.inl hp') n hNstar
  rw [rawNormalizedConstant_eq μ P pE sigmaE sigmaE_pos
    (esseen_affine_standardization P) n hn1] at hs
  have he : n - 1 + 1 = n := by omega
  have hratio : signedRatio P (n - 1) t ≤
      sSup (range (normalizedDiscrepancy P n)) := by
    calc
      _ ≤ |signedRatio P (n - 1) t| := le_abs_self _
      _ = normalizedDiscrepancy P n (t / Real.sqrt ((n - 1 : ℕ) + 1 : ℝ)) := by
        simpa only [he] using abs_signedRatio_eq_normalized P (n - 1) t
      _ ≤ _ := le_csSup (normalizedDiscrepancy_range_bddAbove P n hn1) (mem_range_self _)
  rw [hatt] at hratio
  exact (not_lt_of_ge (hratio.trans hs.le)) hviol

/-- Conditional finite reduction: the only still-to-be-instantiated hypothesis
is the explicit confinement conclusion. No asymptotic main theorem is used. -/
theorem explicit_claim_of_effective_confinement (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (U : PublishedNonuniformBound) (hconf : EffectiveConfinementInput) : ExplicitClaim := by
  intro N hN P
  have hNconf : 2 * appendixNConf ≤ N := by rwa [explicitThreshold_eq_twice_conf] at hN
  have hN4 : 4 ≤ N := by have := appendixNConf_ge_two; omega
  have hN1 : 1 ≤ N := by omega
  apply (BoundAt_iff_normalized P N hN1).2
  intro x
  apply (normalizedDiscrepancy_le_extremalConstant H P N hN1 x).trans
  by_contra hC
  have hC : cE < extremalConstant N := lt_of_not_ge hC
  obtain ⟨n, hnm, hnN, hcn, hd1, hd2, hsupp⟩ :=
    effective_selection_with_support H N hN4 hC
  have hnconf : appendixNConf ≤ n := by
    unfold finiteHalfIndex at hnm
    omega
  have hn2 : 2 ≤ n := appendixNConf_ge_two.trans hnconf
  have he : n - 1 + 1 = n := by omega
  obtain ⟨Q, t, hatt, hβ1, hβ2⟩ := extremal_attainment H (n - 1) (by rwa [he])
  rw [he] at hatt
  have hb := (hsupp Q t hatt).trans Ioo_subset_Icc_self
  have hd := selected_drop_effective_bound N n hN4 (by omega) hnN hd2
  obtain ⟨hbc, hpc⟩ := hconf Q n t hnconf hatt hcn hb hd
  exact confined_extremizer_impossible S B I U Q n hnconf t hatt hcn hbc hpc

end BerryEsseen
