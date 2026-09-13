import BerryEsseen.WassersteinBounds
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual probability couplings for Appendix A's truncation and affine costs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_wasserstein_common_source {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun x => |f x - g x|) ρ) :
    wassersteinOne (ρ.map f) (ρ.map g) ≤ ∫ x, |f x - g x| ∂ρ := by
  let A := fun x => (f x, g x)
  have hA : Measurable A := hf.prodMk hg
  let π := ρ.map A
  have hp : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map hA.aemeasurable
  have hfst : π.map Prod.fst = ρ.map f := by
    rw [Measure.map_map measurable_fst hA]
    rfl
  have hsnd : π.map Prod.snd = ρ.map g := by
    rw [Measure.map_map measurable_snd hA]
    rfl
  have hπi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) π :=
    (integrable_map_measure (by fun_prop) hA.aemeasurable).mpr hi
  have h := wassersteinOne_le_coupling_cost (ρ.map f) (ρ.map g) π hp hfst hsnd hπi
  rw [integral_map hA.aemeasurable (by fun_prop)] at h
  exact h

/-- Keep X on s; outside s use an independent sample of cond μ s. -/
def manuscriptConditionalReplacement (s : Set ℝ) (z : ℝ × ℝ) : ℝ :=
  by classical exact if z.1 ∈ s then z.1 else z.2

theorem manuscriptConditionalReplacement_measurable (s : Set ℝ) (hs : MeasurableSet s) :
    Measurable (manuscriptConditionalReplacement s) := by
  classical
  exact Measurable.ite (hs.preimage measurable_fst) measurable_fst measurable_snd

theorem manuscriptConditionalReplacement_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Set ℝ) (hs : MeasurableSet s) (hnz : μ s ≠ 0) :
    (μ.prod (ProbabilityTheory.cond μ s)).map (manuscriptConditionalReplacement s) =
      ProbabilityTheory.cond μ s := by
  classical
  let ν := ProbabilityTheory.cond μ s
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  apply Measure.ext
  intro t ht
  rw [Measure.map_apply (manuscriptConditionalReplacement_measurable s hs) ht]
  have he : manuscriptConditionalReplacement s ⁻¹' t =
      (s ∩ t) ×ˢ (univ : Set ℝ) ∪ sᶜ ×ˢ t := by
    ext z
    by_cases hz : z.1 ∈ s <;> simp [manuscriptConditionalReplacement, hz]
  have hd : Disjoint ((s ∩ t) ×ˢ (univ : Set ℝ)) (sᶜ ×ˢ t) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact hz'.1 hz.1.1
  rw [he, measure_union hd ((hs.compl).prod ht), Measure.prod_prod, Measure.prod_prod]
  change μ (s ∩ t) * ν univ + μ sᶜ * ν t = ν t
  rw [measure_univ, mul_one]
  have hcond : μ (s ∩ t) = μ s * ν t := by
    dsimp only [ν, ProbabilityTheory.cond]
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply ht, Set.inter_comm t s,
      ← mul_assoc, ENNReal.mul_inv_cancel hnz (measure_ne_top _ _), one_mul]
  have hsum : μ s + μ sᶜ = 1 := by
    simpa only [measure_univ] using measure_add_measure_compl hs (μ := μ)
  rw [hcond, ← add_mul, hsum, one_mul]

theorem manuscript_wasserstein_conditioning_actual
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ) (hs : MeasurableSet s) (hnz : μ s ≠ 0)
    (hμ : Integrable (fun x : ℝ => x) μ) (R S : ℝ)
    (hx : ∀ᵐ x ∂μ, |x| ≤ R) (hy : ∀ᵐ x ∂ProbabilityTheory.cond μ s, |x| ≤ S) :
    wassersteinOne μ (ProbabilityTheory.cond μ s) ≤ (R + S) * μ.real sᶜ := by
  classical
  let ν := ProbabilityTheory.cond μ s
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  have hν : Integrable (fun x : ℝ => x) ν := conditional_integrable_real μ s hnz _ hμ
  let D := manuscriptConditionalReplacement s
  have hD : Measurable D := manuscriptConditionalReplacement_measurable s hs
  have hi : Integrable (fun z : ℝ × ℝ => |z.1 - D z|) (μ.prod ν) := by
    apply ((hμ.abs.comp_fst ν).add (hν.abs.comp_snd μ)).mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_abs]
    by_cases hz : z.1 ∈ s
    · simp only [D, manuscriptConditionalReplacement, if_pos hz, sub_self, abs_zero]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · simpa only [D, manuscriptConditionalReplacement, if_neg hz] using abs_sub z.1 z.2
  have hW := manuscript_wasserstein_common_source (μ.prod ν) Prod.fst D measurable_fst hD hi
  rw [Measure.map_fst_prod, measure_univ, one_smul, manuscriptConditionalReplacement_law μ s hs hnz] at hW
  apply hW.trans
  rw [integral_prod _ hi]
  have hbound : (∫ x, ∫ y, |x - D (x, y)| ∂ν ∂μ) ≤ ∫ x, (sᶜ).indicator (fun _ => R + S) x ∂μ := by
    apply integral_mono_ae hi.integral_prod_left ((integrable_const (R + S)).indicator hs.compl)
    filter_upwards [hx] with x hx
    by_cases hxs : x ∈ s
    · simp [D, manuscriptConditionalReplacement, hxs]
    · have hpoint : ∀ᵐ y ∂ν, |x - y| ≤ R + S := by
        filter_upwards [hy] with y hy
        exact (abs_sub x y).trans (by linarith only [hx, hy])
      have hb := integral_mono_ae ((integrable_const x).sub hν).abs (integrable_const (R + S)) hpoint
      simpa only [D, manuscriptConditionalReplacement, hxs, if_false,
        indicator_of_mem (show x ∈ sᶜ from hxs), integral_const, probReal_univ, one_smul] using hb
  apply hbound.trans_eq
  rw [integral_indicator hs.compl]
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  ring

/-- The actual deterministic coupling W = σY + m on the standardized law. -/
theorem manuscript_wasserstein_affine_standardized_actual
    (μ : Measure ℝ) (Z : StandardizedLaw) (m σ : ℝ) (hσ : 0 < σ)
    (hmap : Z.measure = standardizedMeasure μ m σ) :
    wassersteinOne μ Z.measure ≤ |m| + |σ - 1| * (∫ y, |y| ∂Z.measure) ∧
    wassersteinOne μ Z.measure ≤ |m| + |σ - 1| := by
  have hinv := inverse_standardized_representation μ Z m σ hσ hmap
  have hi : Integrable (fun x => |(σ * x + m) - x|) Z.measure :=
    (((Z.first_integrable.const_mul σ).add (integrable_const m)).sub Z.first_integrable).abs
  have hw := manuscript_wasserstein_common_source Z.measure (fun x => σ * x + m) id (by fun_prop) measurable_id hi
  rw [Measure.map_id] at hw
  rw [← hinv] at hw
  change wassersteinOne μ Z.measure ≤ ∫ x, |σ * x + m - x| ∂Z.measure at hw
  have hcost := integral_mono_ae hi
    ((Z.first_integrable.abs.const_mul |σ - 1|).add (integrable_const |m|)) (by
      filter_upwards [] with x
      change |σ * x + m - x| ≤ |σ - 1| * |x| + |m|
      rw [show σ * x + m - x = (σ - 1) * x + m by ring]
      simpa only [abs_mul] using abs_add_le ((σ - 1) * x) m)
  simp only [Pi.add_apply] at hcost
  rw [integral_add (Z.first_integrable.abs.const_mul _) (integrable_const _), integral_const_mul] at hcost
  simp only [integral_const, probReal_univ, one_smul] at hcost
  have hfirst : wassersteinOne μ Z.measure ≤ |m| + |σ - 1| * (∫ y, |y| ∂Z.measure) := by linarith only [hw, hcost]
  refine ⟨hfirst, ?_⟩
  have hb := mul_le_mul_of_nonneg_left (standardized_first_absolute_moment_le_one Z) (abs_nonneg (σ - 1))
  linarith only [hfirst, hb]

end BerryEsseen
