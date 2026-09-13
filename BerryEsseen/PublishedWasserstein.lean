import BerryEsseen.RawNormalization

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- Actual integrable costs of probability couplings with the given marginals. -/
def transportCosts (μ ν : Measure ℝ) : Set ℝ :=
  {r | ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
    π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) π ∧ r = ∫ z, |z.1 - z.2| ∂π}

def wassersteinOne (μ ν : Measure ℝ) : ℝ := sInf (transportCosts μ ν)

def dualTransportValues (μ ν : Measure ℝ) : Set ℝ :=
  {r | ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ r = (∫ x, f x ∂μ) - ∫ x, f x ∂ν}

/-- Standard published duality; no instance of this premise is asserted.
See reference/published-wasserstein.md for the exact version and correspondence. -/
structure PublishedWassersteinDuality : Prop where
  eq_dual : ∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    Integrable (fun x : ℝ => x) μ → Integrable (fun x : ℝ => x) ν →
    wassersteinOne μ ν = sSup (dualTransportValues μ ν)

theorem transportCosts_bddBelow (μ ν : Measure ℝ) : BddBelow (transportCosts μ ν) := by
  refine ⟨0, ?_⟩
  rintro r ⟨π, hp, hfst, hsnd, hi, rfl⟩
  exact integral_nonneg (fun z => abs_nonneg _)

theorem wassersteinOne_le_coupling_cost (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ))
    (hp : IsProbabilityMeasure π) (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2|) π) :
    wassersteinOne μ ν ≤ ∫ z, |z.1 - z.2| ∂π :=
  csInf_le (transportCosts_bddBelow μ ν) ⟨π, hp, hfst, hsnd, hi, rfl⟩

theorem dualTransportValues_nonempty (μ ν : Measure ℝ) : (dualTransportValues μ ν).Nonempty := by
  refine ⟨0, (fun _ => 0), ?_, ?_⟩
  · exact LipschitzWith.of_dist_le_mul (by simp)
  · simp

theorem lipschitz_one_pointwise (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (x y : ℝ) :
    |f x - f y| ≤ |x - y| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul x y

theorem lipschitz_one_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    Integrable f μ := by
  apply (hi.abs.add (integrable_const |f 0|)).mono' hf.continuous.measurable.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  change |f x| ≤ |x| + |f 0|
  have h := lipschitz_one_pointwise f hf x 0
  simp only [sub_zero] at h
  calc
    |f x| = |f x - f 0 + f 0| := by congr 1; ring
    _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem lipschitz_one_integral_center (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    |(∫ x, f x ∂μ) - f 0| ≤ ∫ x, |x| ∂μ := by
  have hfi := lipschitz_one_integrable μ hi f hf
  have hid : (∫ x, f x ∂μ) - f 0 = ∫ x, f x - f 0 ∂μ := by
    rw [integral_sub hfi (integrable_const _)]
    simp
  rw [hid]
  calc
    _ ≤ ∫ x, |f x - f 0| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x - f 0) (μ := μ)
    _ ≤ _ := integral_mono_ae (hfi.sub (integrable_const _)).abs hi.abs (by
      filter_upwards [] with x
      simpa only [sub_zero] using lipschitz_one_pointwise f hf x 0)

theorem dualTransportValues_bddAbove (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    BddAbove (dualTransportValues μ ν) := by
  refine ⟨(∫ x, |x| ∂μ) + ∫ x, |x| ∂ν, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  have h1 := lipschitz_one_integral_center μ hμ f hf
  have h2 := lipschitz_one_integral_center ν hν f hf
  linarith [le_abs_self ((∫ x, f x ∂μ) - f 0), neg_abs_le ((∫ x, f x ∂ν) - f 0)]

theorem wassersteinOne_le_of_lipschitz (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν)
    (R : ℝ) (h : ∀ f : ℝ → ℝ, LipschitzWith 1 f → (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ R) :
    wassersteinOne μ ν ≤ R := by
  rw [K.eq_dual μ ν inferInstance inferInstance hμ hν]
  apply csSup_le (dualTransportValues_nonempty μ ν)
  rintro r ⟨f, hf, rfl⟩
  exact h f hf

theorem lipschitz_integral_le_wassersteinOne (K : PublishedWassersteinDuality)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν)
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤ wassersteinOne μ ν := by
  rw [K.eq_dual μ ν inferInstance inferInstance hμ hν]
  exact le_csSup (dualTransportValues_bddAbove μ ν hμ hν) ⟨f, hf, rfl⟩

theorem wassersteinOne_triangle (K : PublishedWassersteinDuality)
    (μ ν ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν)
    (hρ : Integrable (fun x : ℝ => x) ρ) :
    wassersteinOne μ ρ ≤ wassersteinOne μ ν + wassersteinOne ν ρ := by
  apply wassersteinOne_le_of_lipschitz K μ ρ hμ hρ
  intro f hf
  linarith [lipschitz_integral_le_wassersteinOne K μ ν hμ hν f hf,
    lipschitz_integral_le_wassersteinOne K ν ρ hν hρ f hf]

end BerryEsseen
