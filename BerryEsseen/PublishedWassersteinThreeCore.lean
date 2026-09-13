import BerryEsseen.Statement
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The cube roots of the actual cubic transport costs of probability couplings. -/
def transportThreeCosts (μ ν : Measure ℝ) : Set ℝ :=
  {r | ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
    π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) π ∧
    r = (∫ z, |z.1 - z.2| ^ 3 ∂π) ^ (1 / 3 : ℝ)}

/-- The real three-Wasserstein distance on laws with finite third moments. -/
def wassersteinThree (μ ν : Measure ℝ) : ℝ := sInf (transportThreeCosts μ ν)

theorem cubic_cost_integrable_of_marginals (μ ν : Measure ℝ)
    (π : Measure (ℝ × ℝ)) (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hμ : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hν : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) π := by
  have hx : Integrable (fun z : ℝ × ℝ => |z.1| ^ 3) π := by
    rw [← hfst] at hμ
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).1 hμ
  have hy : Integrable (fun z : ℝ × ℝ => |z.2| ^ 3) π := by
    rw [← hsnd] at hν
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).1 hν
  apply ((hx.add hy).const_mul 4).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |z.1 - z.2| ^ 3)]
  have h1 : |z.1 - z.2| ≤ |z.1| + |z.2| := abs_sub _ _
  have h2 := pow_le_pow_left₀ (abs_nonneg (z.1 - z.2)) h1 3
  have h3 := mul_nonneg (add_nonneg (abs_nonneg z.1) (abs_nonneg z.2))
    (sq_nonneg (|z.1| - |z.2|))
  simp only [Pi.add_apply]
  nlinarith

theorem transportThreeCosts_nonempty (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hν : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    (transportThreeCosts μ ν).Nonempty := by
  have hfst : (μ.prod ν).map Prod.fst = μ := by simp
  have hsnd : (μ.prod ν).map Prod.snd = ν := by simp
  refine ⟨_, μ.prod ν, inferInstance, hfst, hsnd,
    cubic_cost_integrable_of_marginals μ ν (μ.prod ν) hfst hsnd hμ hν, rfl⟩

theorem transportThreeCosts_bddBelow (μ ν : Measure ℝ) :
    BddBelow (transportThreeCosts μ ν) := by
  refine ⟨0, ?_⟩
  rintro r ⟨π, hp, hfst, hsnd, hi, rfl⟩
  exact Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _

theorem wassersteinThree_nonneg (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hν : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    0 ≤ wassersteinThree μ ν := by
  apply le_csInf (transportThreeCosts_nonempty μ ν hμ hν)
  rintro r ⟨π, hp, hfst, hsnd, hi, rfl⟩
  exact Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _

theorem wassersteinThree_le_coupling_cost (μ ν : Measure ℝ)
    (π : Measure (ℝ × ℝ)) (hp : IsProbabilityMeasure π)
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = ν)
    (hi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) π) :
    wassersteinThree μ ν ≤ (∫ z, |z.1 - z.2| ^ 3 ∂π) ^ (1 / 3 : ℝ) :=
  csInf_le (transportThreeCosts_bddBelow μ ν) ⟨π, hp, hfst, hsnd, hi, rfl⟩

end BerryEsseen
