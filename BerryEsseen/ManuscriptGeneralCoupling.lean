import BerryEsseen.PublishedWassersteinThreeCore
import BerryEsseen.ManuscriptIndependentCopy

/-! Actual near-optimal cubic couplings and their quadratic convergence.
No coupling theorem is postulated: the measures are selected from the
nonempty set defining the actual three-Wasserstein infimum. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

/-- A short finite-to-sfinite instance for the product coupling space. -/
instance manuscriptCoupling_sfinite (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π] : SFinite π := by
  letI : SigmaFinite π := IsFiniteMeasure.toSigmaFinite π
  infer_instance

theorem manuscript_near_cubic_coupling (P Q : StandardizedLaw) (ε : ℝ) (hε : 0 < ε) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      π.map Prod.fst = P.measure ∧ π.map Prod.snd = Q.measure ∧
      Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) π ∧
      (∫ z, |z.1 - z.2| ^ 3 ∂π) ^ (1 / 3 : ℝ) < wassersteinThree P.measure Q.measure + ε := by
  obtain ⟨r, hr, he⟩ := exists_lt_of_csInf_lt
    (transportThreeCosts_nonempty P.measure Q.measure P.third_integrable Q.third_integrable)
    (show sInf (transportThreeCosts P.measure Q.measure) <
      wassersteinThree P.measure Q.measure + ε by unfold wassersteinThree; linarith)
  obtain ⟨π, hp, hf, hs, hi, rfl⟩ := hr
  exact ⟨π, hp, hf, hs, hi, he⟩

theorem manuscript_square_le_scaled_cube (x r : ℝ) (hr : 0 < r) :
    x ^ 2 ≤ r ^ 2 + |x| ^ 3 / r := by
  by_cases hx : |x| ≤ r
  · have hh := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hx : r ≤ |x| := (lt_of_not_ge hx).le
    have hh := mul_le_mul_of_nonneg_right hx (sq_nonneg x)
    have hcube : |x| ^ 3 = |x| * x ^ 2 := by rw [← sq_abs x]; ring
    have hb : x ^ 2 ≤ |x| ^ 3 / r := by
      apply (le_div_iff₀ hr).2
      rw [hcube]
      nlinarith only [hh]
    exact hb.trans (le_add_of_nonneg_left (sq_nonneg r))

theorem manuscript_coupled_square_integrable (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) π) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) π := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa using manuscript_square_le_scaled_cube (z.1 - z.2) 1 (by norm_num)

theorem manuscript_quadratic_cost_bound (π : Measure (ℝ × ℝ))
    [IsProbabilityMeasure π]
    (hi : Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) π) (r : ℝ) (hr : 0 < r) :
    (∫ z, (z.1 - z.2) ^ 2 ∂π) ≤ r ^ 2 + (∫ z, |z.1 - z.2| ^ 3 ∂π) / r := by
  have h := integral_mono (manuscript_coupled_square_integrable π hi)
    ((integrable_const (r ^ 2)).add (hi.div_const r))
    (fun z => manuscript_square_le_scaled_cube (z.1 - z.2) r hr)
  simp only [Pi.add_apply] at h
  simpa only [integral_add (integrable_const (r ^ 2)) (hi.div_const r),
    integral_const, probReal_univ, one_smul, integral_div] using h

theorem manuscript_cubic_coupling_costs_tendsto
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0)) :
    ∃ π : ℕ → Measure (ℝ × ℝ),
      (∀ j, IsProbabilityMeasure (π j)) ∧
      (∀ j, (π j).map Prod.fst = (P j).measure) ∧
      (∀ j, (π j).map Prod.snd = Q.measure) ∧
      (∀ j, Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 3) (π j)) ∧
      Tendsto (fun j => ∫ z, |z.1 - z.2| ^ 3 ∂π j) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ z, (z.1 - z.2) ^ 2 ∂π j) atTop (𝓝 0) := by
  choose π hπ hf hs hi hc using fun j : ℕ =>
    manuscript_near_cubic_coupling (P j) Q (1 / ((j : ℝ) + 1)) (by positivity)
  have hsmall : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hr := squeeze_zero
    (fun j => Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _)
    (fun j => (hc j).le) (by simpa using hW.add hsmall)
  have hcube : Tendsto (fun j => ∫ z, |z.1 - z.2| ^ 3 ∂π j) atTop (𝓝 0) := by
    have h := hr.pow 3
    convert h using 1
    · funext j
      have hnon : 0 ≤ ∫ z, |z.1 - z.2| ^ 3 ∂π j := integral_nonneg (fun _ => by positivity)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnon]
      norm_num
    · norm_num
  refine ⟨π, hπ, hf, hs, hi, hcube, ?_⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  let r := min 1 (ε / 4)
  have hrpos : 0 < r := lt_min (by norm_num) (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrε : r ≤ ε / 4 := min_le_right _ _
  have hrsq : r ^ 2 ≤ ε / 4 := by nlinarith only [hrpos.le, hr1, hrε]
  have hdiv : Tendsto (fun j => (∫ z, |z.1 - z.2| ^ 3 ∂π j) / r) atTop (𝓝 0) := by
    simpa only [zero_div] using hcube.div_const r
  filter_upwards [hdiv.eventually (gt_mem_nhds (by positivity : 0 < ε / 2))] with j hj
  letI := hπ j
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  have hb := manuscript_quadratic_cost_bound (π j) (hi j) r hrpos
  linarith

end BerryEsseen
