import BerryEsseen.ClassicalBounds
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace BerryEsseen

def StandardizedLaw.toProbabilityMeasure (P : StandardizedLaw) : ProbabilityMeasure ℝ :=
  ⟨P.measure, P.probability⟩

theorem standardized_tail_bound (P : StandardizedLaw) (r : ℝ) (hr : 0 < r) :
    P.measure.real (Icc (-r) r)ᶜ ≤ 1 / r ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x : ℝ => sq_nonneg x)) P.second_integrable (r ^ 2)
  rw [P.second_one] at h
  have hsub : (Icc (-r) r)ᶜ ⊆ {x : ℝ | r ^ 2 ≤ x ^ 2} := by
    intro x hx
    have ha : r ≤ |x| := by
      by_contra hh
      exact hx (abs_le.1 (le_of_lt (lt_of_not_ge hh)))
    have hh := pow_le_pow_left₀ hr.le ha 2
    simpa only [sq_abs] using hh
  have hm := measureReal_mono (μ := P.measure) hsub
  apply (le_div_iff₀ (sq_pos_of_pos hr)).2
  nlinarith

def momentCompactSet : Set (ProbabilityMeasure ℝ) :=
  {μ | ∀ n : ℕ, μ (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))ᶜ ≤ 1 / ((n : ℝ≥0) + 1)}

theorem momentCompactSet_isCompact : IsCompact momentCompactSet := by
  apply isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    (K := fun n : ℕ => Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))
  · have hh : Tendsto (fun n : ℕ => (1 : ℝ≥0) / (n : ℝ≥0)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hh.comp (tendsto_add_atTop_nat 1)
  · intro n
    exact isCompact_Icc
  · exact Or.inl inferInstance

theorem standardized_mem_momentCompactSet (P : StandardizedLaw) :
    P.toProbabilityMeasure ∈ momentCompactSet := by
  intro n
  have hr : 0 < (n : ℝ) + 1 := by positivity
  have ht := standardized_tail_bound P ((n : ℝ) + 1) hr
  have hle : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) hr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := ht.trans hle
  change ((P.toProbabilityMeasure : ProbabilityMeasure ℝ) : Measure ℝ).real _ ≤ _ at hh
  rw [ProbabilityMeasure.measureReal_eq_coe_coeFn] at hh
  exact_mod_cast hh

theorem standardized_weak_subsequence (P : ℕ → StandardizedLaw) :
    ∃ (μ : ProbabilityMeasure ℝ) (u : ℕ → ℕ), StrictMono u ∧
      Tendsto (fun j => (P (u j)).toProbabilityMeasure) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ, u, hu, hlim⟩ := momentCompactSet_isCompact.isSeqCompact
    (fun j => standardized_mem_momentCompactSet (P j))
  exact ⟨μ, u, hu, hlim⟩

def sumProbabilityMeasure (μ : ProbabilityMeasure ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨iidSumLaw (μ : Measure ℝ) n, inferInstance⟩

theorem sumProbabilityMeasure_continuous (n : ℕ) : Continuous (fun μ => sumProbabilityMeasure μ n) := by
  induction n with
  | zero =>
    have he : (fun μ : ProbabilityMeasure ℝ => sumProbabilityMeasure μ 0) =
        (fun _ : ProbabilityMeasure ℝ => sumProbabilityMeasure rademacher.toProbabilityMeasure 0) := by
      funext μ
      rfl
    rw [he]
    exact continuous_const
  | succ n ih =>
    have h := (ProbabilityMeasure.continuous_map (f := fun x : ℝ × ℝ => x.1 + x.2) (by fun_prop)).comp
      (ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk ih))
    exact h

theorem weak_limit_integrable_moment_bound (μ : ProbabilityMeasure ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ) (hμ : Tendsto μs atTop (𝓝 μ))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (B : ℝ)
    (hi : ∀ j, Integrable f (μs j : Measure ℝ))
    (hB : ∀ j, (∫ x, f x ∂(μs j : Measure ℝ)) ≤ B) :
    Integrable f (μ : Measure ℝ) ∧ (∫ x, f x ∂(μ : Measure ℝ)) ≤ B := by
  have hL := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (μ : Measure ℝ)) (μs := fun j => (μs j : Measure ℝ)) hf hf0
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG)
  have hBn : 0 ≤ B := (integral_nonneg hf0).trans (hB 0)
  have hBi (j : ℕ) : (∫⁻ x, ENNReal.ofReal (f x) ∂(μs j : Measure ℝ)) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi j) (Eventually.of_forall hf0)]
    exact ENNReal.ofReal_le_ofReal (hB j)
  have hlim := liminf_le_of_frequently_le' (f := atTop) (Eventually.of_forall hBi).frequently
  have htotal := hL.trans hlim
  have hint : Integrable f (μ : Measure ℝ) :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).2
      (htotal.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0)] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff hBn).1 htotal

theorem weak_limit_moment_le_of_tendsto (μ : ProbabilityMeasure ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ) (hμ : Tendsto μs atTop (𝓝 μ))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : ∀ j, Integrable f (μs j : Measure ℝ)) (b : ℝ)
    (hb : Tendsto (fun j => ∫ x, f x ∂(μs j : Measure ℝ)) atTop (𝓝 b)) :
    Integrable f (μ : Measure ℝ) ∧ (∫ x, f x ∂(μ : Measure ℝ)) ≤ b := by
  have hL := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (μ : Measure ℝ)) (μs := fun j => (μs j : Measure ℝ)) hf hf0
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hG)
  have hBn : 0 ≤ b := ge_of_tendsto hb (Eventually.of_forall (fun j => integral_nonneg hf0))
  have hlim : Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (f x) ∂(μs j : Measure ℝ)) atTop
      (𝓝 (ENNReal.ofReal b)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
    simpa only [Function.comp_def, ofReal_integral_eq_lintegral_ofReal (hi _) (Eventually.of_forall hf0)] using h
  rw [hlim.liminf_eq] at hL
  have hint : Integrable f (μ : Measure ℝ) :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).2
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff hBn).1 hL

end BerryEsseen
