import BerryEsseen.EffectiveClusters
import BerryEsseen.EsseenLaw
import BerryEsseen.NormalizedIID

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem strictCDF_eq_leftLim (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    strictCDF μ t = leftLim (cdf μ) t := by
  have hlim := (monotone_cdf μ).tendsto_leftLim t
  have hnonneg : 0 ≤ leftLim (cdf μ) t :=
    ge_of_tendsto hlim (Eventually.of_forall (cdf_nonneg μ))
  unfold strictCDF Measure.real
  have he := StieltjesFunction.measure_Iio (cdf μ) (tendsto_cdf_atBot μ) t
  rw [measure_cdf μ, sub_zero] at he
  rw [he, ENNReal.toReal_ofReal hnonneg]

theorem strictCDF_uniform_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (G : ℝ → ℝ) (hG : Continuous G) (c R : ℝ)
    (h : ∀ x, c * |cdf μ x - G x| ≤ R) (t : ℝ) :
    c * |strictCDF μ t - G t| ≤ R := by
  rw [strictCDF_eq_leftLim]
  have hlim := (monotone_cdf μ).tendsto_leftLim t
  have hGlim : Tendsto G (𝓝[<] t) (𝓝 (G t)) :=
    hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto (((hlim.sub hGlim).abs).const_mul c) (Eventually.of_forall h)

theorem reflected_cdf_eq_strictCDF (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (μ.map (fun y => -y)) x = 1 - strictCDF μ (-x) := by
  have h := reflected_cdf μ (-x)
  simp only [neg_neg] at h
  rw [h, strictCDF, ← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio]

theorem normalizedIIDSumLaw_reflected (P : StandardizedLaw) (n : ℕ) :
    normalizedIIDSumLaw (reflectedLaw P) n =
      (normalizedIIDSumLaw P n).map (fun x => -x) := by
  unfold normalizedIIDSumLaw
  rw [iidSumLaw_reflected, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_def, neg_div]

theorem reflected_normalized_uniform_bound (P : StandardizedLaw) (n : ℕ)
    (hn : 1 ≤ n) (R : ℝ) (h : ∀ x, normalizedDiscrepancy P n x ≤ R) :
    ∀ x, normalizedDiscrepancy (reflectedLaw P) n x ≤ R := by
  letI := normalizedIIDSumLaw_probability P n
  have h' : ∀ x, Real.sqrt (n : ℝ) / thirdMoment P *
      |cdf (normalizedIIDSumLaw P n) x - normalCDF x| ≤ R := by
    intro x
    simpa only [normalizedDiscrepancy_eq_iid_error P n hn x] using h x
  intro x
  have hb := strictCDF_uniform_bound (normalizedIIDSumLaw P n) normalCDF
    normalCDF_continuous (Real.sqrt (n : ℝ) / thirdMoment P) R h' (-x)
  rw [normalizedDiscrepancy_eq_iid_error _ n hn, reflectedLaw_thirdMoment,
    normalizedIIDSumLaw_reflected, reflected_cdf_eq_strictCDF]
  have he : 1 - strictCDF (normalizedIIDSumLaw P n) (-x) - normalCDF x =
      -(strictCDF (normalizedIIDSumLaw P n) (-x) - normalCDF (-x)) := by
    rw [normalCDF_reflection]
    ring
  rw [he, abs_neg]
  exact hb

theorem normalizedDiscrepancy_range_bddAbove (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) :
    BddAbove (range (normalizedDiscrepancy P n)) := by
  letI := normalizedIIDSumLaw_probability P n
  refine ⟨Real.sqrt (n : ℝ) / thirdMoment P, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [normalizedDiscrepancy_eq_iid_error P n hn]
  have hN0 : 0 ≤ normalCDF x := by simpa only [cdf_eq_real] using cdf_nonneg (gaussianReal 0 1) x
  have hN1 : normalCDF x ≤ 1 := by simpa only [cdf_eq_real] using cdf_le_one (gaussianReal 0 1) x
  have hd : |cdf (normalizedIIDSumLaw P n) x - normalCDF x| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [cdf_nonneg (normalizedIIDSumLaw P n) x,
      cdf_le_one (normalizedIIDSumLaw P n) x]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd
    (div_nonneg (Real.sqrt_nonneg _) (thirdMoment_pos P).le)

theorem reflectedLaw_twice (P : StandardizedLaw) : reflectedLaw (reflectedLaw P) = P := by
  apply standardizedLaw_eq_of_measure_eq
  exact reflected_measure_twice P.measure

theorem normalizedDiscrepancy_sup_reflected (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) :
    sSup (range (normalizedDiscrepancy (reflectedLaw P) n)) =
      sSup (range (normalizedDiscrepancy P n)) := by
  have hle (Q : StandardizedLaw) :
      sSup (range (normalizedDiscrepancy (reflectedLaw Q) n)) ≤
        sSup (range (normalizedDiscrepancy Q n)) := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x, rfl⟩
    apply reflected_normalized_uniform_bound Q n hn _ (fun y => ?_) x
    exact le_csSup (normalizedDiscrepancy_range_bddAbove Q n hn) (mem_range_self y)
  apply le_antisymm (hle P)
  simpa only [reflectedLaw_twice] using hle (reflectedLaw P)

end BerryEsseen
