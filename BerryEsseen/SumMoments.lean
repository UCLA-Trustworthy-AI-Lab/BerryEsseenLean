import BerryEsseen.MomentPreservation
import BerryEsseen.PositiveBranch

/-! Exact first and second moments of the iid sum, and uniform control of
thresholds carrying a fixed positive discrepancy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem iidSumLaw_moments (P : StandardizedLaw) (n : ℕ) :
    Integrable (fun x : ℝ => x) (iidSumLaw P.measure n) ∧
    Integrable (fun x : ℝ => x ^ 2) (iidSumLaw P.measure n) ∧
    (∫ x, x ∂iidSumLaw P.measure n) = 0 ∧
    (∫ x, x ^ 2 ∂iidSumLaw P.measure n) = n := by
  induction n with
  | zero =>
    dsimp [iidSumLaw]
    exact ⟨integrable_dirac (by simp), integrable_dirac (by simp), by simp, by simp⟩
  | succ n ih =>
    obtain ⟨hi₁, hi₂, hm, hv⟩ := ih
    have hx₁ := P.first_integrable.comp_fst (iidSumLaw P.measure n)
    have hy₁ := hi₁.comp_snd P.measure
    have hx₂ := P.second_integrable.comp_fst (iidSumLaw P.measure n)
    have hy₂ := hi₂.comp_snd P.measure
    have hxy := (P.first_integrable.mul_prod hi₁).const_mul 2
    have hxxy : Integrable (fun x : ℝ × ℝ => x.1 ^ 2 + 2 * (x.1 * x.2))
        (P.measure.prod (iidSumLaw P.measure n)) := hx₂.add hxy
    have hi : Integrable (fun x : ℝ × ℝ => (x.1 + x.2) ^ 2)
        (P.measure.prod (iidSumLaw P.measure n)) := by
      convert (hx₂.add hxy).add hy₂ using 1
      funext x
      dsimp
      ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
      exact hx₁.add hy₁
    · apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
      exact hi
    · rw [iidSumLaw, integral_map (by fun_prop) (by fun_prop), integral_add hx₁ hy₁,
        integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x), P.mean_zero, hm]
      simp
    · rw [iidSumLaw, integral_map (by fun_prop) (by fun_prop)]
      have he : (fun x : ℝ × ℝ => (x.1 + x.2) ^ 2) =
          (fun x => x.1 ^ 2 + 2 * (x.1 * x.2) + x.2 ^ 2) := by funext x; ring
      rw [he, integral_add hxxy hy₂, integral_add hx₂ hxy,
        integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2),
        integral_const_mul, integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x),
        P.second_one, hv, P.mean_zero, hm]
      simp
      ring

theorem iidSumLaw_cdf_left_bound (P : StandardizedLaw) (n : ℕ) (t : ℝ) (ht : t < 0) :
    cdf (iidSumLaw P.measure n) t ≤ (n : ℝ) / t ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x : ℝ => sq_nonneg x)) (iidSumLaw_moments P n).2.1 (t ^ 2)
  rw [(iidSumLaw_moments P n).2.2.2] at h
  have hm : (iidSumLaw P.measure n).real (Iic t) ≤
      (iidSumLaw P.measure n).real {x : ℝ | t ^ 2 ≤ x ^ 2} := by
    refine measureReal_mono (μ := iidSumLaw P.measure n) ?_ (measure_ne_top _ _)
    intro x hx
    change x ≤ t at hx
    change t ^ 2 ≤ x ^ 2
    nlinarith
  rw [cdf_eq_real]
  apply (le_div_iff₀ (sq_pos_of_ne_zero ht.ne)).2
  nlinarith

theorem normalCDF_tendsto_atTop : Tendsto normalCDF atTop (𝓝 1) := by
  convert tendsto_cdf_atTop (gaussianReal 0 1) using 1
  funext x
  exact (cdf_eq_real (gaussianReal 0 1) x).symm

theorem positive_discrepancy_threshold_bounded (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (P : StandardizedLaw) (t : ℝ),
      δ ≤ cdf (iidSumLaw P.measure n) t - normalCDF (t / Real.sqrt (n : ℝ)) → |t| ≤ L := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  have hnormal : Tendsto (fun t : ℝ => 1 - normalCDF (t / Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
    have hh := normalCDF_tendsto_atTop.comp (tendsto_id.atTop_div_const hs)
    simpa using hh.const_sub 1
  obtain ⟨A, hA⟩ := eventually_atTop.1
    (hnormal.eventually (eventually_lt_nhds hδ))
  let L := max (max A (Real.sqrt ((n : ℝ) / δ) + 1)) 1
  have hL : 0 < L := by dsimp [L]; have := le_max_right (max A (Real.sqrt ((n : ℝ) / δ) + 1)) 1; linarith
  refine ⟨L, hL, ?_⟩
  intro P t hd
  by_contra h
  have hlt : L < |t| := lt_of_not_ge h
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at hlt
    have hh := hA t ((le_trans (le_max_left A _) (le_max_left _ _)).trans hlt.le)
    linarith [cdf_le_one (iidSumLaw P.measure n) t]
  · have ht0 : t < 0 := by rw [abs_of_nonpos ht] at hlt; linarith
    have hCDF := iidSumLaw_cdf_left_bound P n t ht0
    have hPhi : 0 ≤ normalCDF (t / Real.sqrt (n : ℝ)) := by unfold normalCDF; positivity
    have hnum : δ * t ^ 2 ≤ (n : ℝ) := by
      have hdiv : δ ≤ (n : ℝ) / t ^ 2 := by linarith
      exact (le_div_iff₀ (sq_pos_of_ne_zero ht0.ne)).1 hdiv
    have hr : Real.sqrt ((n : ℝ) / δ) < |t| := by
      have hLL : Real.sqrt ((n : ℝ) / δ) + 1 ≤ L :=
        (le_max_right A _).trans (le_max_left _ _)
      linarith
    have hroot := Real.sq_sqrt (show 0 ≤ (n : ℝ) / δ by positivity)
    have hsq : (n : ℝ) / δ < t ^ 2 := by
      nlinarith [Real.sqrt_nonneg ((n : ℝ) / δ), sq_abs t]
    have hneg := (div_lt_iff₀ hδ).1 hsq
    nlinarith

end BerryEsseen
