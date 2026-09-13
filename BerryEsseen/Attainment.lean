import BerryEsseen.MovingThreshold
import BerryEsseen.ExtremizerSupport

/-! Attainment of the actual supremum above the Esseen constant. All weak
compactness, moment preservation, reflection, and threshold steps are proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem positive_maximizing_sequence (H : ClassicalBerryEsseenBounds) (n : ℕ)
    (hC : cE < extremalConstant (n + 1)) :
    ∃ (P : ℕ → StandardizedLaw) (t : ℕ → ℝ),
      (∀ j, cE < signedRatio (P j) n (t j)) ∧
      Tendsto (fun j => signedRatio (P j) n (t j)) atTop (𝓝 (extremalConstant (n + 1))) := by
  let C := extremalConstant (n + 1)
  let ε : ℕ → ℝ := fun j => (C - cE) / ((j : ℝ) + 2)
  have hepos (j : ℕ) : 0 < ε j := div_pos (sub_pos.2 hC) (by positivity)
  choose P t hlo hhi using fun j => extremal_positive_approximation H n (ε j) (hepos j)
  refine ⟨P, t, ?_, ?_⟩
  · intro j
    have he : ε j ≤ (C - cE) / 2 := by
      apply div_le_div_of_nonneg_left (sub_nonneg.2 hC.le) (by norm_num)
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have h := hlo j
    change C - ε j < signedRatio (P j) n (t j) at h
    linarith
  · have hε : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_const_div_atTop_nhds_zero_nat (C - cE)).comp (tendsto_add_atTop_nat 2)
    have hlim : Tendsto (fun j => C - signedRatio (P j) n (t j)) atTop (𝓝 0) :=
      squeeze_zero (fun j => sub_nonneg.2 (hhi j))
        (fun j => by have h := hlo j; change C - ε j < _ at h; linarith) hε
    simpa only [sub_zero, sub_sub_cancel] using hlim.const_sub C

theorem signedRatio_violation_discrepancy_lower (P : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hviol : cE < signedRatio P n t) :
    cE / Real.sqrt (n + 1 : ℝ) ≤ cdf (iidSumLaw P.measure (n + 1)) t -
      normalCDF (t / Real.sqrt (n + 1 : ℝ)) := by
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  have hv := (lt_div_iff₀ (thirdMoment_pos P)).1 hviol
  apply (div_le_iff₀ hs).2
  have hβ := mul_le_mul_of_nonneg_left (thirdMoment_ge_one P) cE_pos.le
  nlinarith

theorem normalCDF_continuous : Continuous normalCDF :=
  continuous_iff_continuousAt.2 (fun x => (normalCDF_hasDerivAt x).continuousAt)

/-- Equality in the manuscript's compactness chain preserves the limiting
third absolute moment, not just its lower-semicontinuity inequality. -/
theorem manuscript_attainment_moment_equality (H : ClassicalBerryEsseenBounds)
    (Q : StandardizedLaw) (n : ℕ) (t b : ℝ)
    (hC : 0 < extremalConstant (n + 1)) (hQβ : thirdMoment Q ≤ b)
    (hdis : extremalConstant (n + 1) * b ≤
      (cdf (iidSumLaw Q.measure (n + 1)) t - normalCDF (t / Real.sqrt (n + 1 : ℝ))) *
        Real.sqrt (n + 1 : ℝ)) : thirdMoment Q = b := by
  have hratio := signedRatio_le_extremalConstant H Q n t
  unfold signedRatio at hratio
  have hbnd := (div_le_iff₀ (thirdMoment_pos Q)).1 hratio
  apply le_antisymm hQβ
  by_contra h
  have hstrict := mul_lt_mul_of_pos_left (lt_of_not_ge h) hC
  nlinarith

theorem manuscript_attained_full_ratio (H : ClassicalBerryEsseenBounds)
    (Q : StandardizedLaw) (n : ℕ) (t : ℝ)
    (hC : 0 ≤ extremalConstant (n + 1))
    (heq : signedRatio Q n t = extremalConstant (n + 1)) :
    sSup (range (normalizedDiscrepancy Q (n + 1))) = extremalConstant (n + 1) := by
  have hb : BddAbove (range (normalizedDiscrepancy Q (n + 1))) := by
    refine ⟨extremalConstant (n + 1), ?_⟩
    rintro y ⟨x, rfl⟩
    exact normalizedDiscrepancy_le_extremalConstant H Q (n + 1) (by omega) x
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro y ⟨x, rfl⟩
    exact normalizedDiscrepancy_le_extremalConstant H Q (n + 1) (by omega) x
  · have hx := le_csSup hb (mem_range_self
      (t / Real.sqrt (n + 1 : ℝ)) :
      normalizedDiscrepancy Q (n + 1) (t / Real.sqrt (n + 1 : ℝ)) ∈ _)
    rwa [← abs_signedRatio_eq_normalized, heq, abs_of_nonneg hC] at hx

/-- Full manuscript statement: the same limiting pair attains the positive
branch and the full Kolmogorov ratio, with the original moment cutoff. -/
theorem manuscript_extremal_attainment_full (H : ClassicalBerryEsseenBounds) (n : ℕ)
    (hC : cE < extremalConstant (n + 1)) :
    ∃ (Q : StandardizedLaw) (t : ℝ), signedRatio Q n t = extremalConstant (n + 1) ∧
      sSup (range (normalizedDiscrepancy Q (n + 1))) = extremalConstant (n + 1) ∧
      1 ≤ thirdMoment Q ∧ thirdMoment Q < momentCutoff := by
  obtain ⟨P, t, hviol, hR⟩ := positive_maximizing_sequence H n hC
  have hB (j : ℕ) : thirdMoment (P j) ≤ momentCutoff :=
    (extremizer_thirdMoment_cutoff H (P j) n (t j) (hviol j)).le
  obtain ⟨Q, u, b, hu, hb1, hbB, hQβ, hw, hβ⟩ := standardized_moment_subsequence P momentCutoff hB
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
  obtain ⟨L, hL, ht⟩ := positive_discrepancy_threshold_bounded (n + 1) (by omega)
    (cE / Real.sqrt (n + 1 : ℝ)) (div_pos cE_pos hs)
  have htb (j : ℕ) : t (u j) ∈ Icc (-L) L := by
    apply abs_le.1
    apply ht (P (u j)) (t (u j))
    simpa only [Nat.cast_add, Nat.cast_one] using
      signedRatio_violation_discrepancy_lower (P (u j)) n (t (u j)) (hviol (u j))
  obtain ⟨T, hT, v, hv, htlim⟩ := isCompact_Icc.isSeqCompact htb
  let P' : ℕ → StandardizedLaw := fun j => P (u (v j))
  let t' : ℕ → ℝ := fun j => t (u (v j))
  have hweak : Tendsto (fun j => (P' j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure) :=
    hw.comp hv.tendsto_atTop
  have hβ' : Tendsto (fun j => thirdMoment (P' j)) atTop (𝓝 b) := hβ.comp hv.tendsto_atTop
  have hR' : Tendsto (fun j => signedRatio (P' j) n (t' j)) atTop
      (𝓝 (extremalConstant (n + 1))) := (hR.comp hu.tendsto_atTop).comp hv.tendsto_atTop
  have hPhi : Tendsto (fun j => normalCDF (t' j / Real.sqrt (n + 1 : ℝ))) atTop
      (𝓝 (normalCDF (T / Real.sqrt (n + 1 : ℝ)))) :=
    normalCDF_continuous.continuousAt.tendsto.comp (htlim.div_const _)
  have hsum : Tendsto (fun j => sumProbabilityMeasure (P' j).toProbabilityMeasure (n + 1)) atTop
      (𝓝 (sumProbabilityMeasure Q.toProbabilityMeasure (n + 1))) :=
    (sumProbabilityMeasure_continuous (n + 1)).continuousAt.tendsto.comp hweak
  let a : ℕ → ℝ := fun j => normalCDF (t' j / Real.sqrt (n + 1 : ℝ)) +
    signedRatio (P' j) n (t' j) * thirdMoment (P' j) / Real.sqrt (n + 1 : ℝ)
  have ha : Tendsto a atTop (𝓝 (normalCDF (T / Real.sqrt (n + 1 : ℝ)) +
      extremalConstant (n + 1) * b / Real.sqrt (n + 1 : ℝ))) :=
    hPhi.add ((hR'.mul hβ').div_const _)
  have hae (j : ℕ) : a j = cdf (iidSumLaw (P' j).measure (n + 1)) (t' j) := by
    dsimp [a, signedRatio]
    field_simp [(thirdMoment_pos (P' j)).ne']
    ring
  have hCDF := moving_cdf_lower_limit
    (fun j => sumProbabilityMeasure (P' j).toProbabilityMeasure (n + 1))
    (sumProbabilityMeasure Q.toProbabilityMeasure (n + 1)) hsum t' T htlim a _ ha
    (fun j => (hae j).le)
  change normalCDF (T / Real.sqrt (n + 1 : ℝ)) +
      extremalConstant (n + 1) * b / Real.sqrt (n + 1 : ℝ) ≤
      cdf (iidSumLaw Q.measure (n + 1)) T at hCDF
  have hdis : extremalConstant (n + 1) * b ≤
      (cdf (iidSumLaw Q.measure (n + 1)) T - normalCDF (T / Real.sqrt (n + 1 : ℝ))) *
        Real.sqrt (n + 1 : ℝ) := by
    apply (div_le_iff₀ hs).1
    linarith
  have hβeq : thirdMoment Q = b :=
    manuscript_attainment_moment_equality H Q n T b (cE_pos.trans hC) hQβ hdis
  have hlow : extremalConstant (n + 1) ≤ signedRatio Q n T := by
    apply (le_div_iff₀ (thirdMoment_pos Q)).2
    rw [hβeq]
    nlinarith
  have heq : signedRatio Q n T = extremalConstant (n + 1) :=
    le_antisymm (signedRatio_le_extremalConstant H Q n T) hlow
  exact ⟨Q, T, heq, manuscript_attained_full_ratio H Q n T (cE_pos.trans hC).le heq,
    thirdMoment_ge_one Q,
    extremizer_thirdMoment_cutoff H Q n T (by rwa [heq])⟩

/-- The existing consumer interface is a projection of the full original
attainment statement, preserving the identical maximizing witness. -/
theorem extremal_attainment (H : ClassicalBerryEsseenBounds) (n : ℕ)
    (hC : cE < extremalConstant (n + 1)) :
    ∃ (Q : StandardizedLaw) (t : ℝ), signedRatio Q n t = extremalConstant (n + 1) ∧
      1 ≤ thirdMoment Q ∧ thirdMoment Q < momentCutoff := by
  obtain ⟨Q, t, hratio, _, hmoment⟩ := manuscript_extremal_attainment_full H n hC
  exact ⟨Q, t, hratio, hmoment⟩

end BerryEsseen
