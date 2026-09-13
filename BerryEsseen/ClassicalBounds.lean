import BerryEsseen.Statement
import BerryEsseen.Examples
import BerryEsseen.ErrorBounds
import BerryEsseen.ManuscriptSelection
import Mathlib.Analysis.Real.Pi.Bounds

/-! Published inputs and the actual extremal constants.

The two fields below are precisely the bounds quoted in the manuscript:
Shevtsova (2013), pp. 124–125, and Shevtsova (2012), Corollary 4.18,
p. 303. They are explicit parameters, accepted under the user's instruction
to assume published results. No new result from the manuscript is a field.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

structure ClassicalBerryEsseenBounds : Prop where
  structural : ∀ (P : StandardizedLaw) (n : ℕ), 1 ≤ n → ∀ x : ℝ,
    discrepancy P n x ≤ min ((0.4690 : ℝ) * thirdMoment P)
      ((0.3031 : ℝ) * (thirdMoment P + 0.646)) / Real.sqrt (n : ℝ)
  remainder : ∀ (P : StandardizedLaw) (n : ℕ), 1 ≤ n → ∀ x : ℝ,
    discrepancy P n x ≤ cE * thirdMoment P / Real.sqrt (n : ℝ) +
      (2.5786 : ℝ) * thirdMoment P ^ 2 / (n : ℝ)

def normalizedDiscrepancy (P : StandardizedLaw) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * discrepancy P n x / thirdMoment P

def extremalValues (n : ℕ) : Set ℝ :=
  {r | ∃ (P : StandardizedLaw) (x : ℝ), normalizedDiscrepancy P n x = r}

def extremalConstant (n : ℕ) : ℝ := sSup (extremalValues n)

def momentCutoff : ℝ := (0.3031 : ℝ) * 0.646 / (cE - 0.3031)

theorem cE_numeric_bounds : (0.4097 : ℝ) < cE ∧ cE < 0.4098 := by
  have hs0 := Real.sqrt_nonneg (2 * Real.pi)
  have hs2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  have h10 := Real.sqrt_nonneg (10 : ℝ)
  have hroot : (2.5066 : ℝ) < Real.sqrt (2 * Real.pi) ∧
      Real.sqrt (2 * Real.pi) < 2.5067 := by
    constructor <;> nlinarith [Real.pi_gt_d6, Real.pi_lt_d4]
  have hten : (3.1622 : ℝ) < Real.sqrt 10 ∧ Real.sqrt 10 < 3.1623 := by
    constructor <;> nlinarith [sqrt10_sq]
  have hden : 0 < 6 * Real.sqrt (2 * Real.pi) := by positivity
  unfold cE
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith [hroot.2, hten.1]
  · apply (div_lt_iff₀ hden).2
    nlinarith [hroot.1, hten.2]

theorem momentCutoff_bounds : 0 < momentCutoff ∧ momentCutoff < 1.84 := by
  have hc : 0 < cE - 0.3031 := by linarith [cE_numeric_bounds.1]
  constructor
  · exact div_pos (by norm_num) hc
  · apply (div_lt_iff₀ hc).2
    nlinarith [cE_numeric_bounds.1]

theorem normalizedDiscrepancy_nonneg (P : StandardizedLaw) (n : ℕ) (x : ℝ) :
    0 ≤ normalizedDiscrepancy P n x := by
  unfold normalizedDiscrepancy discrepancy
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (thirdMoment_pos P).le

theorem normalizedDiscrepancy_structural (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    normalizedDiscrepancy P n x ≤ 0.4690 ∧
      normalizedDiscrepancy P n x ≤ 0.3031 * (thirdMoment P + 0.646) / thirdMoment P := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  have h := (le_div_iff₀ hs).1 (H.structural P n hn x)
  have hb := thirdMoment_pos P
  unfold normalizedDiscrepancy
  constructor
  · apply (div_le_iff₀ hb).2
    have h' := h.trans (min_le_left _ _)
    nlinarith
  · apply (div_le_div_iff_of_pos_right hb).2
    have h' := h.trans (min_le_right _ _)
    nlinarith

theorem normalizedDiscrepancy_remainder (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    normalizedDiscrepancy P n x ≤ cE + 2.5786 * thirdMoment P / Real.sqrt (n : ℝ) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  have hb := thirdMoment_pos P
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    normalizedDiscrepancy P n x ≤ Real.sqrt (n : ℝ) *
        (cE * thirdMoment P / Real.sqrt (n : ℝ) + 2.5786 * thirdMoment P ^ 2 / (n : ℝ)) /
          thirdMoment P := by
      unfold normalizedDiscrepancy
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (H.remainder P n hn x) hs.le) hb.le
    _ = _ := by
      field_simp
      nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]

theorem normalized_violation_momentCutoff (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hviol : cE < normalizedDiscrepancy P n x) : thirdMoment P < momentCutoff := by
  exact moment_cutoff _ _ _ _ _ (thirdMoment_pos P)
    (by linarith [cE_numeric_bounds.1]) hviol
    (normalizedDiscrepancy_structural H P n hn x).2

theorem normalizedDiscrepancy_uniform_remainder (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    normalizedDiscrepancy P n x ≤ cE + 4.75 / Real.sqrt (n : ℝ) := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  by_cases h : normalizedDiscrepancy P n x ≤ cE
  · exact h.trans (le_add_of_nonneg_right (by positivity))
  · have hc := normalized_violation_momentCutoff H P n hn x (lt_of_not_ge h)
    have hβ : thirdMoment P < 1.84 := hc.trans momentCutoff_bounds.2
    have hnum : 2.5786 * thirdMoment P ≤ 4.75 := by linarith
    exact (normalizedDiscrepancy_remainder H P n hn x).trans
      (add_le_add_right (div_le_div_of_nonneg_right hnum hs.le) cE)

theorem extremalValues_nonempty (n : ℕ) : (extremalValues n).Nonempty :=
  ⟨normalizedDiscrepancy rademacher n 0, rademacher, 0, rfl⟩

theorem extremalValues_bddAbove (H : ClassicalBerryEsseenBounds) (n : ℕ) (hn : 1 ≤ n) :
    BddAbove (extremalValues n) := by
  refine ⟨0.4690, ?_⟩
  rintro r ⟨P, x, rfl⟩
  exact (normalizedDiscrepancy_structural H P n hn x).1

theorem normalizedDiscrepancy_le_extremalConstant (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    normalizedDiscrepancy P n x ≤ extremalConstant n :=
  le_csSup (extremalValues_bddAbove H n hn) ⟨P, x, rfl⟩

theorem extremalConstant_bounds (H : ClassicalBerryEsseenBounds) (n : ℕ) (hn : 1 ≤ n) :
    extremalConstant n ≤ 0.4690 ∧ extremalConstant n ≤ cE + 4.75 / Real.sqrt (n : ℝ) := by
  constructor
  · apply csSup_le (extremalValues_nonempty n)
    rintro r ⟨P, x, rfl⟩
    exact (normalizedDiscrepancy_structural H P n hn x).1
  · apply csSup_le (extremalValues_nonempty n)
    rintro r ⟨P, x, rfl⟩
    exact normalizedDiscrepancy_uniform_remainder H P n hn x

theorem BoundAt_iff_normalized (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) :
    BoundAt P n ↔ ∀ x, normalizedDiscrepancy P n x ≤ cE := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  unfold BoundAt normalizedDiscrepancy
  simp only [le_div_iff₀ hs, div_le_iff₀ (thirdMoment_pos P)]
  simp only [mul_comm (Real.sqrt (n : ℝ))]

theorem mainClaim_iff_extremalConstant (H : ClassicalBerryEsseenBounds) :
    MainClaim ↔ ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, extremalConstant n ≤ cE := by
  constructor
  · rintro ⟨N, hN, h⟩
    refine ⟨N, hN, fun n hn => ?_⟩
    apply csSup_le (extremalValues_nonempty n)
    rintro r ⟨P, x, rfl⟩
    exact (BoundAt_iff_normalized P n (hN.trans hn)).1 (h n hn P) x
  · rintro ⟨N, hN, h⟩
    refine ⟨N, hN, fun n hn P => (BoundAt_iff_normalized P n (hN.trans hn)).2 ?_⟩
    intro x
    exact (normalizedDiscrepancy_le_extremalConstant H P n (hN.trans hn) x).trans (h n hn)

/-- Only the positive excess is needed for selection. This avoids requiring
a lower asymptotic estimate for the extremal constants. -/
def extremalExcess (n : ℕ) : ℝ := max (extremalConstant n - cE) 0

theorem extremalExcess_tendsto_zero (H : ClassicalBerryEsseenBounds) :
    Tendsto extremalExcess atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (4.75 : ℝ) / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _
  apply squeeze_zero' (Eventually.of_forall (fun n => le_max_right _ _)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact max_le (by linarith [(extremalConstant_bounds H n hn).2]) (by positivity)

theorem positive_excess_drop (a b c : ℝ) (hb : c < b) :
    max (max (a - c) 0 - max (b - c) 0) 0 = max (a - b) 0 := by
  rw [max_eq_left (by linarith : 0 ≤ b - c)]
  by_cases ha : c ≤ a
  · rw [max_eq_left (by linarith : 0 ≤ a - c)]
    congr 1
    ring
  · rw [max_eq_right (by linarith : a - c ≤ 0)]
    rw [max_eq_right (by linarith : 0 - (b - c) ≤ 0)]
    exact (max_eq_right (by linarith : a - b ≤ 0)).symm

/-- The selected indices in the main proof, for the supremum of the actual
probability discrepancies, using only the two stated published estimates. -/
theorem extremal_harmonic_selection (H : ClassicalBerryEsseenBounds)
    (hviol : ∀ K : ℕ, ∃ n ≥ K, cE < extremalConstant n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ cE < extremalConstant (u j)) ∧
      Tendsto (fun j => scaledDrop extremalConstant (u j)) atTop (𝓝 0) := by
  have hp : ∀ K : ℕ, ∃ n ≥ K, 0 < extremalExcess n := by
    intro K
    obtain ⟨n, hn, hv⟩ := hviol K
    exact ⟨n, hn, lt_of_lt_of_le (sub_pos.2 hv) (le_max_left _ _)⟩
  obtain ⟨u, hu, hp, hd⟩ := manuscript_harmonic_selection extremalExcess
    (extremalExcess_tendsto_zero H) hp
  have hv (j : ℕ) : cE < extremalConstant (u j) := by
    have h := (hp j).2
    dsimp [extremalExcess] at h
    have h' := (lt_max_iff).1 h
    rcases h' with h' | h' <;> linarith
  refine ⟨u, hu, fun j => ⟨(hp j).1, hv j⟩, ?_⟩
  have he : (fun j => scaledDrop extremalExcess (u j)) =
      (fun j => scaledDrop extremalConstant (u j)) := by
    funext j
    unfold scaledDrop extremalExcess
    rw [positive_excess_drop _ _ _ (hv j)]
  rwa [he] at hd

theorem extremal_harmonic_selection_of_not_main (H : ClassicalBerryEsseenBounds)
    (hmain : ¬ MainClaim) :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      (∀ j, 1 ≤ u j ∧ cE < extremalConstant (u j)) ∧
      Tendsto (fun j => scaledDrop extremalConstant (u j)) atTop (𝓝 0) := by
  apply extremal_harmonic_selection H
  intro K
  by_contra h
  push_neg at h
  apply hmain
  apply (mainClaim_iff_extremalConstant H).2
  exact ⟨max K 1, le_max_right _ _, fun n hn => h n ((le_max_left _ _).trans hn)⟩

end BerryEsseen
