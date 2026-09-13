import BerryEsseen.GeneralThirdMomentTails

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def characteristicCubicModulus (P : StandardizedLaw) (u : ℝ) : ℝ :=
  ∫ x, |x| ^ 3 * min (|u| * |x|) 1 ∂P.measure

theorem characteristicCubicModulus_measurable (P : StandardizedLaw) :
    Measurable (characteristicCubicModulus P) := by
  have h : StronglyMeasurable (fun z : ℝ × ℝ => |z.2| ^ 3 * min (|z.1| * |z.2|) 1) :=
    (show Continuous (fun z : ℝ × ℝ => |z.2| ^ 3 * min (|z.1| * |z.2|) 1) by fun_prop).stronglyMeasurable
  exact h.integral_prod_right'.measurable

theorem characteristicCubicModulus_integrable (P : StandardizedLaw) (u : ℝ) :
    Integrable (fun x : ℝ => |x| ^ 3 * min (|u| * |x|) 1) P.measure := by
  apply P.third_integrable.mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (min_le_right _ _)

theorem characteristicCubicModulus_nonneg (P : StandardizedLaw) (u : ℝ) :
    0 ≤ characteristicCubicModulus P u := by
  apply integral_nonneg
  intro x
  positivity

theorem characteristicCubicModulus_le_thirdMoment (P : StandardizedLaw) (u : ℝ) :
    characteristicCubicModulus P u ≤ thirdMoment P := by
  apply integral_mono (characteristicCubicModulus_integrable P u) P.third_integrable
  intro x
  exact mul_le_of_le_one_right (by positivity) (min_le_right _ _)

theorem characteristicCubicModulus_tail_bound (P : StandardizedLaw) (R u : ℝ) (hR : 0 ≤ R) :
    characteristicCubicModulus P u ≤ |u| * R * thirdMoment P + thirdMomentTail P.measure R := by
  let S := {x : ℝ | R < |x|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_abs
  have hb := integral_mono (characteristicCubicModulus_integrable P u)
    ((P.third_integrable.const_mul (|u| * R)).add (P.third_integrable.indicator hS)) (fun x => by
      change |x| ^ 3 * min (|u| * |x|) 1 ≤
        |u| * R * |x| ^ 3 + S.indicator (fun y => |y| ^ 3) x
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        have hh := mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) 3)
          (min_le_right (|u| * |x|) 1)
        nlinarith [mul_nonneg (mul_nonneg (abs_nonneg u) hR) (pow_nonneg (abs_nonneg x) 3)]
      · rw [indicator_of_notMem hx, add_zero]
        have hxR : |x| ≤ R := le_of_not_gt hx
        have hm : min (|u| * |x|) 1 ≤ |u| * R :=
          (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hxR (abs_nonneg u))
        nlinarith [mul_le_mul_of_nonneg_left hm (pow_nonneg (abs_nonneg x) 3)])
  simp only [Pi.add_apply] at hb
  rw [integral_add (P.third_integrable.const_mul (|u| * R))
    (P.third_integrable.indicator hS), integral_const_mul, integral_indicator hS] at hb
  exact hb

theorem uniform_characteristicCubicModulus_of_uniform_tails
    (P : ℕ → StandardizedLaw) (B : ℝ) (hB : 0 < B)
    (hβ : ∀ j, thirdMoment (P j) ≤ B)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ j, thirdMomentTail (P j).measure R ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j u, |u| ≤ δ → characteristicCubicModulus (P j) u ≤ ε := by
  obtain ⟨R, hR, hRt⟩ := htail (ε / 2) (by positivity)
  let δ := ε / (4 * R * B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro j u hu
  have hu' : |u| * (4 * R * B) ≤ ε := by
    exact (le_div_iff₀ (by positivity : 0 < 4 * R * B)).1 hu
  have hb := mul_le_mul_of_nonneg_left (hβ j) (mul_nonneg (abs_nonneg u) hR.le)
  have hm := characteristicCubicModulus_tail_bound (P j) R u hR.le
  have ht := hRt j
  nlinarith

theorem weak_thirdMoment_uniform_characteristicCubicModulus
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j u, |u| ≤ δ → characteristicCubicModulus (P j) u ≤ ε := by
  obtain ⟨B, hβ⟩ := hm.bddAbove_range
  have hβ' : ∀ j, thirdMoment (P j) ≤ B := fun j => hβ (mem_range_self j)
  have hB : 0 < B := (thirdMoment_pos (P 0)).trans_le (hβ' 0)
  exact uniform_characteristicCubicModulus_of_uniform_tails P B hB hβ'
    (weak_thirdMoment_uniformly_small_tails P Q hw hm) ε hε

theorem weak_thirdMoment_uniform_charFun_cubic_remainder
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j u, |u| ≤ δ →
      ‖charFun (P j).measure u - 1 + (u : ℂ) ^ 2 / 2 +
        (u : ℂ) ^ 3 * (signedThirdMoment (P j) : ℂ) * Complex.I / 6‖ ≤ ε * |u| ^ 3 := by
  obtain ⟨δ, hδ, hmod⟩ := weak_thirdMoment_uniform_characteristicCubicModulus P Q hw hm ε hε
  refine ⟨δ, hδ, ?_⟩
  intro j u hu
  exact (charFun_cubic_modulus_bound (P j) u).trans (by
    simpa only [mul_comm ε] using mul_le_mul_of_nonneg_left (hmod j u hu) (pow_nonneg (abs_nonneg u) 3))

theorem weak_thirdMoment_characteristicCubicModulus_diagonal_tendsto
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hm : Tendsto (fun j => thirdMoment (P j)) atTop (𝓝 (thirdMoment Q)))
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun j => characteristicCubicModulus (P j) (u j)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := weak_thirdMoment_uniform_characteristicCubicModulus P Q hw hm
    (ε / 2) (by positivity)
  filter_upwards [(Metric.tendsto_nhds.1 hu) δ hδ] with j hj
  rw [Real.dist_eq, sub_zero] at hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (characteristicCubicModulus_nonneg _ _)]
  have hh := hmod j (u j) hj.le
  linarith

theorem wassersteinThree_characteristicCubicModulus_diagonal_tendsto
    (W : PublishedWassersteinThreeTopology) (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun j => characteristicCubicModulus (P j) (u j)) atTop (𝓝 0) := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  exact weak_thirdMoment_characteristicCubicModulus_diagonal_tendsto P Q hw hm u hu

theorem wassersteinThree_uniform_charFun_cubic_remainder
    (W : PublishedWassersteinThreeTopology) (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j u, |u| ≤ δ →
      ‖charFun (P j).measure u - 1 + (u : ℂ) ^ 2 / 2 +
        (u : ℂ) ^ 3 * (signedThirdMoment (P j) : ℂ) * Complex.I / 6‖ ≤ ε * |u| ^ 3 := by
  obtain ⟨hw, hm⟩ := (standardized_wassersteinThree_tendsto_iff W P Q).1 hW
  exact weak_thirdMoment_uniform_charFun_cubic_remainder P Q hw hm ε hε

end BerryEsseen
