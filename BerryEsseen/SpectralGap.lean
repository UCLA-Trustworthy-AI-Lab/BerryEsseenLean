import BerryEsseen.CompactFourierConvergence
import BerryEsseen.JitterLowFrequency
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exponential decay on compact sets disjoint from the limiting resonances. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem norm_pow_exp_of_square_gap (z : ℂ) (δ : ℝ)
    (hz : ‖z‖ ^ 2 ≤ 1 - δ) (n : ℕ) :
    ‖z‖ ^ n ≤ Real.exp (-(n : ℝ) * δ / 2) := by
  have he := Real.add_one_le_exp (-δ)
  have heq : Real.exp (-δ / 2) ^ 2 = Real.exp (-δ) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hn : ‖z‖ ≤ Real.exp (-δ / 2) := by
    nlinarith [norm_nonneg z, Real.exp_pos (-δ / 2)]
  have hp := pow_le_pow_left₀ (norm_nonneg z) hn n
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

theorem compact_characteristic_spectral_gap (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (K : Set ℝ) (hK : IsCompact K) (hnr : ∀ u ∈ K, u ∉ resonanceSubgroup Q.measure) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, ∀ u ∈ K, ∀ n : ℕ,
      ‖charFun (P j).measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * δ / 2) := by
  by_cases hne : K.Nonempty
  · have hcont : Continuous (characteristicSquare Q) :=
      continuous_iff_continuousAt.2 (fun u => (characteristicSquare_hasDerivAt Q u).continuousAt)
    obtain ⟨a, ha, hamax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
    have hnorm : ‖charFun Q.measure a‖ < 1 := by
      by_contra h
      exact hnr a ha ((mem_resonanceSubgroup_iff Q.measure a).2
        (le_antisymm (norm_charFun_le_one a) (le_of_not_gt h)))
    have ha1 : characteristicSquare Q a < 1 := by
      unfold characteristicSquare
      nlinarith [norm_nonneg (charFun Q.measure a)]
    let δ := (1 - characteristicSquare Q a) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    refine ⟨δ, hδ, ?_⟩
    have hu := compact_characteristicSquare_convergence P Q hW3 K hK
    filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hu) δ hδ] with j hj
    intro u hu n
    apply norm_pow_exp_of_square_gap
    have hh := hj u hu
    rw [Real.dist_eq] at hh
    have hmax := hamax hu
    change characteristicSquare Q u ≤ characteristicSquare Q a at hmax
    change characteristicSquare (P j) u ≤ _
    have := (abs_lt.1 hh).1
    dsimp [δ] at this ⊢
    linarith
  · refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro j u hu
    exact (hne ⟨u, hu⟩).elim

theorem sqrt_mul_exp_decay (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * Real.exp (-(n j : ℝ) * δ / 2)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (δ / 2)
    (div_pos hδ (by norm_num))).comp (tendsto_natCast_atTop_atTop.comp hn)
  convert hh using 1
  funext j
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_eq_rpow]
  congr 2
  ring

end BerryEsseen
