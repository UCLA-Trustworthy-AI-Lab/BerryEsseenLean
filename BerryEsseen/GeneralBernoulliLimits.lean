import BerryEsseen.GeneralBinomialMass
import BerryEsseen.PublishedWassersteinThree

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem standardizedBernoulli_tendsto (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => (standardizedBernoulliLaw (p j) (hp j)).toProbabilityMeasure)
      atTop (𝓝 (standardizedBernoulliLaw p₀ hp₀).toProbabilityMeasure) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun j => ∫ x, f x ∂(standardizedBernoulliLaw (p j) (hp j)).measure)
    atTop (𝓝 (∫ x, f x ∂(standardizedBernoulliLaw p₀ hp₀).measure))
  simp_rw [integral_standardizedBernoulli]
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  have hσ := (hlim.mul hq).sqrt
  have hs : Real.sqrt (p₀ * (1 - p₀)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))).ne'
  have hfl := f.continuous.continuousAt.tendsto.comp (hlim.neg.div hσ hs)
  have hfr := f.continuous.continuousAt.tendsto.comp (hq.div hσ hs)
  exact (hq.mul hfl).add (hlim.mul hfr)

theorem standardizedBernoulli_third_tendsto (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => thirdMoment (standardizedBernoulliLaw (p j) (hp j))) atTop
      (𝓝 (thirdMoment (standardizedBernoulliLaw p₀ hp₀))) := by
  simp_rw [standardizedBernoulli_third]
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  exact ((hlim.pow 2).add (hq.pow 2)).div ((hlim.mul hq).sqrt)
    (Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))).ne'

theorem standardizedBernoulli_signed_third_tendsto (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => signedThirdMoment (standardizedBernoulliLaw (p j) (hp j))) atTop
      (𝓝 (signedThirdMoment (standardizedBernoulliLaw p₀ hp₀))) := by
  simp_rw [standardizedBernoulli_signed_third]
  have hq := (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  exact ((tendsto_const_nhds (x := (1 : ℝ))).sub (hlim.const_mul 2)).div ((hlim.mul hq).sqrt)
    (Real.sqrt_pos.mpr (mul_pos hp₀.1 (sub_pos.mpr hp₀.2))).ne'

theorem standardizedBernoulli_wassersteinThree_tendsto (W : PublishedWassersteinThreeTopology)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1) (hlim : Tendsto p atTop (𝓝 p₀)) :
    Tendsto (fun j => wassersteinThree (standardizedBernoulliLaw (p j) (hp j)).measure
      (standardizedBernoulliLaw p₀ hp₀).measure) atTop (𝓝 0) := by
  apply (standardized_wassersteinThree_tendsto_iff W _ _).mpr
  exact ⟨standardizedBernoulli_tendsto p hp p₀ hp₀ hlim,
    standardizedBernoulli_third_tendsto p hp p₀ hp₀ hlim⟩

theorem bernoulli_general_parameter_bounds (p δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) :
    p ∈ Ioo 0 1 ∧ δ ≤ Real.sqrt (p * (1 - p)) ∧
      Real.sqrt (p * (1 - p)) ≤ 1 / 2 ∧
      p ^ 2 + (1 - p) ^ 2 ∈ Icc (1 / 2) 1 := by
  have hp0 : 0 < p := hδ.trans_le hp
  have hq0 : 0 < 1 - p := hδ.trans_le hq
  have hv0 := mul_pos hp0 hq0
  have hv := mul_le_mul hp hq hδ.le hp0.le
  have hs := Real.sq_sqrt hv0.le
  have hs0 := Real.sqrt_nonneg (p * (1 - p))
  refine ⟨⟨hp0, by linarith only [hq0]⟩, ?_, ?_, ?_⟩
  · nlinarith only [hv, hs, hs0, hδ]
  · nlinarith [sq_nonneg (p - 1 / 2)]
  · constructor <;> nlinarith [sq_nonneg (p - 1 / 2)]

theorem standardizedBernoulli_third_margin_bound (p δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) :
    thirdMoment (standardizedBernoulliLaw p (bernoulli_general_parameter_bounds p δ hδ hp hq).1) ≤ 1 / δ := by
  have hb := bernoulli_general_parameter_bounds p δ hδ hp hq
  rw [standardizedBernoulli_third]
  exact div_le_div₀ (by positivity) hb.2.2.2.2 hδ hb.2.1

theorem standardizedBernoulli_support_atoms (p : ℝ) (hp : p ∈ Ioo 0 1) :
    -p / Real.sqrt (p * (1 - p)) ∈ (standardizedBernoulliLaw p hp).measure.support ∧
    (1 - p) / Real.sqrt (p * (1 - p)) ∈ (standardizedBernoulliLaw p hp).measure.support := by
  constructor
  · rw [Measure.mem_support_iff_forall]
    intro U hU
    have hxU := mem_of_mem_nhds hU
    rw [standardizedBernoulliLaw_measure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    have hl : 0 < ENNReal.ofReal (1 - p) * Measure.dirac (-p / Real.sqrt (p * (1 - p))) U := by
      rw [Measure.dirac_apply_of_mem hxU, mul_one]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hp.2)
    exact hl.trans_le (le_add_right le_rfl)
  · rw [Measure.mem_support_iff_forall]
    intro U hU
    have hxU := mem_of_mem_nhds hU
    rw [standardizedBernoulliLaw_measure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    have hr : 0 < ENNReal.ofReal p * Measure.dirac ((1 - p) / Real.sqrt (p * (1 - p))) U := by
      rw [Measure.dirac_apply_of_mem hxU, mul_one]
      exact ENNReal.ofReal_pos.mpr hp.1
    exact hr.trans_le (le_add_left le_rfl)

theorem standardizedBernoulli_resonance_multiplier_zero (p : ℝ) (hp : p ∈ Ioo 0 1)
    (r : ℝ) (hr : r ≠ 0) (hres : r ∈ resonanceSubgroup (standardizedBernoulliLaw p hp).measure) :
    Real.sinc ((1 / Real.sqrt (p * (1 - p))) * r / 2) = 0 := by
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  have hh : 0 < 1 / Real.sqrt (p * (1 - p)) := one_div_pos.mpr hs
  have hsp := standardizedBernoulli_support_atoms p hp
  obtain ⟨k, hk⟩ := resonance_support_difference (standardizedBernoulliLaw p hp).measure r hres _ _ hsp.2 hsp.1
  have he : r * (1 / Real.sqrt (p * (1 - p))) = 2 * Real.pi * (k : ℝ) := by
    convert hk using 1 <;> ring
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, mul_zero] at he
    exact (mul_ne_zero hr hh.ne') he
  have he' : r = 2 * Real.pi * (k : ℝ) / (1 / Real.sqrt (p * (1 - p))) := (eq_div_iff hh.ne').mpr he
  rw [he']
  exact spanJitter_multiplier_resonance_zero _ hh k hk0

end BerryEsseen
