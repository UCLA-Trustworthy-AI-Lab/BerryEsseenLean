import BerryEsseen.LatticeCentered

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem centered_signed_third_of_representation (μ : Measure ℝ) (Z : StandardizedLaw)
    (m σ : ℝ) (hσ : 0 < σ) (hmap : Z.measure = standardizedMeasure μ m σ) :
    (∫ x, (x - m) ^ 3 ∂μ) = σ ^ 3 * signedThirdMoment Z := by
  rw [inverse_standardized_representation μ Z m σ hσ hmap,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [add_sub_cancel_right, mul_pow]
  exact integral_const_mul _ _

theorem two_atom_centered_deficit_formula (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a < b) (hx : ∀ᵐ x ∂μ, x = a ∨ x = b)
    (hσ : 0 < rawStdDev μ) :
    latticeCenteredDeficit μ (b - a) = rawStdDev μ ^ 3 *
      (2 * cStar * (μ.real {b} - pE) ^ 2 / Real.sqrt (μ.real {b} * (1 - μ.real {b}))) := by
  let p := μ.real {b}
  have hp := two_atoms_probability_interior μ a b hab hx hσ
  have hrep := two_atoms_canonical_standardization μ a b hab hx hσ
  let Z := standardizedBernoulliLaw p hp
  have hmom := raw_moments_of_standardized_representation μ Z (rawMean μ) (rawStdDev μ) hσ hrep.1
  have hsgn := centered_signed_third_of_representation μ Z (rawMean μ) (rawStdDev μ) hσ hrep.1
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  have hpoly : cStar * (p ^ 2 + (1 - p) ^ 2) - (1 - 2 * p) - 3 =
      2 * cStar * (p - pE) ^ 2 := by
    nlinarith only [bernoulli_moment_deficit_identity p]
  unfold latticeCenteredDeficit
  rw [hmom.2.2, hsgn]
  dsimp only [Z]
  rw [standardizedBernoulli_third, standardizedBernoulli_signed_third]
  change cStar * (rawStdDev μ ^ 3 * ((p ^ 2 + (1 - p) ^ 2) / Real.sqrt (p * (1 - p)))) -
      rawStdDev μ ^ 3 * ((1 - 2 * p) / Real.sqrt (p * (1 - p))) - 3 * (b - a) * rawStdDev μ ^ 2 = _
  calc
    _ = rawStdDev μ ^ 3 / Real.sqrt (p * (1 - p)) *
        (cStar * (p ^ 2 + (1 - p) ^ 2) - (1 - 2 * p) - 3) := by
      rw [hrep.2.2]
      change _ = _
      field_simp [hs.ne']
      <;> ring
    _ = _ := by rw [hpoly]; ring

theorem small_variance_scale_cube_lower (σ δ : ℝ) (hσ : 0 < σ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) (hv : |σ ^ 2 - 1| ≤ 5 * δ) : 2 / 3 ≤ σ ^ 3 := by
  have hlo := (abs_le.mp hv).1
  have hs : 99 / 100 ≤ σ := by nlinarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 99 / 100) hs 3
  norm_num at hp
  linarith

theorem manuscript_lattice_parameter_error_exact (p σ δ : ℝ) (hp : p ∈ Ioo 0 1) (hσ : 0 < σ)
    (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6)) (hv : |σ ^ 2 - 1| ≤ 5 * δ)
    (hF : σ ^ 3 * (2 * cStar * (p - pE) ^ 2 / Real.sqrt (p * (1 - p))) ≤ 2000 * δ) :
    |p - pE| ≤ Real.sqrt (750 / cStar) * Real.sqrt δ ∧
      |p - pE| ≤ 12 * Real.sqrt δ := by
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr (mul_pos hp.1 (sub_pos.mpr hp.2))
  have hsupper : Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
    have hsq := Real.sq_sqrt (mul_pos hp.1 (sub_pos.mpr hp.2)).le
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hc := cStar_effective_bounds
  have hc0 : 0 ≤ cStar := by linarith [hc.1]
  have hδ0 := hδ.1
  have hH : 0 ≤ 2 * cStar * (p - pE) ^ 2 / Real.sqrt (p * (1 - p)) := by positivity
  have hbound : 2 * cStar * (p - pE) ^ 2 / Real.sqrt (p * (1 - p)) ≤ 3000 * δ := by
    have hm := mul_le_mul_of_nonneg_right (small_variance_scale_cube_lower σ δ hσ hδ.2 hv) hH
    nlinarith only [hm, hF]
  have hnum := (div_le_iff₀ hs).mp hbound
  have hden := mul_le_mul_of_nonneg_left hsupper (show 0 ≤ 3000 * δ by positivity)
  have hcpos : 0 < cStar := by linarith [hc.1]
  have hsquare : (p - pE) ^ 2 ≤ (750 / cStar) * δ := by
    rw [show (750 / cStar) * δ = (750 * δ) / cStar by ring]
    apply (le_div_iff₀ hcpos).mpr
    nlinarith only [hnum, hden]
  have hexact : |p - pE| ≤ Real.sqrt (750 / cStar) * Real.sqrt δ := by
    have hh := Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (by positivity : 0 ≤ 750 / cStar)] at hh
    exact hh
  have hconstant : Real.sqrt (750 / cStar) ≤ 12 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hcpos).mpr
    nlinarith [hc.1]
  exact ⟨hexact, hexact.trans (mul_le_mul_of_nonneg_right hconstant (Real.sqrt_nonneg δ))⟩

theorem lattice_parameter_error (p σ δ : ℝ) (hp : p ∈ Ioo 0 1) (hσ : 0 < σ)
    (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6)) (hv : |σ ^ 2 - 1| ≤ 5 * δ)
    (hF : σ ^ 3 * (2 * cStar * (p - pE) ^ 2 / Real.sqrt (p * (1 - p))) ≤ 2000 * δ) :
    |p - pE| ≤ 12 * Real.sqrt δ :=
  (manuscript_lattice_parameter_error_exact p σ δ hp hσ hδ hv hF).2

theorem lattice_parameter_interval (p δ : ℝ) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hp : |p - pE| ≤ 12 * Real.sqrt δ) : p ∈ Icc (2 / 5) (9 / 20) := by
  have hE : 209 / 500 < pE ∧ pE < 21 / 50 := by
    unfold pE
    constructor <;> nlinarith [sqrt10_sq, sqrt10_bounds.1, sqrt10_bounds.2]
  have hs : Real.sqrt δ ≤ 1 / 1000 := by nlinarith [Real.sq_sqrt hδ.1, Real.sqrt_nonneg δ, hδ.2]
  have hpabs := abs_le.mp hp
  constructor <;> linarith [hE.1, hE.2, hpabs.1, hpabs.2]

theorem effective_lattice_conditional_parameter (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧ P.measure {-a, b} ≠ 0 ∧
      P.measure.real ({-a, b}ᶜ : Set ℝ) ≤ δ ∧
      |rawMean (ProbabilityTheory.cond P.measure {-a, b})| ≤ 2 * δ ∧
      |rawStdDev (ProbabilityTheory.cond P.measure {-a, b}) ^ 2 - 1| ≤ 5 * δ ∧
      0 < rawStdDev (ProbabilityTheory.cond P.measure {-a, b}) ∧
      (ProbabilityTheory.cond P.measure {-a, b}).real {b} ∈ Icc (2 / 5) (9 / 20) ∧
      |(ProbabilityTheory.cond P.measure {-a, b}).real {b} - pE| ≤ 12 * Real.sqrt δ := by
  obtain ⟨a, b, ha, hb, hab, hnz, hr, hm, hv, hσ, hF⟩ :=
    effective_lattice_centered_conditioning P h δ hlat hβ hκ hD hδ
  let ν := ProbabilityTheory.cond P.measure {-a, b}
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  have hp := two_atoms_probability_interior ν (-a) b (by linarith) (conditional_pair_mem _ _ _) hσ
  have he := two_atom_centered_deficit_formula ν (-a) b (by linarith) (conditional_pair_mem _ _ _) hσ
  rw [show b - -a = h by linarith] at he
  change latticeCenteredDeficit ν h ≤ 2000 * δ at hF
  rw [he] at hF
  have hparam := lattice_parameter_error _ (rawStdDev ν) δ hp hσ ⟨hD.1.trans hD.2, hδ⟩ hv hF
  exact ⟨a, b, ha, hb, hab, hnz, hr, hm, hv, hσ,
    lattice_parameter_interval _ δ ⟨hD.1.trans hD.2, hδ⟩ hparam, hparam⟩

theorem manuscript_bernoulli_span_hasDerivAt (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    HasDerivAt (fun t : ℝ => (Real.sqrt (t * (1 - t)))⁻¹)
      (-(1 - 2 * p) / (2 * (Real.sqrt (p * (1 - p))) ^ 3)) p := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hv : 0 < p * (1 - p) := mul_pos hp01.1 (sub_pos.mpr hp01.2)
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hv
  have hd : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * p) p := by
    have hh := (hasDerivAt_id p).mul ((hasDerivAt_const p 1).sub (hasDerivAt_id p))
    simp only [Pi.sub_apply, id_eq, mul_one, one_mul, sub_zero, zero_sub] at hh
    convert hh using 1 <;> ring
  convert (hd.sqrt hv.ne').inv hs.ne' using 1
  field_simp [hs.ne']
  <;> ring

theorem manuscript_bernoulli_span_derivative_bound (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    |-(1 - 2 * p) / (2 * (Real.sqrt (p * (1 - p))) ^ 3)| < 1 := by
  have hslo := (effective_binomial_parameters p hp).2.1
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg (show 0 ≤ 1 - 2 * p by linarith [hp.2]),
    abs_of_pos (show 0 < 2 * (Real.sqrt (p * (1 - p))) ^ 3 by positivity)]
  apply (div_lt_one (by positivity : 0 < 2 * (Real.sqrt (p * (1 - p))) ^ 3)).mpr
  have hc := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.48) hslo 3
  norm_num at hc
  linarith [hp.1]

theorem manuscript_bernoulli_span_lt_three (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) :
    (Real.sqrt (p * (1 - p)))⁻¹ < 3 := by
  have hslo := (effective_binomial_parameters p hp).2.1
  have hs : 0 < Real.sqrt (p * (1 - p)) := by linarith
  rw [← one_div, div_lt_iff₀ hs]
  linarith

theorem bernoulli_span_lipschitz (p q : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hq : q ∈ Icc (2 / 5) (9 / 20)) :
    |(Real.sqrt (p * (1 - p)))⁻¹ - (Real.sqrt (q * (1 - q)))⁻¹| ≤ |p - q| := by
  have hd : ∀ t ∈ Icc (2 / 5 : ℝ) (9 / 20),
      HasDerivWithinAt (fun t : ℝ => (Real.sqrt (t * (1 - t)))⁻¹)
        (-(1 - 2 * t) / (2 * (Real.sqrt (t * (1 - t))) ^ 3))
        (Icc (2 / 5 : ℝ) (9 / 20)) t :=
    fun t ht => (manuscript_bernoulli_span_hasDerivAt t ht).hasDerivWithinAt
  have hb : ∀ t ∈ Icc (2 / 5 : ℝ) (9 / 20),
      ‖-(1 - 2 * t) / (2 * (Real.sqrt (t * (1 - t))) ^ 3)‖ ≤ 1 := by
    intro t ht
    exact (manuscript_bernoulli_span_derivative_bound t ht).le
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _) hq hp
  simpa only [Real.norm_eq_abs, one_mul] using hh

theorem manuscript_lattice_span_error_budget (p σ h δ : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hσ : 0 < σ) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hv : |σ ^ 2 - 1| ≤ 5 * δ) (hscale : σ = h * Real.sqrt (p * (1 - p)))
    (hparam : |p - pE| ≤ 12 * Real.sqrt δ) :
    |h - hE| ≤ 15 * δ + 12 * Real.sqrt δ ∧ |h - hE| ≤ 1000 * Real.sqrt δ := by
  let s := Real.sqrt (p * (1 - p))
  let t := Real.sqrt (pE * (1 - pE))
  have hslo : 0.48 ≤ s := (effective_binomial_parameters p hp).2.1
  have hs : 0 < s := by linarith
  have ht : hE = t⁻¹ := by unfold hE t sigmaE qE; rw [one_div]
  have hdiff := bernoulli_span_lipschitz p pE hp ⟨pE_bounds.1.le, pE_bounds.2.le⟩
  have hσdiff : |σ - 1| ≤ 5 * δ := by
    have he : |σ - 1| * (σ + 1) = |σ ^ 2 - 1| := by
      rw [← abs_of_pos (show 0 < σ + 1 by linarith), ← abs_mul]
      congr 1
      ring
    have hm := mul_nonneg hσ.le (abs_nonneg (σ - 1))
    nlinarith only [he, hm, hv]
  have hscale' : h = σ / s := by
    apply (eq_div_iff hs.ne').mpr
    exact hscale.symm
  have hsplit : h - hE = (σ - 1) / s + (s⁻¹ - t⁻¹) := by
    rw [hscale', ht]
    ring
  have hfirst : |(σ - 1) / s| ≤ 3 * |σ - 1| := by
    rw [abs_div, abs_of_pos hs, div_eq_mul_inv]
    have hh := mul_le_mul_of_nonneg_left (manuscript_bernoulli_span_lt_three p hp).le
      (abs_nonneg (σ - 1))
    simpa only [mul_comm] using hh
  rw [hsplit]
  have hbound := abs_add_le ((σ - 1) / s) (s⁻¹ - t⁻¹)
  have hδroot : δ ≤ Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.1, Real.sqrt_nonneg δ, hδ.1, hδ.2]
  change |s⁻¹ - t⁻¹| ≤ |p - pE| at hdiff
  constructor <;> nlinarith [Real.sqrt_nonneg δ]

theorem lattice_span_error (p σ h δ : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hσ : 0 < σ) (hδ : δ ∈ Icc 0 (1 / (10 : ℝ) ^ 6))
    (hv : |σ ^ 2 - 1| ≤ 5 * δ) (hscale : σ = h * Real.sqrt (p * (1 - p)))
    (hparam : |p - pE| ≤ 12 * Real.sqrt δ) : |h - hE| ≤ 1000 * Real.sqrt δ :=
  (manuscript_lattice_span_error_budget p σ h δ hp hσ hδ hv hscale hparam).2

theorem effective_lattice_span_stability_nonnegative (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) : |h - hE| ≤ 1000 * Real.sqrt δ := by
  obtain ⟨a, b, ha, hb, hab, hnz, hr, hm, hv, hσ, hp, hparam⟩ :=
    effective_lattice_conditional_parameter P h δ hlat hβ hκ hD hδ
  let ν := ProbabilityTheory.cond P.measure {-a, b}
  letI : IsProbabilityMeasure ν := cond_isProbabilityMeasure hnz
  have hrep := two_atoms_canonical_standardization ν (-a) b (by linarith) (conditional_pair_mem _ _ _) hσ
  have hscale : rawStdDev ν = h * Real.sqrt (ν.real {b} * (1 - ν.real {b})) := by
    simpa only [show b - -a = h by linarith] using hrep.2.2
  exact lattice_span_error _ (rawStdDev ν) h δ hp hσ ⟨hD.1.trans hD.2, hδ⟩ hv hscale hparam

theorem latticeMomentDeficit_reflected (P : StandardizedLaw) (h : ℝ) :
    latticeMomentDeficit (reflectedLaw P) h = latticeMomentDeficit P h := by
  rw [latticeMomentDeficit, reflectedLaw_thirdMoment, reflectedLaw_signedThirdMoment, abs_neg]
  rfl

theorem effective_lattice_span_stability (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hD : latticeMomentDeficit P h ∈ Icc 0 δ) (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    |h - hE| ≤ 1000 * Real.sqrt δ := by
  by_cases hκ : 0 ≤ signedThirdMoment P
  · exact effective_lattice_span_stability_nonnegative P h δ hlat hβ hκ hD hδ
  · apply effective_lattice_span_stability_nonnegative (reflectedLaw P) h δ (reflected_lattice_span P h hlat)
    · simpa only [reflectedLaw_thirdMoment] using hβ
    · rw [reflectedLaw_signedThirdMoment]
      linarith
    · simpa only [latticeMomentDeficit_reflected] using hD
    · exact hδ

end BerryEsseen
