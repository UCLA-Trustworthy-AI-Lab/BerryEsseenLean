import BerryEsseen.BinomialMeasure
import BerryEsseen.EffectivePeakCalculus
import BerryEsseen.JitterCharacteristic
import BerryEsseen.PhaseConcentration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The Fourier route used in the manuscript's Lemma 2.5.
No Berry--Esseen inequality is an input to the atom bound below. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate ENNReal
namespace BerryEsseen

def manuscriptRawBernoulliCF (p u : ℝ) : ℂ := ((1 - p : ℝ) : ℂ) + (p : ℂ) * realPhase u 1

theorem manuscript_bernoulli_cosine_identity (p u : ℝ) :
    ‖manuscriptRawBernoulliCF p u‖ ^ 2 = 1 - 2 * p * (1 - p) * (1 - Real.cos u) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [manuscriptRawBernoulliCF, realPhase, mul_one, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  nlinarith [mul_nonneg (sq_nonneg p) (sq_nonneg (Real.sin u)), Real.sin_sq_add_cos_sq u,
    congrArg (fun r : ℝ => p ^ 2 * r) (Real.sin_sq_add_cos_sq u)]

theorem manuscript_bernoulli_charFun (p : ℝ) (hp : p ∈ Icc 0 1) (t : ℝ) :
    charFun (bernoulliMeasure p) t = manuscriptRawBernoulliCF p t := by
  rw [charFun_eq_integral_realPhase, bernoulliMeasure, mixtureMeasure,
    integral_add_measure ((realPhase_integrable (Measure.dirac 0) t).smul_measure ENNReal.ofReal_ne_top)
      ((realPhase_integrable (Measure.dirac 1) t).smul_measure ENNReal.ofReal_ne_top)]
  simp [integral_smul_measure, ENNReal.toReal_ofReal hp.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2), Complex.real_smul,
    manuscriptRawBernoulliCF, realPhase]

theorem manuscript_binomial_charFun (p : ℝ) (hp : p ∈ Icc 0 1) (n : ℕ) (t : ℝ) :
    charFun (binomialMeasure p n) t = manuscriptRawBernoulliCF p t ^ n := by
  letI := bernoulliMeasure_probability p hp
  rw [binomialMeasure, charFun_iidSumLaw, manuscript_bernoulli_charFun p hp]

theorem manuscript_bernoulli_sine_identity (p t : ℝ) :
    ‖manuscriptRawBernoulliCF p t‖ ^ 2 = 1 - 4 * p * (1 - p) * Real.sin (t / 2) ^ 2 := by
  rw [manuscript_bernoulli_cosine_identity]
  have h := Real.sin_sq_eq_half_sub (t / 2)
  have he : 2 * (t / 2) = t := by ring
  rw [he] at h
  nlinarith [congrArg (fun x : ℝ => 4 * p * (1 - p) * x) h]

theorem manuscript_sine_lower (t : ℝ) (ht : |t| ≤ Real.pi) :
    |t| / Real.pi ≤ Real.sin (|t| / 2) := by
  have h := Real.mul_le_sin (x := |t| / 2) (by positivity) (by linarith)
  convert h using 1 <;> ring

theorem manuscript_bernoulli_gaussian_decay (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (t : ℝ) (ht : |t| ≤ Real.pi) :
    ‖manuscriptRawBernoulliCF p t‖ ^ n ≤
      Real.exp (-2 * (n : ℝ) * p * (1 - p) * t ^ 2 / Real.pi ^ 2) := by
  have hsine := manuscript_sine_lower t ht
  have hsine_sq : (|t| / Real.pi) ^ 2 ≤ Real.sin (|t| / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsine 2
  have habs_sine_sq : Real.sin (|t| / 2) ^ 2 = Real.sin (t / 2) ^ 2 := by
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg ht0]
    · rw [abs_of_neg (lt_of_not_ge ht0), neg_div, Real.sin_neg, neg_sq]
  rw [div_pow, sq_abs, habs_sine_sq] at hsine_sq
  have hv : 0 ≤ p * (1 - p) := mul_nonneg hp.1 (sub_nonneg.mpr hp.2)
  have hm := mul_le_mul_of_nonneg_left hsine_sq
    (show 0 ≤ 4 * p * (1 - p) by nlinarith)
  have hb : ‖manuscriptRawBernoulliCF p t‖ ^ 2 ≤
      1 - (4 * p * (1 - p) / Real.pi ^ 2) * t ^ 2 := by
    rw [manuscript_bernoulli_sine_identity]
    ring_nf at hm ⊢
    linarith only [hm]
  convert norm_pow_gaussian_of_quadratic_bound (manuscriptRawBernoulliCF p t) t
    (4 * p * (1 - p) / Real.pi ^ 2) hb n using 1
  congr 1
  ring

theorem manuscript_integer_phase_integral (m : ℤ) :
    (∫ t in -Real.pi..Real.pi, Complex.exp (((t * (m : ℝ)) : ℝ) * Complex.I)) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hm : m = 0
  · simp [hm, intervalIntegral.integral_const]
    norm_cast
    ring
  · rw [if_neg hm]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_right (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I)) hmR]
    have ha : -Real.pi * (m : ℝ) = -(Real.pi * (m : ℝ)) := by ring
    rw [ha, integral_exp_mul_I_eq_sin]
    rw [mul_comm Real.pi (m : ℝ), Real.sin_int_mul_pi]
    simp

theorem manuscript_binomial_charFun_sum (p : ℝ) (hp : p ∈ Icc 0 1)
    (n : ℕ) (t : ℝ) :
    charFun (binomialMeasure p n) t =
      ∑ j ∈ Finset.range (n + 1), (binomialWeight p n j : ℂ) * realPhase t j := by
  rw [charFun_eq_integral_realPhase, binomialMeasure_blocks p hp]
  rw [integral_finset_sum_measure (fun j hj =>
    (integrable_dirac (by finiteness)).smul_measure (blockWeight_ne_top p n j))]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [integral_smul_measure, integral_dirac, blockWeight_toReal p hp,
    Complex.real_smul, binomialWeight]

theorem manuscript_binomial_inversion (p : ℝ) (hp : p ∈ Icc 0 1)
    (n k : ℕ) (hk : k ≤ n) :
    (∫ t in -Real.pi..Real.pi,
      charFun (binomialMeasure p n) t * Complex.exp (((-t * (k : ℝ)) : ℝ) * Complex.I)) =
        (2 * Real.pi : ℂ) * (binomialWeight p n k : ℂ) := by
  classical
  have hfun : (fun t : ℝ => charFun (binomialMeasure p n) t *
      Complex.exp (((-t * (k : ℝ)) : ℝ) * Complex.I)) =
      fun t => ∑ j ∈ Finset.range (n + 1), (binomialWeight p n j : ℂ) *
        Complex.exp (((t * ((j : ℤ) - (k : ℤ) : ℤ)) : ℝ) * Complex.I) := by
    funext t
    rw [manuscript_binomial_charFun_sum p hp, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_assoc, realPhase, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfun, intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul, manuscript_integer_phase_integral]
    simp only [sub_eq_zero, Nat.cast_inj]
    rw [Finset.sum_eq_single k]
    · simp
      ring
    · intro b hb hbk
      simp [hbk]
    · intro hkn
      exact False.elim (hkn (Finset.mem_range.mpr (by omega)))
  · intro j hj
    apply Continuous.intervalIntegrable
    fun_prop

theorem manuscript_binomial_fourier_mass_bound (p : ℝ) (hp : p ∈ Icc 0 1)
    (n k : ℕ) (hk : k ≤ n) :
    binomialWeight p n k ≤ (1 / (2 * Real.pi)) *
      ∫ t in -Real.pi..Real.pi, ‖manuscriptRawBernoulliCF p t‖ ^ n := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => charFun (binomialMeasure p n) t *
      Complex.exp (((-t * (k : ℝ)) : ℝ) * Complex.I)) (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)
  rw [manuscript_binomial_inversion p hp n k hk] at h
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    manuscript_binomial_charFun p hp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (binomialWeight_nonneg p hp n k)] at h
  norm_num [abs_of_pos Real.pi_pos] at h
  have h' : binomialWeight p n k ≤
      (∫ t in -Real.pi..Real.pi, ‖manuscriptRawBernoulliCF p t‖ ^ n) / (2 * Real.pi) :=
    (le_div_iff₀ hπ).mpr (by nlinarith only [h])
  convert h' using 1 <;> ring

theorem manuscript_binomial_gaussian_integral_bound (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    binomialWeight p n k ≤ (1 / (2 * Real.pi)) *
      ∫ t : ℝ, Real.exp (-(2 * (n : ℝ) * p * (1 - p) / Real.pi ^ 2) * t ^ 2) := by
  have hpcc : p ∈ Icc 0 1 := ⟨hp.1.le, hp.2.le⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < p := hp.1
  have hq0 : 0 < 1 - p := sub_pos.mpr hp.2
  have hb : 0 < 2 * (n : ℝ) * p * (1 - p) / Real.pi ^ 2 := by
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hnR) hp.1) (sub_pos.mpr hp.2)) (sq_pos_of_pos Real.pi_pos)
  have hI := integrable_exp_neg_mul_sq hb
  have hf : Continuous (fun t : ℝ => ‖manuscriptRawBernoulliCF p t‖ ^ n) := by
    unfold manuscriptRawBernoulliCF realPhase
    fun_prop
  have hg : Continuous (fun t : ℝ => Real.exp (-(2 * (n : ℝ) * p * (1 - p) / Real.pi ^ 2) * t ^ 2)) := by
    fun_prop
  apply (manuscript_binomial_fourier_mass_bound p hpcc n k hk).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∫ t in -Real.pi..Real.pi, ‖manuscriptRawBernoulliCF p t‖ ^ n) ≤
        ∫ t in -Real.pi..Real.pi,
          Real.exp (-(2 * (n : ℝ) * p * (1 - p) / Real.pi ^ 2) * t ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
      intro t ht
      convert manuscript_bernoulli_gaussian_decay p hpcc n t (abs_le.mpr ht) using 1
      congr 1
      ring
    _ ≤ _ := by
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
      exact setIntegral_le_integral hI (ae_of_all _ (fun t => (Real.exp_pos _).le))

theorem manuscript_binomial_atom_bound (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    binomialWeight p n k ≤
      (Real.sqrt (Real.pi ^ 3 / (2 * p * (1 - p))) / (2 * Real.pi)) /
        Real.sqrt (n : ℝ) := by
  have h := manuscript_binomial_gaussian_integral_bound p hp n k hn hk
  rw [integral_gaussian] at h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < p := hp.1
  have hq0 : 0 < 1 - p := sub_pos.mpr hp.2
  have he : Real.pi / (2 * (n : ℝ) * p * (1 - p) / Real.pi ^ 2) =
      (Real.pi ^ 3 / (2 * p * (1 - p))) / (n : ℝ) := by
    field_simp
    <;> ring
  rw [he, Real.sqrt_div (by positivity)] at h
  convert h using 1 <;> ring

theorem manuscript_binomial_uniform_atom_bound (p δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (n k : ℕ) (hn : 1 ≤ n) :
    binomialWeight p n k ≤
      (Real.sqrt (Real.pi ^ 3 / (2 * δ ^ 2)) / (2 * Real.pi)) /
        Real.sqrt (n : ℝ) := by
  have hpI : p ∈ Ioo 0 1 := ⟨hδ.trans_le hp, by linarith⟩
  by_cases hk : k ≤ n
  · apply (manuscript_binomial_atom_bound p hpI n k hn hk).trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hv := mul_le_mul hp hq hδ.le (hδ.trans_le hp).le
    nlinarith only [hv]
  · simp [binomialWeight, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
    positivity

theorem manuscript_effective_binomial_mass_upper (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n k : ℕ) (hn : 1 ≤ n) :
    binomialWeight p n k ≤ 2 / Real.sqrt (n : ℝ) := by
  have h := manuscript_binomial_uniform_atom_bound p (2 / 5) (by norm_num)
    hp.1 (by linarith [hp.2]) n k hn
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  have hs : Real.pi ^ 3 / (2 * (2 / 5 : ℝ) ^ 2) ≤ (4 * Real.pi) ^ 2 := by
    apply (div_le_iff₀ (by norm_num : 0 < 2 * (2 / 5 : ℝ) ^ 2)).mpr
    have hm := mul_le_mul_of_nonneg_left Real.pi_lt_four.le (sq_nonneg Real.pi)
    nlinarith only [hm, sq_nonneg Real.pi]
  have hr := (Real.sqrt_le_iff).mpr ⟨(by positivity : 0 ≤ 4 * Real.pi), hs⟩
  nlinarith only [hr]

theorem manuscript_binomial_uniform_atom_coefficient (δ : ℝ) (hδ : 0 < δ) :
    Real.sqrt (Real.pi ^ 3 / (2 * δ ^ 2)) / (2 * Real.pi) ≤ 3 / (4 * δ) := by
  have hπ := Real.pi_pos
  have hs : Real.pi ^ 3 / (2 * δ ^ 2) ≤ (3 * Real.pi / (2 * δ)) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * δ ^ 2) (by positivity : 0 < (2 * δ) ^ 2)).mpr
    have h := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (show 0 ≤ Real.pi ^ 2 * δ ^ 2 by positivity)
    nlinarith only [h, mul_nonneg (sq_nonneg Real.pi) (sq_nonneg δ)]
  have hroot := (Real.sqrt_le_iff).mpr ⟨(by positivity : 0 ≤ 3 * Real.pi / (2 * δ)), hs⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  convert hroot using 1 <;> ring

end BerryEsseen
