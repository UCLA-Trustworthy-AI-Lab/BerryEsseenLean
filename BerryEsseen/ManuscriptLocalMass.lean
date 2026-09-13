import BerryEsseen.ManuscriptBinomialTheorem
import BerryEsseen.EffectiveLocalMass
import BerryEsseen.ReflectionBounds

/-! The original local-mass proof with A₀=3·10⁶/√2, c₁ as printed,
the original [λ/2,3λ/2] conditional variance window, and open endpoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def manuscriptLocalA0 : ℝ := 3000000 / Real.sqrt 2
def manuscriptLocalC1 : ℝ := (1 / 4) * Real.sqrt (2 / 3) * standardNormalDensity manuscriptLocalA0

theorem manuscriptLocalA0_pos : 0 < manuscriptLocalA0 := by unfold manuscriptLocalA0; positivity

theorem manuscriptLocalA0_sq : manuscriptLocalA0 ^ 2 = 4500000000000 := by
  unfold manuscriptLocalA0
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem manuscriptLocalC1_formula :
    manuscriptLocalC1 = (Real.sqrt (2 / 3) * phi0 / 4) * Real.exp (-2250000000000) := by
  unfold manuscriptLocalC1
  rw [standardNormalDensity_formula, manuscriptLocalA0_sq]
  norm_num
  ring

theorem manuscriptLocalC1_pos : 0 < manuscriptLocalC1 := by
  unfold manuscriptLocalC1
  have := standardNormalDensity_pos manuscriptLocalA0
  positivity

theorem manuscript_local_density_budgets :
    Real.exp (-3000000000000) < manuscriptLocalC1 ∧
    Real.exp (-appendixA) ≤ manuscriptLocalC1 / (4 * Real.sqrt 2) ∧
    Real.exp (-4000000000000) ≤ Real.exp (-100) * (manuscriptLocalC1 / 2) := by
  have hs23 : (1 / 2 : ℝ) ≤ Real.sqrt (2 / 3) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hp := phi0_pos
  have hsmall := exp_neg_le_phi0_sixty_four 750000000000 (by norm_num)
  have hexp := Real.exp_pos (-2250000000000 : ℝ)
  have hm := mul_le_mul_of_nonneg_left hsmall hexp.le
  rw [← Real.exp_add] at hm
  norm_num at hm
  have hc : Real.exp (-3000000000000) < manuscriptLocalC1 := by
    rw [manuscriptLocalC1_formula]
    have hf := mul_le_mul_of_nonneg_right hs23 hp.le
    nlinarith only [hm, hf, hp, hexp, mul_pos hexp hp]
  refine ⟨hc, ?_, ?_⟩
  · have h97 := exp_neg_le_phi0_sixty_four 97000000000000 (by norm_num)
    have h97' : Real.exp (-97000000000000 : ℝ) ≤ 1 / 8 := by
      linarith [phi0_lt_two_fifths]
    have hm97 := mul_le_mul_of_nonneg_left h97' (Real.exp_pos (-3000000000000 : ℝ)).le
    rw [← Real.exp_add] at hm97
    norm_num [appendixA] at hm97 ⊢
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt (2 : ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_left hs2 (Real.exp_pos (-100000000000000 : ℝ)).le
    nlinarith only [hm97, hmul, hc]
  · have hlast := exp_neg_le_phi0_sixty_four 999999999900 (by norm_num)
    have hlast' : Real.exp (-999999999900 : ℝ) ≤ 1 / 2 := by
      linarith [phi0_lt_two_fifths]
    have hm' := mul_le_mul_of_nonneg_left hlast' (Real.exp_pos (-3000000000100 : ℝ)).le
    rw [← Real.exp_add] at hm'
    norm_num at hm'
    have hexact : Real.exp (-3000000000100 : ℝ) =
        Real.exp (-100) * Real.exp (-3000000000000) := by
      rw [← Real.exp_add]
      norm_num
    rw [hexact] at hm'
    have hmult := mul_le_mul_of_nonneg_left hc.le (Real.exp_pos (-100 : ℝ)).le
    nlinarith only [hm', hmult]

theorem manuscript_noise_window_endpoint (lam t x k a : ℝ)
    (hlam : 1 / (10 : ℝ) ^ 12 ≤ lam) (ht : lam / 2 ≤ t)
    (hxk : |k - x| ≤ max 1 (Real.sqrt lam)) (ha : |a| ≤ 1 / 2) :
    |((x + a) - k) / Real.sqrt t| ≤ manuscriptLocalA0 := by
  have hL : 0 < lam := by linarith
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.mpr ht0
  have htsq := Real.sq_sqrt ht0.le
  have hLsq := Real.sq_sqrt hL.le
  have h2sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h2pos := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hnum : |(x + a) - k| ≤ max 1 (Real.sqrt lam) + 1 / 2 := by
    have htri := abs_add_le (x - k) a
    rw [abs_sub_comm x k] at htri
    rw [show (x + a) - k = (x - k) + a by ring]
    linarith
  rw [abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  unfold manuscriptLocalA0
  apply (le_of_mul_le_mul_right ?_ h2pos)
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ h2pos.ne']
  by_cases hsmall : Real.sqrt lam ≤ 1
  · rw [max_eq_left hsmall] at hnum
    have hm := mul_le_mul_of_nonneg_right hnum h2pos.le
    have hroot : (3 / 2 : ℝ) * Real.sqrt 2 ≤ 3000000 * Real.sqrt t := by
      nlinarith only [htsq, h2sq, hlam, ht, hs.le, h2pos.le]
    nlinarith only [hm, hroot]
  · rw [max_eq_right (le_of_not_ge hsmall)] at hnum
    have hsL : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have hroot : Real.sqrt lam ≤ Real.sqrt 2 * Real.sqrt t := by
      nlinarith only [hLsq, htsq, h2sq, ht, hsL, mul_pos h2pos hs]
    have hm := mul_le_mul_of_nonneg_right hnum h2pos.le
    have hroot2 := mul_le_mul_of_nonneg_right hroot h2pos.le
    have hbig : (1 : ℝ) ≤ Real.sqrt 2 * Real.sqrt t := by linarith
    have hbig2 := mul_le_mul_of_nonneg_right hbig h2pos.le
    nlinarith only [hm, hroot2, hbig2, h2sq, hs.le]

theorem manuscript_open_interval_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (hab : a < b) : μ.real (Ioo a b) = strictCDF μ b - cdf μ a := by
  rw [← Iio_diff_Iic, measureReal_diff (by intro x hx; exact lt_of_le_of_lt hx hab) measurableSet_Iic]
  rw [cdf_eq_real]
  rfl

theorem manuscript_noise_cdf_unit_bound (I : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (ht : 0 < (twoNoiseBlock P Q n k).secondMoment) (x : ℝ) :
    |cdf (twoNoiseBlock P Q n k).measure x - normalCDF (x / Real.sqrt (twoNoiseBlock P Q n k).secondMoment)| ≤
      ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment := by
  have h := twoNoiseBlock_normal_bound I P Q ε hε hP hQ n k hn hk ht x
  have hs : 0 < Real.sqrt (twoNoiseBlock P Q n k).secondMoment := Real.sqrt_pos.mpr ht
  exact h.trans (div_le_div_of_nonneg_right (by nlinarith only [hε]) hs.le)

theorem manuscript_noise_open_interval_bound (I : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (ht : 0 < (twoNoiseBlock P Q n k).secondMoment)
    (a b : ℝ) (hab : a < b) :
    normalCDF (b / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) -
      normalCDF (a / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) -
      2 * ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment ≤
        (twoNoiseBlock P Q n k).measure.real (Ioo a b) := by
  have hb := strictCDF_uniform_bound (twoNoiseBlock P Q n k).measure
    (fun x => normalCDF (x / Real.sqrt (twoNoiseBlock P Q n k).secondMoment))
    (normalCDF_continuous.comp (by fun_prop)) 1 (ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment)
    (fun x => by simpa only [one_mul] using manuscript_noise_cdf_unit_bound I P Q ε hε hP hQ n k hn hk ht x) b
  have ha := manuscript_noise_cdf_unit_bound I P Q ε hε hP hQ n k hn hk ht a
  rw [manuscript_open_interval_cdf _ _ _ hab]
  simp only [one_mul] at hb
  have hb' := (abs_le.mp hb).1
  have ha' := (abs_le.mp ha).2
  simp only [div_eq_mul_inv] at ha' hb' ⊢
  linarith only [ha', hb']

theorem manuscript_noise_gaussian_mass (lam t a b : ℝ)
    (hL : 0 < lam) (ht0 : 0 < t) (ht : t ≤ 3 * lam / 2)
    (ha : |a / Real.sqrt t| ≤ manuscriptLocalA0)
    (hb : |b / Real.sqrt t| ≤ manuscriptLocalA0) (hab : 1 / 4 ≤ b - a) :
    manuscriptLocalC1 / Real.sqrt lam ≤ normalCDF (b / Real.sqrt t) - normalCDF (a / Real.sqrt t) := by
  have hs := Real.sqrt_pos.mpr ht0
  have hsL := Real.sqrt_pos.mpr hL
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hs23 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 / 3 by norm_num)
  have hr : Real.sqrt (2 / 3 : ℝ) * Real.sqrt t ≤ Real.sqrt lam := by
    nlinarith only [Real.sq_sqrt ht0.le, Real.sq_sqrt hL.le, hsq, ht, mul_pos hs23 hs, hsL.le]
  have hn := normalCDF_interval_central_lower manuscriptLocalA0 (a / Real.sqrt t) (b / Real.sqrt t)
    manuscriptLocalA0_pos.le ha hb (div_le_div_of_nonneg_right (by linarith : a ≤ b) hs.le)
  have hD : centralDensityFloor manuscriptLocalA0 = standardNormalDensity manuscriptLocalA0 := by
    rw [standardNormalDensity_formula]
    rfl
  rw [hD] at hn
  have hcoef : manuscriptLocalC1 * Real.sqrt t ≤ (b - a) * standardNormalDensity manuscriptLocalA0 * Real.sqrt lam := by
    have hm := mul_le_mul_of_nonneg_right hr (standardNormalDensity_pos manuscriptLocalA0).le
    have hwidth := mul_le_mul_of_nonneg_right hab
      (mul_nonneg (standardNormalDensity_pos manuscriptLocalA0).le hsL.le)
    unfold manuscriptLocalC1
    nlinarith only [hm, hwidth]
  have hfrac : manuscriptLocalC1 / Real.sqrt lam ≤
      ((b - a) / Real.sqrt t) * standardNormalDensity manuscriptLocalA0 := by
    apply (div_le_iff₀ hsL).mpr
    apply (le_of_mul_le_mul_right ?_ hs)
    convert hcoef using 1 <;> field_simp <;> ring
  apply hfrac.trans
  convert hn using 1 <;> ring

theorem manuscript_noise_block_window_mass (I : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (lam x a b : ℝ)
    (hlam : 1 / (10 : ℝ) ^ 12 ≤ lam)
    (htlo : lam / 2 ≤ (twoNoiseBlock P Q n k).secondMoment)
    (hthi : (twoNoiseBlock P Q n k).secondMoment ≤ 3 * lam / 2)
    (hxk : |(k : ℝ) - x| ≤ max 1 (Real.sqrt lam))
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    manuscriptLocalC1 / (2 * Real.sqrt lam) ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo ((x + a) - k) ((x + b) - k)) := by
  let t := (twoNoiseBlock P Q n k).secondMoment
  have hL : 0 < lam := by linarith
  have ht : 0 < t := by dsimp only [t]; linarith
  have hs := Real.sqrt_pos.mpr ht
  have hsL := Real.sqrt_pos.mpr hL
  have hroot : Real.sqrt lam ≤ Real.sqrt (2 : ℝ) * Real.sqrt t := by
    nlinarith only [Real.sq_sqrt ht.le, Real.sq_sqrt hL.le,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), htlo, hsL.le,
      mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)) hs]
  have hε := manuscript_local_density_budgets.2.1
  have hε' := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt (2 : ℝ))).mp hε
  have herror : 2 * Real.exp (-appendixA) / Real.sqrt t ≤ manuscriptLocalC1 / (2 * Real.sqrt lam) := by
    apply (div_le_div_iff₀ hs (by positivity : 0 < 2 * Real.sqrt lam)).mpr
    have hm := mul_le_mul_of_nonneg_left hroot (Real.exp_pos (-appendixA)).le
    have hc := mul_le_mul_of_nonneg_right hε' hs.le
    nlinarith only [hm, hc]
  have hgauss := manuscript_noise_gaussian_mass lam t ((x + a) - k) ((x + b) - k) hL ht hthi
    (manuscript_noise_window_endpoint lam t x k a hlam htlo hxk ha)
    (manuscript_noise_window_endpoint lam t x k b hlam htlo hxk hb) (by linarith)
  have hBE := manuscript_noise_open_interval_bound I P Q (Real.exp (-appendixA)) (Real.exp_pos _).le
    hP hQ n k hn hk ht ((x + a) - k) ((x + b) - k) (by linarith)
  change normalCDF (((x + b) - k) / Real.sqrt t) - normalCDF (((x + a) - k) / Real.sqrt t) -
    2 * Real.exp (-appendixA) / Real.sqrt t ≤ _ at hBE
  have he : manuscriptLocalC1 / Real.sqrt lam = 2 * (manuscriptLocalC1 / (2 * Real.sqrt lam)) := by ring
  linarith only [hgauss, hBE, herror, he]

theorem manuscriptLocalC1_printed_formula :
    manuscriptLocalC1 = Real.exp (-2250000000000) / (4 * Real.sqrt (3 * Real.pi)) := by
  have hpi := Real.pi_pos
  have h2 : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi)).ne'
  have h3 : Real.sqrt (3 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 3 * Real.pi)).ne'
  have he : Real.sqrt (2 / 3 : ℝ) * Real.sqrt (3 * Real.pi) = Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    congr 1
    ring
  rw [manuscriptLocalC1_formula, phi0]
  field_simp [h2, h3]
  nlinarith only [he]

theorem manuscript_conditional_variance_window (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n)
    (hlam : 0 < accumulatedNoiseVariance P Q p n)
    (hcentral : |(k : ℝ) - n * p| ≤ 5 * Real.sqrt (n : ℝ)) :
    |(twoNoiseBlock P Q n k).secondMoment / accumulatedNoiseVariance P Q p n - 1| ≤
      25 / (2 * Real.sqrt (n : ℝ)) ∧
    accumulatedNoiseVariance P Q p n / 2 ≤ (twoNoiseBlock P Q n k).secondMoment ∧
    (twoNoiseBlock P Q n k).secondMoment ≤ 3 * accumulatedNoiseVariance P Q p n / 2 := by
  have hn1 : 1 ≤ n := by omega
  have hq : (2 / 5 : ℝ) ≤ 1 - p := by linarith [hp.2]
  have hclose := noise_variance_central_bound P Q p (2 / 5) 5 (by norm_num) hp.1 hq (by norm_num)
    n k hn1 hk hcentral
  have hroot := effective_binomial_root_lower n hn
  have hr0 : 0 < Real.sqrt (n : ℝ) := by norm_num at hroot; linarith
  have he : 5 * accumulatedNoiseVariance P Q p n / ((2 / 5 : ℝ) * Real.sqrt (n : ℝ)) =
      (25 / (2 * Real.sqrt (n : ℝ))) * accumulatedNoiseVariance P Q p n := by ring
  rw [he] at hclose
  have hratio : |(twoNoiseBlock P Q n k).secondMoment / accumulatedNoiseVariance P Q p n - 1| ≤
      25 / (2 * Real.sqrt (n : ℝ)) := by
    rw [show (twoNoiseBlock P Q n k).secondMoment / accumulatedNoiseVariance P Q p n - 1 =
      ((twoNoiseBlock P Q n k).secondMoment - accumulatedNoiseVariance P Q p n) / accumulatedNoiseVariance P Q p n by
        field_simp, abs_div, abs_of_pos hlam]
    exact (div_le_iff₀ hlam).mpr hclose
  have hbudget : (25 : ℝ) / (2 * Real.sqrt (n : ℝ)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (n : ℝ))).mpr
    norm_num at hroot ⊢
    linarith
  have h := hclose.trans (mul_le_mul_of_nonneg_right hbudget hlam.le)
  refine ⟨hratio, ?_, ?_⟩
  · linarith [(abs_le.mp h).1]
  · linarith [(abs_le.mp h).2]

theorem manuscript_binomial_z_eleven (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n k : ℕ) (hn : 1 ≤ n) (hcentral : |(k : ℝ) - n * p| ≤ 5 * Real.sqrt (n : ℝ)) :
    |binomialZ p n k| < 11 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := Real.sqrt_pos.mpr hn0
  have hs := (effective_binomial_parameters p hp).2.1
  have hp01 := (effective_binomial_parameters p hp).1
  have hv : 0 < p * (1 - p) := mul_pos hp01.1 (sub_pos.mpr hp01.2)
  unfold binomialZ
  simp only [Int.cast_natCast]
  rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul hn0.le, abs_div,
    abs_of_pos (mul_pos hr (Real.sqrt_pos.mpr hv))]
  apply (div_lt_iff₀ (mul_pos hr (Real.sqrt_pos.mpr hv))).mpr
  have hmul := mul_le_mul_of_nonneg_left hs hr.le
  nlinarith only [hmul, hcentral, hr]

theorem manuscript_effective_local_mass_pointwise_of_wide
    (I : PublishedNonIIDBound)
    (hwide : ∀ (p : ℝ), p ∈ Icc (2 / 5) (9 / 20) → ∀ (n : ℕ), 10 ^ 100 ≤ n →
      ∀ k : ℕ, k ≤ n → |binomialZ p n k| ≤ 11 → Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (x a b : ℝ) (hx : |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ))
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    Real.exp (-4000000000000) / Real.sqrt (n : ℝ) ≤
      (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x + a) (x + b)) := by
  let lam := accumulatedNoiseVariance P Q p n
  let r := Real.sqrt (n : ℝ)
  let K := integerWindow x (max 1 (Real.sqrt lam))
  let C := manuscriptLocalC1 / 2
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hL : 0 < lam := by change _ ≤ lam at hlam; linarith
  have hC : 0 < C := div_pos manuscriptLocalC1_pos (by norm_num)
  have hq : (2 / 5 : ℝ) ≤ 1 - p := by linarith [hp.2]
  have hε : Real.exp (-appendixA) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num [appendixA])
  have hLn : lam ≤ n := by
    have h := accumulatedNoiseVariance_le_noise_bound P Q p (Real.exp (-appendixA)) hpcc (Real.exp_pos _).le hP hQ n
    have he2 : Real.exp (-appendixA) ^ 2 ≤ 1 := by nlinarith [Real.exp_pos (-appendixA)]
    have hm := mul_le_mul_of_nonneg_left he2 hn0.le
    nlinarith only [h, hm]
  have hroot := effective_binomial_root_lower n hn
  have hlarge : 2 * ((3 : ℝ) + 1) ≤ (2 / 5) * Real.sqrt (n : ℝ) := by norm_num at hroot ⊢; linarith
  have hgeo := central_integer_window_geometry p (2 / 5) 3 lam x (by norm_num) hp.1 hq (by norm_num)
    n hn1 hLn hlarge hx
  have hK : K ⊆ Finset.range (n + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (by have h := (hgeo.2.2 k hk).1; omega)
  have hcentral (k : ℕ) (hk : k ∈ K) : |(k : ℝ) - n * p| ≤ 5 * Real.sqrt (n : ℝ) := by
    have h := (hgeo.2.2 k hk).2
    nlinarith only [h, Real.sqrt_nonneg (n : ℝ)]
  have hweights : ∀ k ∈ K, Real.exp (-100) / r ≤ binomialWeight p n k := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    exact hwide p hp n hn k hkgeo.1 (manuscript_binomial_z_eleven p hp n k hn1 (hcentral k hk)).le
  have hnoise : ∀ k ∈ K, C / Real.sqrt lam ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo ((x + a) - k) ((x + b) - k)) := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    have ht := (manuscript_conditional_variance_window P Q p hp n k hn hkgeo.1 hL (hcentral k hk)).2
    have h := manuscript_noise_block_window_mass I P Q hP hQ n k hn1 hkgeo.1 lam x a b hlam ht.1 ht.2
      (integerWindow_distance x _ hgeo.1 (by positivity) k hk) ha hb hab
    simpa only [C, div_div] using h
  have hprob := twoCluster_open_interval_lower_of_blocks P Q p hpcc n (x + a) (x + b) (by linarith) K hK
    (Real.exp (-100) / r) (C / Real.sqrt lam) (by positivity) (by positivity) hweights hnoise
  have hcard : Real.sqrt lam ≤ (K.card : ℝ) := (le_max_right 1 (Real.sqrt lam)).trans
    (integerWindow_card_lower x _ hgeo.1 (le_max_left _ _))
  have hcount := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ Real.exp (-100) / r * (C / Real.sqrt lam))
  have hid : Real.sqrt lam * (Real.exp (-100) / r * (C / Real.sqrt lam)) = Real.exp (-100) * C / r := by
    field_simp [(Real.sqrt_pos.mpr hL).ne']
  rw [hid] at hcount
  have hD := div_le_div_of_nonneg_right manuscript_local_density_budgets.2.2 hr.le
  exact hD.trans (hcount.trans (by simpa only [mul_assoc] using hprob))

theorem manuscript_effective_local_mass_of_wide
    (I : PublishedNonIIDBound)
    (hwide : ∀ (p : ℝ), p ∈ Icc (2 / 5) (9 / 20) → ∀ (n : ℕ), 10 ^ 100 ≤ n →
      ∀ k : ℕ, k ≤ n → |binomialZ p n k| ≤ 11 → Real.exp (-100) / Real.sqrt (n : ℝ) ≤ binomialWeight p n k)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (a b : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    Real.exp (-4000000000000) / Real.sqrt (n : ℝ) ≤
      sInf (Set.range (fun x : {x : ℝ // |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ)} =>
        (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x.val + a) (x.val + b)))) := by
  letI : Nonempty {x : ℝ // |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ)} :=
    ⟨⟨n * p, by simp only [sub_self, abs_zero]; positivity⟩⟩
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact manuscript_effective_local_mass_pointwise_of_wide I hwide P Q p hp hP hQ n hn hlam x.val a b x.property ha hb hab

theorem manuscript_effective_local_mass
    (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (a b : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    Real.exp (-4000000000000) / Real.sqrt (n : ℝ) ≤
      sInf (Set.range (fun x : {x : ℝ // |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ)} =>
        (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x.val + a) (x.val + b)))) := by
  exact manuscript_effective_local_mass_of_wide I manuscript_effective_binomial_wide P Q p hp hP hQ n hn hlam a b ha hb hab

theorem manuscript_effective_local_mass_pointwise
    (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (x a b : ℝ) (hx : |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ))
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    Real.exp (-4000000000000) / Real.sqrt (n : ℝ) ≤
      (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x + a) (x + b)) := by
  exact manuscript_effective_local_mass_pointwise_of_wide I manuscript_effective_binomial_wide P Q p hp hP hQ n hn hlam x a b hx ha hb hab

end BerryEsseen
