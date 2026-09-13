import BerryEsseen.LimitEnvelopes

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def generalEdgeworthShiftConstant (K h : ℝ) : ℝ :=
  phi0 * (3 * h ^ 2 / 8 + 3 * K * |h| / 2)

theorem general_edgeworthCDF_shift_remainder (n : ℕ) (hn : 1 ≤ n) (κ b x K : ℝ) (hκ : |κ| ≤ K) :
    |Real.sqrt (n : ℝ) * (edgeworthCDF n κ (x + b / (2 * Real.sqrt (n : ℝ))) - normalCDF x) -
      edgeworthEnvelope b κ x| ≤ generalEdgeworthShiftConstant K b / Real.sqrt (n : ℝ) := by
  have hK0 : 0 ≤ K := (abs_nonneg κ).trans hκ
  let s := Real.sqrt (n : ℝ)
  let a := b / (2 * s)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n by omega))
  let A := normalCDF (x + a) - normalCDF x - a * standardNormalDensity x
  let B := (1 - (x + a) ^ 2) * standardNormalDensity (x + a) - (1 - x ^ 2) * standardNormalDensity x
  have hA : |A| ≤ 3 * phi0 / 2 * a ^ 2 := gaussianCDF_first_remainder x a
  have hB : |B| ≤ 18 * phi0 * |a| := by
    simpa only [add_sub_cancel_left] using gaussian_second_polynomial_lipschitz x (x + a)
  have hcoef : |κ / (6 * s)| ≤ K / (6 * s) := by
    rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
    exact div_le_div_of_nonneg_right hκ (by positivity)
  have he : s * (edgeworthCDF n κ (x + a) - normalCDF x) - edgeworthEnvelope b κ x =
      s * (A + κ / (6 * s) * B) := by
    dsimp [A, B, edgeworthCDF, edgeworthEnvelope, a, s]
    field_simp [hs.ne']
    <;> ring
  change |s * (edgeworthCDF n κ (x + a) - normalCDF x) - edgeworthEnvelope b κ x| ≤ _
  rw [he, abs_mul, abs_of_pos hs]
  have hbnd : |A + κ / (6 * s) * B| ≤ 3 * phi0 / 2 * a ^ 2 + K / (6 * s) * (18 * phi0 * |a|) := by
    calc
      _ ≤ |A| + |κ / (6 * s)| * |B| := by simpa only [abs_mul] using abs_add_le A (κ / (6 * s) * B)
      _ ≤ _ := add_le_add hA (mul_le_mul hcoef hB (abs_nonneg _) (by positivity))
  calc
    _ ≤ s * (3 * phi0 / 2 * a ^ 2 + K / (6 * s) * (18 * phi0 * |a|)) := mul_le_mul_of_nonneg_left hbnd hs.le
    _ = _ := by
      change _ = generalEdgeworthShiftConstant K b / s
      dsimp [a, generalEdgeworthShiftConstant]
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) hs)]
      field_simp [hs.ne']
      <;> ring

theorem generalEdgeworthShiftConstant_neg (K h : ℝ) :
    generalEdgeworthShiftConstant K (-h) = generalEdgeworthShiftConstant K h := by
  simp only [generalEdgeworthShiftConstant, neg_sq, abs_neg]

theorem generalEdgeworthShiftConstant_scaled_tendsto_zero
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (K h : ℝ) :
    Tendsto (fun j => generalEdgeworthShiftConstant K h / Real.sqrt (n j : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn))

theorem general_jitter_envelopes_of_expansion (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (K : ℝ) (hκ : ∀ j, |signedThirdMoment (P j)| ≤ K)
    (h : ℝ) (hh : 0 ≤ h)
    (hU : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      edgeworthEnvelope (-h) (signedThirdMoment (P j)) x - ε ≤
        Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤
        edgeworthEnvelope h (signedThirdMoment (P j)) x + ε := by
  have hC := generalEdgeworthShiftConstant_scaled_tendsto_zero n hn K h
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff.1 hU) (ε / 2) (by linarith),
    hC.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hjU hjC
  intro x
  let s := Real.sqrt (n j : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by have := hn1 j; omega))
  have hn1j : 1 ≤ n j := hn1 j
  have hp := general_edgeworthCDF_shift_remainder (n j) hn1j (signedThirdMoment (P j)) h x K (hκ j)
  have hm := general_edgeworthCDF_shift_remainder (n j) hn1j (signedThirdMoment (P j)) (-h) x K (hκ j)
  rw [generalEdgeworthShiftConstant_neg,
    show x + -h / (2 * Real.sqrt (n j : ℝ)) = x - h / (2 * Real.sqrt (n j : ℝ)) by ring] at hm
  have hJu : |s * jitterCDFError (P j) (n j) h (x + h / (2 * s))| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjU (x + h / (2 * s))
  have hJl : |s * jitterCDFError (P j) (n j) h (x - h / (2 * s))| < ε / 2 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjU (x - h / (2 * s))
  unfold jitterCDFError at hJu hJl
  have hsp := actual_normalized_jitter_sandwich (P j) (n j) hn1j h hh x
  have hslu := mul_le_mul_of_nonneg_left hsp.2 hs.le
  have hsll := mul_le_mul_of_nonneg_left hsp.1 hs.le
  have hpU := (abs_le.1 hp).2
  have hmL := (abs_le.1 hm).1
  have hjUpper := (abs_lt.1 hJu).2
  have hjLower := (abs_lt.1 hJl).1
  change generalEdgeworthShiftConstant K h / s < ε / 2 at hjC
  change s * (edgeworthCDF (n j) (signedThirdMoment (P j)) (x + h / (2 * s)) - normalCDF x) -
    edgeworthEnvelope h (signedThirdMoment (P j)) x ≤ generalEdgeworthShiftConstant K h / s at hpU
  change -(generalEdgeworthShiftConstant K h / s) ≤
    s * (edgeworthCDF (n j) (signedThirdMoment (P j)) (x - h / (2 * s)) - normalCDF x) -
      edgeworthEnvelope (-h) (signedThirdMoment (P j)) x at hmL
  change edgeworthEnvelope (-h) (signedThirdMoment (P j)) x - ε ≤
    s * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
    s * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤ edgeworthEnvelope h (signedThirdMoment (P j)) x + ε
  constructor <;> nlinarith

theorem general_jitter_limit_envelopes_of_expansion (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (K : ℝ) (hκ : ∀ j, |signedThirdMoment (P j)| ≤ K)
    (h : ℝ) (hh : 0 ≤ h)
    (hU : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop)
    (κ : ℝ) (hκlim : Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 κ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      edgeworthEnvelope (-h) κ x - ε ≤
        Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ∧
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) x - normalCDF x) ≤
        edgeworthEnvelope h κ x + ε := by
  have hκ0 : Tendsto (fun j => phi0 / 6 * |signedThirdMoment (P j) - κ|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero] using ((hκlim.sub_const κ).abs).const_mul (phi0 / 6)
  intro ε hε
  filter_upwards [general_jitter_envelopes_of_expansion P n hn hn1 K hκ h hh hU (ε / 2) (by linarith),
    hκ0.eventually (gt_mem_nhds (by linarith : 0 < ε / 2))] with j hj hsmall
  intro x
  have hp := (abs_le.mp (edgeworthEnvelope_parameter_bound h (signedThirdMoment (P j)) κ x)).2
  have hm := (abs_le.mp (edgeworthEnvelope_parameter_bound (-h) (signedThirdMoment (P j)) κ x)).1
  have henv := hj x
  constructor <;> linarith only [hp, hm, henv.1, henv.2, hsmall]

theorem general_jitter_uniform_absolute_bound_of_expansion (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (K : ℝ) (hκ : ∀ j, |signedThirdMoment (P j)| ≤ K)
    (h : ℝ) (hh : 0 ≤ h)
    (hU : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop)
    (κ : ℝ) (hκlim : Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 κ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x : ℝ,
      Real.sqrt (n j : ℝ) * |normalizedSumCDF (P j) (n j) x - normalCDF x| ≤
        (h / 2 + |κ| / 6) * phi0 + ε := by
  intro ε hε
  filter_upwards [general_jitter_limit_envelopes_of_expansion P n hn hn1 K hκ h hh hU κ hκlim ε hε] with j hj
  intro x
  have hu := edgeworthEnvelope_abs_bound h κ x
  have hl := edgeworthEnvelope_abs_bound (-h) κ x
  rw [abs_of_nonneg hh] at hu
  rw [abs_neg, abs_of_nonneg hh] at hl
  have he := hj x
  rw [← abs_of_nonneg (Real.sqrt_nonneg (n j : ℝ)), ← abs_mul, abs_le]
  constructor
  · linarith only [he.1, (abs_le.mp hl).1]
  · linarith only [he.2, (abs_le.mp hu).2]

/-- The actual Kolmogorov error scaled by the square root of the sample size. -/
def scaledSumCDFSup (P : StandardizedLaw) (n : ℕ) : ℝ :=
  sSup (Set.range (fun x : ℝ => Real.sqrt (n : ℝ) * |normalizedSumCDF P n x - normalCDF x|))

theorem scaledSumCDFSup_eq_sqrt_mul (P : StandardizedLaw) (n : ℕ) :
    scaledSumCDFSup P n = Real.sqrt (n : ℝ) *
      sSup (Set.range (fun x : ℝ => |normalizedSumCDF P n x - normalCDF x|)) := by
  symm
  exact Real.smul_iSup_of_nonneg (Real.sqrt_nonneg (n : ℝ))
    (fun x : ℝ => |normalizedSumCDF P n x - normalCDF x|)

theorem scaledSumCDFSup_nonneg (P : StandardizedLaw) (n : ℕ) :
    0 ≤ scaledSumCDFSup P n := by
  have hb : BddAbove (Set.range (fun x : ℝ => Real.sqrt (n : ℝ) * |normalizedSumCDF P n x - normalCDF x|)) := by
    refine ⟨Real.sqrt (n : ℝ), ?_⟩
    rintro y ⟨x, rfl⟩
    have hN0 : 0 ≤ normalCDF x := by simpa only [cdf_eq_real] using cdf_nonneg (gaussianReal 0 1) x
    have hN1 : normalCDF x ≤ 1 := by simpa only [cdf_eq_real] using cdf_le_one (gaussianReal 0 1) x
    have hP0 : 0 ≤ normalizedSumCDF P n x := cdf_nonneg _ _
    have hP1 : normalizedSumCDF P n x ≤ 1 := cdf_le_one _ _
    have hab : |normalizedSumCDF P n x - normalCDF x| ≤ 1 :=
      abs_le.mpr ⟨by linarith only [hP0, hN1], by linarith only [hP1, hN0]⟩
    exact (mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg _)).trans_eq (mul_one _)
  exact (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)).trans
    (le_csSup hb (show Real.sqrt (n : ℝ) * |normalizedSumCDF P n 0 - normalCDF 0| ∈ Set.range _ from ⟨0, rfl⟩))

theorem general_jitter_limsup_of_expansion (P : ℕ → StandardizedLaw)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn1 : ∀ j, 1 ≤ n j)
    (K : ℝ) (hκ : ∀ j, |signedThirdMoment (P j)| ≤ K)
    (h : ℝ) (hh : 0 ≤ h)
    (hU : TendstoUniformly (fun j x => Real.sqrt (n j : ℝ) * jitterCDFError (P j) (n j) h x)
      (fun _ => 0) atTop)
    (κ : ℝ) (hκlim : Tendsto (fun j => signedThirdMoment (P j)) atTop (𝓝 κ)) :
    atTop.limsup (fun j => scaledSumCDFSup (P j) (n j)) ≤ (|κ| + 3 * h) * phi0 / 6 := by
  have hlow : IsCoboundedUnder (· ≤ ·) atTop (fun j => scaledSumCDFSup (P j) (n j)) :=
    isCoboundedUnder_le_of_le atTop (fun j => scaledSumCDFSup_nonneg (P j) (n j))
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le hlow
  filter_upwards [general_jitter_uniform_absolute_bound_of_expansion P n hn hn1 K hκ h hh hU κ hκlim ε hε] with j hj
  unfold scaledSumCDFSup
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨x, rfl⟩
  convert hj x using 1 <;> ring

end BerryEsseen
