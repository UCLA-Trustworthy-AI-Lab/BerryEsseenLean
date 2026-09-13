import BerryEsseen.SupportLimit

/-! The two separate uniform first-order estimates used at the start of
the manuscript's Lemma 5.3. Their constants depend only on the common
support bound. Neither estimate uses a limit of the complete Gaussian H. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def manuscriptContactFirstConstant (L : ℝ) : ℝ :=
  3 * phi0 / 2 * (L ^ 2 + 1) + (L ^ 3 + 3 * L ^ 2 + 3 * L + 5)

def manuscriptNormalFirstConstant (L : ℝ) : ℝ :=
  3 * phi0 / 2 * L ^ 2 + 6 * phi0

theorem manuscript_contact_polynomial_bound (β M v L : ℝ)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 2) (hM : |M| ≤ 1) (hv : |v| ≤ L) :
    abs (|v| ^ 3 - β - 3 * M * v - 3 / 2 * β * (v ^ 2 - 1)) ≤
      L ^ 3 + 3 * L ^ 2 + 3 * L + 5 := by
  have hL : 0 ≤ L := (abs_nonneg v).trans hv
  have hv2 : |v ^ 2 - 1| ≤ L ^ 2 + 1 := by
    calc
      _ ≤ |v ^ 2| + |(1 : ℝ)| := abs_sub _ _
      _ = |v| ^ 2 + 1 := by rw [abs_pow, abs_one]
      _ ≤ _ := by gcongr
  calc
    _ ≤ (abs (|v| ^ 3 - β) + |3 * M * v|) + |3 / 2 * β * (v ^ 2 - 1)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (|v| ^ 3 + β + 3 * |M| * |v|) + (3 / 2) * β * |v ^ 2 - 1| := by
      simp only [abs_mul, abs_div, abs_of_nonneg hβ0,
        abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h := abs_sub (|v| ^ 3) β
      rw [abs_of_nonneg (by positivity : 0 ≤ |v| ^ 3), abs_of_nonneg hβ0] at h
      linarith
    _ ≤ (L ^ 3 + 2 + 3 * 1 * L) + (3 / 2) * 2 * (L ^ 2 + 1) := by gcongr
    _ = _ := by ring

/-- The first displayed uniform O(1/n) in Lemma 5.3: the actual contact
equation, uniformly over every point of the bounded support. -/
theorem manuscript_contact_first_order (H : ClassicalBerryEsseenBounds)
    (P : StandardizedLaw) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1)) (v L : ℝ)
    (hvsupp : v ∈ P.measure.support) (hvL : |v| ≤ L) :
    |cdf (iidSumLaw P.measure n) (t - v) - cdf (iidSumLaw P.measure (n + 1)) t +
      standardNormalDensity (t / Real.sqrt (n + 1 : ℝ)) * v / Real.sqrt (n + 1 : ℝ)| ≤
        manuscriptContactFirstConstant L / (n + 1 : ℝ) := by
  have hφ : 0 < phi0 := phi0_pos
  let s := Real.sqrt (n + 1 : ℝ)
  let z := t / s
  let β := thirdMoment P
  let M := signedSecondMoment P
  let R := signedRatio P n t
  have hs : 0 < s := by dsimp [s]; positivity
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hs2 : s ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hR0 : 0 ≤ R := by dsimp [R]; rw [hattain]; exact cE_pos.le.trans hv.le
  have hR1 : R ≤ 1 := by
    have h := (extremalConstant_bounds H (n + 1) (by omega)).1
    dsimp [R]; rw [hattain]; linarith
  have hβ0 : 0 ≤ β := (thirdMoment_pos P).le
  have hβ2 : β ≤ 2 := by
    have h := extremizer_thirdMoment_cutoff H P n t (by rw [hattain]; exact hv)
    dsimp [β]; linarith [momentCutoff_bounds.2]
  have hL : 0 ≤ L := (abs_nonneg v).trans hvL
  have hv2 : |v ^ 2 - 1| ≤ L ^ 2 + 1 := by
    calc
      _ ≤ |v ^ 2| + |(1 : ℝ)| := abs_sub _ _
      _ = |v| ^ 2 + 1 := by rw [abs_pow, abs_one]
      _ ≤ _ := by gcongr
  have hpoly := manuscript_contact_polynomial_bound β M v L hβ0 hβ2
    (signedSecondMoment_abs_le_one P) hvL
  have hcoef : |R / s| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hR0 hs.le)]
    exact (div_le_iff₀ hs).2 (by linarith)
  have hzbound : |z * standardNormalDensity z / 2| ≤ 3 * phi0 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (gaussian_first_monomial_bound z) (by norm_num)
  have hrem : |-(z * standardNormalDensity z / 2) * (v ^ 2 - 1) +
      R / s * (|v| ^ 3 - β - 3 * M * v - 3 / 2 * β * (v ^ 2 - 1))| ≤
        manuscriptContactFirstConstant L := by
    calc
      _ ≤ |-(z * standardNormalDensity z / 2) * (v ^ 2 - 1)| +
          |R / s * (|v| ^ 3 - β - 3 * M * v - 3 / 2 * β * (v ^ 2 - 1))| := abs_add_le _ _
      _ = |z * standardNormalDensity z / 2| * |v ^ 2 - 1| +
          |R / s| * abs (|v| ^ 3 - β - 3 * M * v - 3 / 2 * β * (v ^ 2 - 1)) := by
        rw [abs_mul, abs_neg, abs_mul]
      _ ≤ (3 * phi0 / 2) * (L ^ 2 + 1) + 1 * (L ^ 3 + 3 * L ^ 2 + 3 * L + 5) := by
        exact add_le_add (mul_le_mul hzbound hv2 (abs_nonneg _) (by positivity))
          (mul_le_mul hcoef hpoly (abs_nonneg _) (by norm_num))
      _ = _ := by simp only [manuscriptContactFirstConstant, one_mul]
  have hc := influence_contact_equation H P n t hattain hR0 v hvsupp
  change (n + 1 : ℝ) * (cdf (iidSumLaw P.measure n) (t - v) -
      cdf (iidSumLaw P.measure (n + 1)) t) = -s * standardNormalDensity z * v -
      z * standardNormalDensity z / 2 * (v ^ 2 - 1) +
      R / s * (|v| ^ 3 - β - 3 * M * v - 3 / 2 * β * (v ^ 2 - 1)) at hc
  have he : (n + 1 : ℝ) * (cdf (iidSumLaw P.measure n) (t - v) -
      cdf (iidSumLaw P.measure (n + 1)) t + standardNormalDensity z * v / s) =
      -(z * standardNormalDensity z / 2) * (v ^ 2 - 1) +
      R / s * (|v| ^ 3 - β - 3 * M * v - 3 / 2 * β * (v ^ 2 - 1)) := by
    rw [mul_add, hc, ← hs2]
    field_simp [hs.ne']
    <;> ring
  rw [← he, abs_mul, abs_of_pos hN] at hrem
  exact (le_div_iff₀ hN).2 (by simpa only [mul_comm] using hrem)

theorem manuscript_gaussian_scale_first_order (u d : ℝ) (hd : d ∈ Icc 0 (1 / 2)) :
    |normalCDF (u / Real.sqrt (1 - d)) - normalCDF u| ≤ 6 * phi0 * d := by
  have h := gaussian_scale_remainder u d hd
  have hm : |d * u * standardNormalDensity u / 2| ≤ d * (3 * phi0) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc,
      abs_mul, abs_of_nonneg hd.1]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (gaussian_first_monomial_bound u) hd.1) (by norm_num)
  have ht := (abs_add_le
    (normalCDF (u / Real.sqrt (1 - d)) - normalCDF u - d * u * standardNormalDensity u / 2)
    (d * u * standardNormalDensity u / 2)).trans (add_le_add h hm)
  rw [sub_add_cancel] at ht
  have hd2 : d ^ 2 ≤ d / 2 := by nlinarith [hd.1, hd.2]
  have hp := mul_le_mul_of_nonneg_left hd2 phi0_pos.le
  nlinarith

/-- The second displayed uniform O(1/n): ordinary first-order translation
Taylor and first-order scale Taylor, uniformly in the normal argument z. -/
theorem manuscript_normal_first_order (n : ℕ) (hn : 1 ≤ n) (z v L : ℝ)
    (hv : |v| ≤ L) :
    |normalCDF ((z - v / Real.sqrt (n + 1 : ℝ)) /
        Real.sqrt (1 - 1 / Real.sqrt (n + 1 : ℝ) ^ 2)) - normalCDF z +
      standardNormalDensity z * v / Real.sqrt (n + 1 : ℝ)| ≤
        manuscriptNormalFirstConstant L / (n + 1 : ℝ) := by
  let s := Real.sqrt (n + 1 : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  have hs2low : 2 ≤ s ^ 2 := by rw [hs2]; exact_mod_cast (by omega : 2 ≤ n + 1)
  have hd : (1 / s ^ 2 : ℝ) ∈ Icc 0 (1 / 2) :=
    ⟨by positivity, (div_le_iff₀ (sq_pos_of_pos hs)).2 (by linarith)⟩
  have hscale := manuscript_gaussian_scale_first_order (z - v / s) (1 / s ^ 2) hd
  have htrans := gaussianCDF_first_remainder z (-v / s)
  have he : normalCDF ((z - v / s) / Real.sqrt (1 - 1 / s ^ 2)) - normalCDF z +
      standardNormalDensity z * v / s =
      (normalCDF ((z - v / s) / Real.sqrt (1 - 1 / s ^ 2)) - normalCDF (z - v / s)) +
      (normalCDF (z + -v / s) - normalCDF z - (-v / s) * standardNormalDensity z) := by
    rw [show z + -v / s = z - v / s by ring]
    ring
  have hb := (abs_add_le _ _).trans (add_le_add hscale htrans)
  rw [← he] at hb
  have hφ : 0 < phi0 := phi0_pos
  have hv2 : v ^ 2 ≤ L ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
  have htrans' : 3 * phi0 / 2 * (-v / s) ^ 2 ≤ 3 * phi0 / 2 * L ^ 2 / s ^ 2 := by
    rw [div_pow, neg_sq]
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hv2 (sq_nonneg s)) (by positivity : 0 ≤ 3 * phi0 / 2)) |>.trans_eq (by ring)
  apply hb.trans
  calc
    _ ≤ 6 * phi0 * (1 / s ^ 2) + 3 * phi0 / 2 * L ^ 2 / s ^ 2 := add_le_add le_rfl htrans'
    _ = manuscriptNormalFirstConstant L / (n + 1 : ℝ) := by
      rw [← hs2]
      unfold manuscriptNormalFirstConstant
      ring

end BerryEsseen
