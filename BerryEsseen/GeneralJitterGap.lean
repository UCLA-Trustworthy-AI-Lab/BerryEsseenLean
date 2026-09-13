import BerryEsseen.GeneralJitterEnvelopes
import BerryEsseen.GeneralBinomialEnvelopeTails
import BerryEsseen.EffectiveJitterGap

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def absoluteEdgeworthEnvelope (h κ z : ℝ) : ℝ :=
  h / 2 * standardNormalDensity z + |κ| / 6 * |(1 - z ^ 2) * standardNormalDensity z|

theorem absoluteEdgeworthEnvelope_bounds (h κ z : ℝ) (hh : 0 ≤ h) :
    |edgeworthEnvelope h κ z| ≤ absoluteEdgeworthEnvelope h κ z ∧
    |edgeworthEnvelope (-h) κ z| ≤ absoluteEdgeworthEnvelope h κ z := by
  have hpos := (standardNormalDensity_pos z).le
  have hA := abs_add_le (h / 2 * standardNormalDensity z)
    (κ / 6 * ((1 - z ^ 2) * standardNormalDensity z))
  have hB := abs_add_le (-(h / 2 * standardNormalDensity z))
    (κ / 6 * ((1 - z ^ 2) * standardNormalDensity z))
  have hmain : 0 ≤ h / 2 * standardNormalDensity z := by positivity
  norm_num only [abs_mul, abs_div, abs_of_nonneg hh, abs_of_nonneg hpos, abs_neg] at hA hB
  constructor
  · have he : edgeworthEnvelope h κ z = h / 2 * standardNormalDensity z +
        κ / 6 * ((1 - z ^ 2) * standardNormalDensity z) := by unfold edgeworthEnvelope; ring
    rw [he]
    simpa only [absoluteEdgeworthEnvelope, abs_mul, abs_of_nonneg hpos] using hA
  · have he : edgeworthEnvelope (-h) κ z = -(h / 2 * standardNormalDensity z) +
        κ / 6 * ((1 - z ^ 2) * standardNormalDensity z) := by unfold edgeworthEnvelope; ring
    rw [he]
    simpa only [absoluteEdgeworthEnvelope, abs_mul, abs_of_nonneg hpos] using hB

theorem absoluteEdgeworthEnvelope_global_bound (h κ z : ℝ) (hh : 0 ≤ h) :
    absoluteEdgeworthEnvelope h κ z ≤ (h / 2 + |κ| / 6) * phi0 := by
  have h1 := mul_le_mul_of_nonneg_left (standardNormalDensity_le_phi0 z) (by positivity : 0 ≤ h / 2)
  have hgauss : |(1 - z ^ 2) * standardNormalDensity z| ≤ phi0 := by
    simpa only [show 1 - z ^ 2 = -(z ^ 2 - 1) by ring, neg_mul, abs_neg] using gaussian_second_derivative_bound z
  have h2 := mul_le_mul_of_nonneg_left hgauss (by positivity : 0 ≤ |κ| / 6)
  dsimp only [absoluteEdgeworthEnvelope]
  nlinarith only [h1, h2]

theorem absoluteEdgeworthEnvelope_rational_bound (h κ z : ℝ) (hh : 0 ≤ h) :
    absoluteEdgeworthEnvelope h κ z ≤ 3 * (h + |κ|) / (1 + z ^ 2) := by
  have ha : |1 - z ^ 2| ≤ 1 + z ^ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg z], by nlinarith [sq_nonneg z]⟩
  have hφ := (standardNormalDensity_pos z).le
  have hq : absoluteEdgeworthEnvelope h κ z ≤
      (h + |κ|) * (standardNormalDensity z * (4 + z ^ 2) / 3) := by
    have h2 := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ |κ| / 6 * standardNormalDensity z)
    have hhz := mul_nonneg hh (sq_nonneg z)
    have hkz := mul_nonneg (abs_nonneg κ) (sq_nonneg z)
    have hc : h / 2 + |κ| / 6 * (1 + z ^ 2) ≤ (h + |κ|) * (4 + z ^ 2) / 3 := by nlinarith [abs_nonneg κ]
    have ht := mul_le_mul_of_nonneg_right hc hφ
    dsimp only [absoluteEdgeworthEnvelope]
    rw [abs_mul, abs_of_nonneg hφ]
    nlinarith only [h2, ht]
  exact hq.trans (by
    convert mul_le_mul_of_nonneg_left (gaussian_quadratic_rational_bound z) (by positivity : 0 ≤ h + |κ|) using 1 <;> ring)

theorem absoluteEdgeworthEnvelope_uniform_tail (h κ : ℝ) (hh : 0 ≤ h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R ≥ 0, ∀ z : ℝ, R ≤ |z| → absoluteEdgeworthEnvelope h κ z < ε := by
  let C := 3 * (h + |κ|)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C / ε + 1, by positivity, ?_⟩
  intro z hz
  have hz1 : 1 ≤ |z| := by linarith [div_nonneg hC hε.le]
  have hz2 : |z| ≤ z ^ 2 := by nlinarith [mul_nonneg (abs_nonneg z) (sub_nonneg.mpr hz1), sq_abs z]
  have hmul := (div_le_iff₀ hε).mp (show C / ε ≤ |z| - 1 by linarith)
  have hb : C / (1 + z ^ 2) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < 1 + z ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hz2 hε.le]
  exact (absoluteEdgeworthEnvelope_rational_bound h κ z hh).trans_lt hb

theorem edgeworthEnvelope_both_parameter_bound (h h' κ κ' z : ℝ) :
    |edgeworthEnvelope h κ z - edgeworthEnvelope h' κ' z| ≤
      phi0 * (|h - h'| / 2 + |κ - κ'| / 6) := by
  have hκb := edgeworthEnvelope_parameter_bound h κ κ' z
  have hh : |edgeworthEnvelope h κ' z - edgeworthEnvelope h' κ' z| ≤ phi0 * |h - h'| / 2 := by
    have he : edgeworthEnvelope h κ' z - edgeworthEnvelope h' κ' z =
      (h - h') / 2 * standardNormalDensity z := by unfold edgeworthEnvelope; ring
    rw [he, abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos (standardNormalDensity_pos z)]
    convert mul_le_mul_of_nonneg_left (standardNormalDensity_le_phi0 z) (by positivity : 0 ≤ |h - h'| / 2) using 1 <;> ring
  have htri := abs_add_le (edgeworthEnvelope h κ z - edgeworthEnvelope h κ' z)
    (edgeworthEnvelope h κ' z - edgeworthEnvelope h' κ' z)
  rw [sub_add_sub_cancel] at htri
  nlinarith only [htri, hκb, hh]

/-- A generic analytic strict-gap principle. The CDF-specific hypotheses are
the actual two shifted-jitter errors and their local improvements. -/
theorem strict_gap_of_jitter_envelopes
    (F Jplus Jminus : ℕ → ℝ → ℝ) (h κ : ℝ) (hh : 0 < h)
    (hu : TendstoUniformly (fun j z => Jplus j z - edgeworthEnvelope h κ z) (fun _ => 0) atTop)
    (hl : TendstoUniformly (fun j z => Jminus j z - edgeworthEnvelope (-h) κ z) (fun _ => 0) atTop)
    (horder : ∀ᶠ j in atTop, ∀ z, Jminus j z ≤ F j z ∧ F j z ≤ Jplus j z)
    (hgap : ∀ R ≥ 0, ∃ D > 0, ∀ᶠ j in atTop, ∀ z, |z| ≤ R →
      Jminus j z + D ≤ F j z ∧ F j z ≤ Jplus j z - D) :
    ∃ δ > 0, ∀ᶠ j in atTop, ∀ z, |F j z| ≤ (h / 2 + |κ| / 6) * phi0 - δ := by
  let L := (h / 2 + |κ| / 6) * phi0
  have hL : 0 < L := mul_pos (by positivity) phi0_pos
  obtain ⟨R, hR, htail⟩ := absoluteEdgeworthEnvelope_uniform_tail h κ hh.le (L / 2) (by positivity)
  obtain ⟨D, hD, hlocal⟩ := hgap R hR
  let δ := min (D / 2) (L / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδD : δ ≤ D / 2 := min_le_left _ _
  have hδL : δ ≤ L / 4 := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [Metric.tendstoUniformly_iff.1 hu δ hδ,
    Metric.tendstoUniformly_iff.1 hl δ hδ, horder, hlocal] with j hju hjl hjo hjg
  intro z
  have hU : |Jplus j z - edgeworthEnvelope h κ z| < δ := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hju z
  have hLo : |Jminus j z - edgeworthEnvelope (-h) κ z| < δ := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hjl z
  have hab := absoluteEdgeworthEnvelope_bounds h κ z hh.le
  have hupp := (abs_le.mp hab.1).2
  have hlow := (abs_le.mp hab.2).1
  change |F j z| ≤ L - δ
  rw [abs_le]
  by_cases hz : |z| ≤ R
  · have hg := hjg z hz
    have hb := absoluteEdgeworthEnvelope_global_bound h κ z hh.le
    change absoluteEdgeworthEnvelope h κ z ≤ L at hb
    constructor <;> linarith [(abs_lt.mp hU).2, (abs_lt.mp hLo).1, hg.1, hg.2]
  · have ht := htail z (le_of_not_ge hz)
    have ho := hjo z
    constructor <;> linarith [(abs_lt.mp hU).2, (abs_lt.mp hLo).1, ho.1, ho.2]

end BerryEsseen
