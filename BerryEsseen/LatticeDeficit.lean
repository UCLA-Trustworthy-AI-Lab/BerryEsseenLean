import BerryEsseen.EffectiveIntervals
import BerryEsseen.SmallVarianceNeighborhood

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def latticeMomentDeficit (P : StandardizedLaw) (h : ℝ) : ℝ :=
  cStar * thirdMoment P - |signedThirdMoment P| - 3 * h

def latticeDeficitPolynomial (h x : ℝ) : ℝ :=
  cStar * |x| ^ 3 - x ^ 3 - 3 * h * x ^ 2

theorem cStar_effective_bounds : 123 / 20 < cStar ∧ cStar < 7 := by
  unfold cStar
  constructor <;> nlinarith [sqrt10_sq, sqrt10_bounds.1, sqrt10_bounds.2]

theorem manuscript_effective_lattice_span_enclosure (P : StandardizedLaw) (h δ : ℝ)
    (hβ : thirdMoment P ≤ 2) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    : (cStar - 1 - δ) / 3 ≤ h ∧ h ≤ 2 * cStar / 3 := by
  have hκ := signedThirdMoment_abs_le P
  have hβ1 := thirdMoment_ge_one P
  have hc := cStar_effective_bounds
  have hl := mul_nonneg (by linarith [hc.1] : 0 ≤ cStar - 1) (sub_nonneg.mpr hβ1)
  have hu := mul_le_mul_of_nonneg_left hβ (by linarith [hc.1] : 0 ≤ cStar)
  dsimp only [latticeMomentDeficit, mem_Icc] at hD
  constructor <;> nlinarith [hD.1, hD.2, abs_nonneg (signedThirdMoment P)]

theorem effective_lattice_span_bounds (P : StandardizedLaw) (h δ : ℝ)
    (hβ : thirdMoment P ≤ 2) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) : 17 / 10 < h ∧ h < 5 := by
  have he := manuscript_effective_lattice_span_enclosure P h δ hβ hD
  have hc := cStar_effective_bounds
  constructor <;> linarith [he.1, he.2, hc.1, hc.2]

theorem lattice_bracket_quadratic_nonneg (a b : ℝ) :
    0 ≤ (cStar - 2) * a ^ 2 + (cStar - 4) * b ^ 2 - 6 * a * b := by
  have hc : 0 < cStar - 2 := by linarith [cStar_effective_bounds.1]
  have hid : (cStar - 2) *
      ((cStar - 2) * a ^ 2 + (cStar - 4) * b ^ 2 - 6 * a * b) =
        ((cStar - 2) * a - 3 * b) ^ 2 := by
    unfold cStar
    nlinarith only [sqrt10_sq]
  exact nonneg_of_mul_nonneg_right (hid.symm ▸ sq_nonneg _) hc

theorem lattice_quadratic_growth (C h a u : ℝ) (hC : 5 ≤ C) (hh : 0 < h)
    (ha : 0 ≤ a) (hu : a + h ≤ u) :
    C * u ^ 2 - 3 * h * u - (C * a ^ 2 - 3 * h * a) ≥ h * u := by
  have hw : h ≤ u - a := by linarith
  have hp := mul_nonneg (sub_nonneg.mpr hC) (show 0 ≤ u ^ 2 - a ^ 2 by nlinarith)
  have h1 := mul_nonneg ha (show 0 ≤ 10 * (u - a) - h by linarith)
  have h2 := mul_nonneg (show 0 ≤ u - a by linarith) (show 0 ≤ 5 * (u - a) - 4 * h by linarith)
  nlinarith only [hp, h1, h2]

theorem lattice_deficit_pointwise (a b h x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = h)
    (hx : x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) :
    ((cStar - 1) * b ^ 2 - 3 * h * b) * x +
      h * ({-a, b}ᶜ : Set ℝ).indicator (fun y => y ^ 2) x ≤ latticeDeficitPolynomial h x := by
  have hh : 0 < h := by linarith
  have hc := cStar_effective_bounds
  have hK := lattice_bracket_quadratic_nonneg a b
  have hbase : 0 ≤ (cStar + 1) * a ^ 2 - 3 * h * a +
      ((cStar - 1) * b ^ 2 - 3 * h * b) := by rw [← hab]; nlinarith only [hK]
  rcases hx with hx | hx | hx | hx
  · subst x
    have hs : -a ∉ ({-a, b}ᶜ : Set ℝ) := by simp
    rw [Set.indicator_of_notMem hs, mul_zero, add_zero, latticeDeficitPolynomial,
      abs_neg, abs_of_pos ha]
    have hp := mul_nonneg ha.le hbase
    nlinarith only [hp]
  · subst x
    have hs : b ∉ ({-a, b}ᶜ : Set ℝ) := by simp
    rw [Set.indicator_of_notMem hs, mul_zero, add_zero, latticeDeficitPolynomial, abs_of_pos hb]
    exact le_of_eq (by ring)
  · have hs : x ∈ ({-a, b}ᶜ : Set ℝ) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff]
      push_neg
      constructor <;> linarith
    rw [Set.indicator_of_mem hs, latticeDeficitPolynomial, abs_of_neg (show x < 0 by linarith)]
    have hg := lattice_quadratic_growth (cStar + 1) h a (-x) (by linarith) hh ha.le (by linarith)
    have hp := mul_nonneg (show 0 ≤ -x by linarith) hbase
    have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ -x by linarith)
    nlinarith only [hp, hg']
  · have hs : x ∈ ({-a, b}ᶜ : Set ℝ) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff]
      push_neg
      constructor <;> linarith
    rw [Set.indicator_of_mem hs, latticeDeficitPolynomial, abs_of_pos (show 0 < x by linarith)]
    have hg := lattice_quadratic_growth (cStar - 1) h b x (by linarith) hh hb.le hx
    have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ x by linarith)
    nlinarith only [hg']

theorem latticeDeficitPolynomial_integrable (P : StandardizedLaw) (h : ℝ) :
    Integrable (latticeDeficitPolynomial h) P.measure :=
  ((P.third_integrable.const_mul cStar).sub (signedThirdMoment_integrable P)).sub
    (P.second_integrable.const_mul (3 * h))

theorem latticeDeficitPolynomial_integral (P : StandardizedLaw) (h : ℝ) :
    (∫ x, latticeDeficitPolynomial h x ∂P.measure) =
      cStar * thirdMoment P - signedThirdMoment P - 3 * h := by
  unfold latticeDeficitPolynomial
  have hi : Integrable (fun x : ℝ => cStar * |x| ^ 3 - x ^ 3) P.measure :=
    (P.third_integrable.const_mul cStar).sub (signedThirdMoment_integrable P)
  have he := integral_sub hi (P.second_integrable.const_mul (3 * h))
  simp only [Pi.sub_apply] at he
  rw [he]
  have he' := integral_sub (P.third_integrable.const_mul cStar) (signedThirdMoment_integrable P)
  simp only [Pi.sub_apply] at he'
  rw [he', integral_const_mul, integral_const_mul, P.second_one, mul_one]
  rfl

theorem lattice_outside_second_bound (P : StandardizedLaw) (a b h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = h) (hκ : 0 ≤ signedThirdMoment P)
    (hx : ∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) :
    (∫ x, ({-a, b}ᶜ : Set ℝ).indicator (fun y => y ^ 2) x ∂P.measure) ≤ latticeMomentDeficit P h / h := by
  have hh : 0 < h := by linarith
  have hset : MeasurableSet ({-a, b}ᶜ : Set ℝ) := ((measurableSet_singleton b).insert (-a)).compl
  have hi := P.second_integrable.indicator hset
  have hbound := integral_mono_ae
    ((P.first_integrable.const_mul ((cStar - 1) * b ^ 2 - 3 * h * b)).add (hi.const_mul h))
    (latticeDeficitPolynomial_integrable P h)
    (hx.mono (fun x hx => lattice_deficit_pointwise a b h x ha hb hab hx))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (P.first_integrable.const_mul _) (hi.const_mul h),
    integral_const_mul, integral_const_mul, P.mean_zero, mul_zero, zero_add,
    latticeDeficitPolynomial_integral] at hbound
  rw [latticeMomentDeficit, abs_of_nonneg hκ]
  apply (le_div_iff₀ hh).mpr
  nlinarith only [hbound]

theorem thirdMoment_ge_lattice_gap (P : StandardizedLaw) (h : ℝ)
    (hx : ∀ᵐ x ∂P.measure, x ≠ 0 → h ≤ |x|) : h ≤ thirdMoment P := by
  have hp : ∀ᵐ x ∂P.measure, h * x ^ 2 ≤ |x| ^ 3 := by
    filter_upwards [hx] with x hx
    by_cases hz : x = 0
    · simp [hz]
    · calc
        h * x ^ 2 = h * |x| ^ 2 := by rw [sq_abs]
        _ ≤ |x| * |x| ^ 2 := mul_le_mul_of_nonneg_right (hx hz) (sq_nonneg _)
        _ = |x| ^ 3 := by ring
  have hi := integral_mono_ae (P.second_integrable.const_mul h) P.third_integrable hp
  rw [integral_const_mul, P.second_one, mul_one] at hi
  exact hi

theorem translated_lattice_nonzero_gap (a h : ℝ) (hh : 0 < h)
    (hzero : ∃ j : ℤ, a + (j : ℝ) * h = 0) (x : ℝ)
    (hx : ∃ k : ℤ, x = a + (k : ℝ) * h) (hxn : x ≠ 0) : h ≤ |x| := by
  obtain ⟨j, hj⟩ := hzero
  obtain ⟨k, hk⟩ := hx
  have hkj : k ≠ j := by intro he; subst k; exact hxn (hk.trans hj)
  rcases lt_or_gt_of_ne hkj with hlt | hgt
  · have hi : (k : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : k + 1 ≤ j)
    have hm := mul_le_mul_of_nonneg_right hi hh.le
    have hs : x ≤ -h := by nlinarith only [hm, hk, hj]
    rw [abs_of_neg (by linarith : x < 0)]
    linarith
  · have hi : (j : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : j + 1 ≤ k)
    have hm := mul_le_mul_of_nonneg_right hi hh.le
    have hs : h ≤ x := by nlinarith only [hm, hk, hj]
    exact hs.trans (le_abs_self x)

theorem effective_lattice_translate_avoids_zero (P : StandardizedLaw) (h δ a : ℝ)
    (hh : 0 < h) (hβ : thirdMoment P ≤ 2)
    (hD : latticeMomentDeficit P h ∈ Icc 0 δ) (hδ : δ ≤ 1 / (10 : ℝ) ^ 6)
    (hlat : ∀ x ∈ P.measure.support, ∃ k : ℤ, x = a + (k : ℝ) * h) :
    ¬ ∃ j : ℤ, a + (j : ℝ) * h = 0 := by
  intro hz
  have hg : h ≤ thirdMoment P := thirdMoment_ge_lattice_gap P h (by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact translated_lattice_nonzero_gap a h hh hz x (hlat x hx))
  have hb := effective_lattice_span_bounds P h δ hβ hD hδ
  have hκ := signedThirdMoment_abs_le P
  have hc := cStar_effective_bounds
  have hm := mul_nonneg (show 0 ≤ cStar - 1 by linarith) (sub_nonneg.mpr hg)
  have hlarge := mul_lt_mul_of_pos_right (show (2 : ℝ) < cStar - 4 by linarith) hh
  have hdu := hD.2
  unfold latticeMomentDeficit at hdu
  nlinarith only [hm, hlarge, hκ, hdu, hδ, hb.1]

theorem translated_lattice_bracketing (a₀ h : ℝ) (hh : 0 < h)
    (hzero : ¬ ∃ j : ℤ, a₀ + (j : ℝ) * h = 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧
      ∀ x : ℝ, (∃ k : ℤ, x = a₀ + (k : ℝ) * h) →
        x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x := by
  let j : ℤ := ⌊-a₀ / h⌋
  let l := a₀ + (j : ℝ) * h
  have hl : l ≤ 0 := by
    have hf := mul_le_mul_of_nonneg_right (Int.floor_le (-a₀ / h)) hh.le
    rw [div_mul_cancel₀ _ hh.ne'] at hf
    dsimp only [l, j]
    linarith only [hf]
  have hln : l ≠ 0 := by intro he; exact hzero ⟨j, he⟩
  have hlt : l < 0 := lt_of_le_of_ne hl hln
  have hu : 0 < l + h := by
    have hf := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (-a₀ / h)) hh
    rw [div_mul_cancel₀ _ hh.ne'] at hf
    dsimp only [l, j]
    nlinarith only [hf]
  refine ⟨-l, l + h, by linarith, hu, by ring, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := hx
  by_cases he : k = j
  · left
    simpa only [neg_neg, he] using hk
  by_cases he' : k = j + 1
  · right; left
    rw [hk, he']
    dsimp only [l]
    push_cast
    ring
  have hcases : k ≤ j - 1 ∨ j + 2 ≤ k := by omega
  rcases hcases with hlo | hhi
  · right; right; left
    have hr : (k : ℝ) ≤ j - 1 := by exact_mod_cast hlo
    have hm := mul_le_mul_of_nonneg_right hr hh.le
    dsimp only [l]
    nlinarith only [hm, hk]
  · right; right; right
    have hr : (j : ℝ) + 2 ≤ k := by exact_mod_cast hhi
    have hm := mul_le_mul_of_nonneg_right hr hh.le
    dsimp only [l]
    nlinarith only [hm, hk]

theorem effective_lattice_outside_second (P : StandardizedLaw) (h δ : ℝ)
    (hlat : IsLatticeSpan P.measure h) (hβ : thirdMoment P ≤ 2)
    (hκ : 0 ≤ signedThirdMoment P) (hD : latticeMomentDeficit P h ∈ Icc 0 δ)
    (hδ : δ ≤ 1 / (10 : ℝ) ^ 6) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = h ∧
      (∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x) ∧
      (∫ x, ({-a, b}ᶜ : Set ℝ).indicator (fun y => y ^ 2) x ∂P.measure) ≤ δ := by
  obtain ⟨hh, a₀, ha₀⟩ := hlat
  have hz := effective_lattice_translate_avoids_zero P h δ a₀ hh hβ hD hδ ha₀
  obtain ⟨a, b, ha, hb, hab, hgeom⟩ := translated_lattice_bracketing a₀ h hh hz
  have hx : ∀ᵐ x ∂P.measure, x = -a ∨ x = b ∨ x ≤ -a - h ∨ b + h ≤ x := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact hgeom x (ha₀ x hx)
  refine ⟨a, b, ha, hb, hab, hx, ?_⟩
  have hbound := lattice_outside_second_bound P a b h ha hb hab hκ hx
  have hd0 : 0 ≤ δ := hD.1.trans hD.2
  have hh1 : 1 ≤ h := by linarith [(effective_lattice_span_bounds P h δ hβ hD hδ).1]
  apply hbound.trans
  apply (div_le_iff₀ hh).mpr
  exact hD.2.trans (by nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hh1)])

end BerryEsseen
