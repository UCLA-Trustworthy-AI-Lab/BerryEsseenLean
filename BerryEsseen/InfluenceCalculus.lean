import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The scalar chain rule calculation in Lemma 4.3.
Inputs: the separately required contamination derivatives of the moments and
convolution CDF. This does NOT prove those input identities for measures. -/
open scoped Topology
namespace BerryEsseen

theorem contamination_chain_rule
    (m v ρ F Φ : ℝ → ℝ) (s z y β M G R φ : ℝ)
    (hs : s ≠ 0) (hβ : β ≠ 0)
    (hm0 : m 0 = 0) (hv0 : v 0 = 1) (hρ0 : ρ 0 = β)
    (hR : R = s * (F 0 - Φ z) / β)
    (hm : HasDerivAt m y 0)
    (hv : HasDerivAt v (y ^ 2 - 1) 0)
    (hρ : HasDerivAt ρ (|y| ^ 3 - β - 3 * y * M) 0)
    (hF : HasDerivAt F (s ^ 2 * (G - F 0)) 0)
    (hΦ : HasDerivAt Φ φ z) :
    HasDerivAt
      (fun e => s * (Real.sqrt (v e)) ^ 3 / ρ e *
        (F e - Φ ((s * z - s ^ 2 * m e) / (s * Real.sqrt (v e)))))
      ((s ^ 3 * (G - F 0) + s ^ 2 * y * φ +
        s / 2 * z * φ * (y ^ 2 - 1) +
        3 / 2 * R * β * (y ^ 2 - 1) -
        R * (|y| ^ 3 - β - 3 * y * M)) / β) 0 := by
  have hvne : v 0 ≠ 0 := by rw [hv0]; norm_num
  have hvroot := hv.sqrt hvne
  have hden : s * Real.sqrt (v 0) ≠ 0 := by simpa [hv0] using hs
  have harg := ((hm.const_mul (s ^ 2)).const_sub (s * z)).div
    (hvroot.const_mul s) hden
  have harg0 : (s * z - s ^ 2 * m 0) / (s * Real.sqrt (v 0)) = z := by
    simp [hm0, hv0, hs]
  have hΦarg : HasDerivAt Φ φ ((s * z - s ^ 2 * m 0) / (s * Real.sqrt (v 0))) := by
    rw [harg0]; exact hΦ
  have hpref := ((hvroot.pow 3).const_mul s).div hρ (by simpa [hρ0] using hβ)
  have hres := hpref.mul (hF.sub (hΦarg.comp 0 harg))
  convert hres using 1
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply]
  rw [harg0, hR]
  simp only [hm0, hv0, hρ0, Real.sqrt_one, mul_one, mul_zero, sub_zero, one_pow]
  push_cast
  field_simp
  ring

/-- The version applicable to genuine contamination measures: only right
derivatives within the probability-weight interval are required. -/
theorem contamination_chain_rule_within
    (m v ρ F Φ : ℝ → ℝ) (s z y β M G R φ : ℝ)
    (hs : s ≠ 0) (hβ : β ≠ 0)
    (hm0 : m 0 = 0) (hv0 : v 0 = 1) (hρ0 : ρ 0 = β)
    (hR : R = s * (F 0 - Φ z) / β)
    (hm : HasDerivWithinAt m y (Set.Icc 0 1) 0)
    (hv : HasDerivWithinAt v (y ^ 2 - 1) (Set.Icc 0 1) 0)
    (hρ : HasDerivWithinAt ρ (|y| ^ 3 - β - 3 * y * M) (Set.Icc 0 1) 0)
    (hF : HasDerivWithinAt F (s ^ 2 * (G - F 0)) (Set.Icc 0 1) 0)
    (hΦ : HasDerivAt Φ φ z) :
    HasDerivWithinAt
      (fun e => s * (Real.sqrt (v e)) ^ 3 / ρ e *
        (F e - Φ ((s * z - s ^ 2 * m e) / (s * Real.sqrt (v e)))))
      ((s ^ 3 * (G - F 0) + s ^ 2 * y * φ +
        s / 2 * z * φ * (y ^ 2 - 1) +
        3 / 2 * R * β * (y ^ 2 - 1) -
        R * (|y| ^ 3 - β - 3 * y * M)) / β) (Set.Icc 0 1) 0 := by
  have hvne : v 0 ≠ 0 := by rw [hv0]; norm_num
  have hvroot := hv.sqrt hvne
  have hden : s * Real.sqrt (v 0) ≠ 0 := by simpa [hv0] using hs
  have harg := ((hm.const_mul (s ^ 2)).const_sub (s * z)).div
    (hvroot.const_mul s) hden
  have harg0 : (s * z - s ^ 2 * m 0) / (s * Real.sqrt (v 0)) = z := by
    simp [hm0, hv0, hs]
  have hΦarg : HasDerivAt Φ φ ((s * z - s ^ 2 * m 0) / (s * Real.sqrt (v 0))) := by
    rw [harg0]; exact hΦ
  have hpref := ((hvroot.pow 3).const_mul s).div hρ (by simpa [hρ0] using hβ)
  have hres := hpref.mul (hF.sub (hΦarg.comp_hasDerivWithinAt 0 harg))
  convert hres using 1
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply]
  rw [harg0, hR]
  simp only [hm0, hv0, hρ0, Real.sqrt_one, mul_one, mul_zero, sub_zero, one_pow]
  push_cast
  field_simp
  ring

end BerryEsseen
