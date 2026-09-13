import BerryEsseen.CharacteristicDerivatives
import BerryEsseen.GaussianBounds

/-! Gaussian characteristic moments used to verify the signed Edgeworth density. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def gaussianChar (u : ℝ) : ℂ := Complex.exp (-(u : ℂ) ^ 2 / 2)

theorem gaussianChar_eq_real (u : ℝ) : gaussianChar u = (Real.exp (-u ^ 2 / 2) : ℂ) := by
  rw [Complex.ofReal_exp]
  simp only [gaussianChar, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat]

theorem gaussianChar_hasDerivAt (u : ℝ) :
    HasDerivAt gaussianChar (-(u : ℂ) * gaussianChar u) u := by
  have hd := (((((hasDerivAt_id (u : ℂ)).pow 2).neg).div_const 2).cexp).comp_ofReal
  convert hd using 1
  dsimp [gaussianChar]
  ring

theorem gaussian_power_integrable (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (show (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) by simp) k

theorem gaussian_weighted_zero (u : ℝ) : weightedCharFun (gaussianReal 0 1) 0 u = gaussianChar u := by
  rw [weightedCharFun_zero, charFun_gaussianReal]
  simp [gaussianChar, neg_div]

theorem gaussian_weighted_one (u : ℝ) :
    weightedCharFun (gaussianReal 0 1) 1 u = Complex.I * (u : ℂ) * gaussianChar u := by
  have hd := weightedCharFun_hasDerivAt (gaussianReal 0 1) 0 (gaussian_power_integrable 0) (gaussian_power_integrable 1) u
  have he : weightedCharFun (gaussianReal 0 1) 0 = gaussianChar := funext gaussian_weighted_zero
  rw [he] at hd
  have hh := hd.unique (gaussianChar_hasDerivAt u)
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [hh]
  ring_nf
  simp [Complex.I_sq]

theorem gaussian_weighted_two (u : ℝ) :
    weightedCharFun (gaussianReal 0 1) 2 u = (1 - (u : ℂ) ^ 2) * gaussianChar u := by
  have hd := weightedCharFun_hasDerivAt (gaussianReal 0 1) 1 (gaussian_power_integrable 1) (gaussian_power_integrable 2) u
  have he : weightedCharFun (gaussianReal 0 1) 1 = fun v : ℝ => Complex.I * (v : ℂ) * gaussianChar v := funext gaussian_weighted_one
  rw [he] at hd
  have hid : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := by
    simpa only [id_eq] using (hasDerivAt_id (u : ℂ)).comp_ofReal
  have hd' := (hid.const_mul Complex.I).mul (gaussianChar_hasDerivAt u)
  have hh := hd.unique hd'
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [hh]
  ring

theorem gaussian_weighted_three (u : ℝ) :
    weightedCharFun (gaussianReal 0 1) 3 u = Complex.I * (3 * (u : ℂ) - (u : ℂ) ^ 3) * gaussianChar u := by
  have hd := weightedCharFun_hasDerivAt (gaussianReal 0 1) 2 (gaussian_power_integrable 2) (gaussian_power_integrable 3) u
  have he : weightedCharFun (gaussianReal 0 1) 2 = fun v : ℝ => (1 - (v : ℂ) ^ 2) * gaussianChar v := funext gaussian_weighted_two
  rw [he] at hd
  have hid : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := by
    simpa only [id_eq] using (hasDerivAt_id (u : ℂ)).comp_ofReal
  have hd' := ((hid.pow 2).const_sub 1).mul (gaussianChar_hasDerivAt u)
  have hh := hd.unique hd'
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [hh]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem gaussian_hermite_three_fourier (u : ℝ) :
    (∫ x : ℝ, (((x ^ 3 - 3 * x : ℝ) : ℂ) * realPhase u x) ∂gaussianReal 0 1) =
      -Complex.I * (u : ℂ) ^ 3 * gaussianChar u := by
  have h3 := weightedCharFun_integrable (gaussianReal 0 1) 3 (gaussian_power_integrable 3) u
  have h1 := weightedCharFun_integrable (gaussianReal 0 1) 1 (gaussian_power_integrable 1) u
  have he : (fun x : ℝ => (((x ^ 3 - 3 * x : ℝ) : ℂ) * realPhase u x)) =
      (fun x : ℝ => (x : ℂ) ^ 3 * realPhase u x - (3 : ℂ) * ((x : ℂ) ^ 1 * realPhase u x)) := by
    funext x
    push_cast
    ring
  rw [he, integral_sub h3 (h1.const_mul _), integral_const_mul]
  change weightedCharFun _ 3 u - 3 * weightedCharFun _ 1 u = _
  rw [gaussian_weighted_three, gaussian_weighted_one]
  ring

end BerryEsseen
