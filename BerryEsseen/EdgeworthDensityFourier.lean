import BerryEsseen.GaussianFourierMoments
import BerryEsseen.GaussianHermiteCDF
import BerryEsseen.PublishedSmoothing
import BerryEsseen.LowFrequencyExpansion

/-! The signed comparison is an actual integrable density of mass one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem densityFourier_integrable (g : ℝ → ℝ) (hg : Integrable g) (u : ℝ) :
    Integrable (fun x : ℝ => (g x : ℂ) * realPhase u x) := by
  apply hg.norm.mono' (hg.ofReal.aestronglyMeasurable.mul (by unfold realPhase; fun_prop))
  exact ae_of_all _ (fun x => by
    simp only [norm_mul, Complex.norm_real, realPhase_norm, mul_one, le_refl])

theorem densityFourier_add (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) (u : ℝ) :
    densityFourier (fun x => f x + g x) u = densityFourier f u + densityFourier g u := by
  unfold densityFourier
  simp only [Complex.ofReal_add, add_mul]
  rw [integral_add (densityFourier_integrable f hf u) (densityFourier_integrable g hg u)]

theorem densityFourier_const_mul (g : ℝ → ℝ) (a u : ℝ) :
    densityFourier (fun x => a * g x) u = (a : ℂ) * densityFourier g u := by
  unfold densityFourier
  simp only [Complex.ofReal_mul, mul_assoc, integral_const_mul]

theorem standardNormalDensity_fourier (u : ℝ) : densityFourier standardNormalDensity u = gaussianChar u := by
  have hh := gaussian_weighted_zero u
  rw [weightedCharFun, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)] at hh
  simpa only [pow_zero, one_mul, Complex.real_smul, standardNormalDensity, densityFourier] using hh

theorem gaussianHermiteThree_fourier (u : ℝ) :
    densityFourier gaussianHermiteThree u = -Complex.I * (u : ℂ) ^ 3 * gaussianChar u := by
  have hh := gaussian_hermite_three_fourier u
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)] at hh
  convert hh using 1
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp [densityFourier, gaussianHermiteThree, standardNormalDensity]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem edgeworthDensity_fourier (n : ℕ) (κ u : ℝ) :
    densityFourier (edgeworthDensity n κ) u = edgeworthChar n κ u := by
  unfold edgeworthDensity
  rw [densityFourier_add _ _ standardNormalDensity_integrable (gaussianHermiteThree_integrable.const_mul _),
    densityFourier_const_mul, standardNormalDensity_fourier, gaussianHermiteThree_fourier,
    gaussianChar_eq_real]
  unfold edgeworthChar
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem densityFourier_zero (g : ℝ → ℝ) : densityFourier g 0 = ((∫ x, g x : ℝ) : ℂ) := by
  unfold densityFourier realPhase
  simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, integral_complex_ofReal]

theorem edgeworthDensity_mass_one (n : ℕ) (κ : ℝ) : (∫ x, edgeworthDensity n κ x) = 1 := by
  have hh := edgeworthDensity_fourier n κ 0
  rw [densityFourier_zero] at hh
  simp [edgeworthChar] at hh
  exact_mod_cast hh

end BerryEsseen
