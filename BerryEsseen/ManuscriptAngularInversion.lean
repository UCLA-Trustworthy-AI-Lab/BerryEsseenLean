import BerryEsseen.PublishedSmoothing
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BerryEsseen

def manuscriptAngularFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, f x * realPhase t x

theorem manuscriptAngularFourier_eq (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f t = manuscriptAngularFourier f (-2 * Real.pi * t) := by
  rw [Real.fourier_eq']
  unfold manuscriptAngularFourier realPhase
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 2
  simp only [Complex.ofReal_mul]
  ring

theorem manuscriptAngularFourier_inversion (f : ℝ → ℂ)
    (hf : Integrable f) (hc : Continuous f)
    (hF : Integrable (manuscriptAngularFourier f)) (x : ℝ) :
    f x = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, manuscriptAngularFourier f t * realPhase (-t) x := by
  have hscale : (-2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hfi : Integrable (𝓕 f) := by
    have heq : 𝓕 f = fun t => manuscriptAngularFourier f ((-2 * Real.pi)*t) :=
      funext (manuscriptAngularFourier_eq f)
    rw [heq]
    exact hF.comp_mul_left' hscale
  have hi := hf.fourierInv_fourier_eq hfi hc.continuousAt (v := x)
  rw [Real.fourierInv_eq'] at hi
  have he : (fun t : ℝ => Complex.exp (((2 * Real.pi * inner ℝ t x : ℝ) : ℂ) * Complex.I) • 𝓕 f t) =
      (fun t : ℝ => (fun u : ℝ => manuscriptAngularFourier f u * realPhase (-u) x)
        ((-2 * Real.pi) * t)) := by
    funext t
    rw [manuscriptAngularFourier_eq]
    simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul, realPhase]
    rw [mul_comm]
    congr 1
    congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  rw [he, Measure.integral_comp_mul_left
    (fun u : ℝ => manuscriptAngularFourier f u * realPhase (-u) x) (-2 * Real.pi)] at hi
  have hs : |(-2 * Real.pi : ℝ)⁻¹| = 1 / (2 * Real.pi) := by
    rw [abs_inv, abs_of_neg (by nlinarith [Real.pi_pos])]
    ring
  simpa only [hs, Complex.real_smul, one_div] using hi.symm

theorem manuscript_densityFourier_inversion (g : ℝ → ℝ)
    (hg : Integrable g) (hc : Continuous g)
    (hF : Integrable (densityFourier g)) (x : ℝ) :
    (g x : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, densityFourier g t * realPhase (-t) x := by
  exact manuscriptAngularFourier_inversion (fun y => (g y : ℂ)) hg.ofReal
    (Complex.continuous_ofReal.comp hc) hF x

end BerryEsseen
