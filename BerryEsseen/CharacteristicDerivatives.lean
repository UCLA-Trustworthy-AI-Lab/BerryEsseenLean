import BerryEsseen.Resonances
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual characteristic derivatives and the curvature at every resonance. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def weightedCharFun (μ : Measure ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) ^ k * realPhase u x ∂μ

theorem weightedCharFun_integrable (μ : Measure ℝ) (k : ℕ)
    (hk : Integrable (fun x : ℝ => x ^ k) μ) (u : ℝ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ k * realPhase u x) μ := by
  apply hk.norm.mono' (by unfold realPhase; fun_prop)
  apply ae_of_all
  intro x
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, realPhase_norm, mul_one, abs_pow]
  exact le_rfl

theorem realPhase_hasDerivAt (u x : ℝ) :
    HasDerivAt (fun v => realPhase v x) (Complex.I * (x : ℂ) * realPhase u x) u := by
  have hd := ((((hasDerivAt_id (u : ℂ)).mul_const (x : ℂ)).mul_const Complex.I).cexp).comp_ofReal
  convert hd using 1
  · funext v
    simp only [realPhase, Complex.ofReal_mul]
    rfl
  · simp only [realPhase, Complex.ofReal_mul, mul_one, one_mul, id_eq]
    ring

theorem weightedCharFun_hasDerivAt (μ : Measure ℝ) (k : ℕ)
    (hk : Integrable (fun x : ℝ => x ^ k) μ)
    (hk1 : Integrable (fun x : ℝ => x ^ (k + 1)) μ) (u : ℝ) :
    HasDerivAt (weightedCharFun μ k) (Complex.I * weightedCharFun μ (k + 1) u) u := by
  let F : ℝ → ℝ → ℂ := fun v x => (x : ℂ) ^ k * realPhase v x
  let F' : ℝ → ℝ → ℂ := fun v x => Complex.I * ((x : ℂ) ^ (k + 1) * realPhase v x)
  have hm : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) μ :=
    .of_forall (fun v => by dsimp [F, realPhase]; fun_prop)
  have hm' : AEStronglyMeasurable (F' u) μ := by dsimp [F', realPhase]; fun_prop
  have hbound : ∀ᵐ x ∂μ, ∀ v ∈ (univ : Set ℝ), ‖F' v x‖ ≤ |x| ^ (k + 1) := by
    apply ae_of_all
    intro x v _
    simp only [F', norm_mul, Complex.norm_I, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      realPhase_norm, mul_one, one_mul, le_refl]
  have hb : Integrable (fun x : ℝ => |x| ^ (k + 1)) μ := by
    simpa only [Real.norm_eq_abs, abs_pow] using hk1.norm
  have hd : ∀ᵐ x ∂μ, ∀ v ∈ (univ : Set ℝ), HasDerivAt (fun w => F w x) (F' v x) v := by
    apply ae_of_all
    intro x v _
    convert (realPhase_hasDerivAt v x).const_mul ((x : ℂ) ^ k) using 1
    dsimp [F']
    ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (show (univ : Set ℝ) ∈ 𝓝 u from univ_mem) hm (weightedCharFun_integrable μ k hk u)
    hm' hbound hb hd).2
  simpa only [F, F', integral_const_mul, weightedCharFun] using h

theorem weightedCharFun_zero (μ : Measure ℝ) (u : ℝ) : weightedCharFun μ 0 u = charFun μ u := by
  simp only [weightedCharFun, pow_zero, one_mul, charFun_eq_integral_realPhase]

theorem charFun_hasDerivAt (P : StandardizedLaw) (u : ℝ) :
    HasDerivAt (charFun P.measure) (Complex.I * weightedCharFun P.measure 1 u) u := by
  have h0 : Integrable (fun x : ℝ => x ^ 0) P.measure := by simpa using integrable_const (1 : ℝ)
  have h1 : Integrable (fun x : ℝ => x ^ (0 + 1)) P.measure := by simpa using P.first_integrable
  have hf := weightedCharFun_hasDerivAt P.measure 0 h0 h1 u
  convert hf using 1
  funext t
  exact (weightedCharFun_zero P.measure t).symm

def charFunDerivative (P : StandardizedLaw) (u : ℝ) : ℂ := Complex.I * weightedCharFun P.measure 1 u

theorem charFunDerivative_hasDerivAt (P : StandardizedLaw) (u : ℝ) :
    HasDerivAt (charFunDerivative P) (-weightedCharFun P.measure 2 u) u := by
  have h1 : Integrable (fun x : ℝ => x ^ 1) P.measure := by simpa using P.first_integrable
  have hd := (weightedCharFun_hasDerivAt P.measure 1 h1 P.second_integrable u).const_mul Complex.I
  simpa only [charFunDerivative, ← mul_assoc, Complex.I_mul_I, neg_one_mul] using hd

def characteristicSquare (P : StandardizedLaw) (u : ℝ) : ℝ := ‖charFun P.measure u‖ ^ 2

def characteristicSquareSlope (P : StandardizedLaw) (u : ℝ) : ℝ :=
  2 * inner ℝ (charFun P.measure u) (charFunDerivative P u)

def characteristicSquareCurvature (P : StandardizedLaw) (u : ℝ) : ℝ :=
  2 * (inner ℝ (charFun P.measure u) (-weightedCharFun P.measure 2 u) +
    inner ℝ (charFunDerivative P u) (charFunDerivative P u))

theorem characteristicSquare_hasDerivAt (P : StandardizedLaw) (u : ℝ) :
    HasDerivAt (characteristicSquare P) (characteristicSquareSlope P u) u :=
  (charFun_hasDerivAt P u).norm_sq

theorem characteristicSquareSlope_hasDerivAt (P : StandardizedLaw) (u : ℝ) :
    HasDerivAt (characteristicSquareSlope P) (characteristicSquareCurvature P u) u :=
  ((charFun_hasDerivAt P u).inner ℝ (charFunDerivative_hasDerivAt P u)).const_mul 2

theorem weightedCharFun_at_resonance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (hu : u ∈ resonanceSubgroup μ) (k : ℕ) :
    weightedCharFun μ k u = ((∫ x : ℝ, x ^ k ∂μ : ℝ) : ℂ) * charFun μ u := by
  have hphase : ∀ᵐ x ∂μ, realPhase u x = charFun μ u := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact resonance_phase_on_support μ u hu x hx
  calc
    _ = ∫ x : ℝ, ((x ^ k : ℝ) : ℂ) * charFun μ u ∂μ := by
      apply integral_congr_ae
      filter_upwards [hphase] with x hx
      simp only [weightedCharFun, hx, Complex.ofReal_pow]
    _ = _ := by rw [integral_mul_const, integral_complex_ofReal]

theorem characteristicSquareCurvature_at_resonance (P : StandardizedLaw)
    (u : ℝ) (hu : u ∈ resonanceSubgroup P.measure) : characteristicSquareCurvature P u = -2 := by
  have h1 : weightedCharFun P.measure 1 u = 0 := by
    rw [weightedCharFun_at_resonance P.measure u hu]
    simp only [pow_one, P.mean_zero, Complex.ofReal_zero, zero_mul]
  have h2 : weightedCharFun P.measure 2 u = charFun P.measure u := by
    rw [weightedCharFun_at_resonance P.measure u hu, P.second_one]
    simp
  have hn := (mem_resonanceSubgroup_iff P.measure u).1 hu
  simp only [characteristicSquareCurvature, charFunDerivative, h1, h2, mul_zero,
    inner_neg_right, real_inner_self_eq_norm_sq, inner_zero_left, add_zero, hn]
  norm_num

end BerryEsseen
