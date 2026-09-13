import BerryEsseen.Resonances
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ComplexConjugate
namespace BerryEsseen

theorem realPhase_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    Integrable (realPhase u) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold realPhase; fun_prop)
  exact ae_of_all _ (fun x => (realPhase_norm u x).le)

theorem unit_phase_squared_distance (z c : ℂ) (hz : ‖z‖ = 1) (hc : ‖c‖ = 1) :
    ‖z - c‖ ^ 2 = 2 - 2 * (z * conj c).re := by
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hz, hc]
  norm_num

theorem phase_squared_deviation_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (c : ℂ) (hc : ‖c‖ = 1) : Integrable (fun x => ‖realPhase u x - c‖ ^ 2) μ := by
  have hi := (integrable_const (2 : ℝ)).sub (((realPhase_integrable μ u).mul_const (conj c)).re.const_mul 2)
  apply hi.congr
  exact ae_of_all _ (fun x => (unit_phase_squared_distance _ c (realPhase_norm u x) hc).symm)

theorem phase_squared_deviation_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (c : ℂ) (hc : ‖c‖ = 1) :
    (∫ x, ‖realPhase u x - c‖ ^ 2 ∂μ) = 2 - 2 * (charFun μ u * conj c).re := by
  have he : (fun x => ‖realPhase u x - c‖ ^ 2) = fun x => 2 - 2 * (realPhase u x * conj c).re := by
    funext x
    exact unit_phase_squared_distance _ c (realPhase_norm u x) hc
  have hi : Integrable (fun x => 2 * (realPhase u x * conj c).re) μ := ((realPhase_integrable μ u).mul_const (conj c)).re.const_mul 2
  have hri : (∫ x, (realPhase u x * conj c).re ∂μ) = (∫ x, realPhase u x * conj c ∂μ).re := integral_re ((realPhase_integrable μ u).mul_const (conj c))
  rw [he, integral_sub (integrable_const (2 : ℝ)) hi,
    integral_const, probReal_univ, one_smul, integral_const_mul,
    hri, integral_mul_const,
    ← charFun_eq_integral_realPhase]

theorem phase_concentration_identity (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    (∫ x, ‖realPhase u x - Complex.exp ((Complex.arg (charFun μ u) : ℂ) * Complex.I)‖ ^ 2 ∂μ) =
      2 * (1 - ‖charFun μ u‖) := by
  let c := Complex.exp ((Complex.arg (charFun μ u) : ℂ) * Complex.I)
  have hc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hprod : c * conj c = 1 := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hp : (‖charFun μ u‖ : ℂ) * c = charFun μ u := Complex.norm_mul_exp_arg_mul_I _
  have hr : (charFun μ u * conj c).re = ‖charFun μ u‖ := by
    calc
      _ = (((‖charFun μ u‖ : ℂ) * c) * conj c).re := by rw [hp]
      _ = _ := by rw [mul_assoc, hprod, mul_one, Complex.ofReal_re]
  change (∫ x, ‖realPhase u x - c‖ ^ 2 ∂μ) = _
  rw [phase_squared_deviation_integral μ u c hc, hr]
  ring

def circularResidual (v : ℝ) : ℝ := v - (round (v / (2 * Real.pi)) : ℝ) * (2 * Real.pi)

theorem circularResidual_bound (v : ℝ) : |circularResidual v| ≤ Real.pi := by
  have hp : 0 < 2 * Real.pi := by positivity
  have he : circularResidual v = (2 * Real.pi) * (v / (2 * Real.pi) - (round (v / (2 * Real.pi)) : ℝ)) := by
    unfold circularResidual
    field_simp <;> ring
  rw [he, abs_mul, abs_of_pos hp]
  have h := mul_le_mul_of_nonneg_left (abs_sub_round (v / (2 * Real.pi))) hp.le
  nlinarith only [h]

theorem circularResidual_phase (v : ℝ) : realPhase 1 (circularResidual v) = realPhase 1 v := by
  have he : (circularResidual v : ℂ) * Complex.I = (v : ℂ) * Complex.I -
      (round (v / (2 * Real.pi)) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold circularResidual
    push_cast
    ring
  simp only [realPhase, one_mul]
  rw [he, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

theorem realPhase_chord_lower (v : ℝ) (hv : |v| ≤ Real.pi) :
    |v| ≤ (Real.pi / 2) * ‖realPhase 1 v - 1‖ := by
  have hs := Real.mul_abs_le_abs_sin (x := v / 2) (by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  have hm := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  rw [realPhase, one_mul, mul_comm (v : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  convert hm using 1 <;> field_simp <;> ring

theorem circularResidual_chord_bound (v : ℝ) :
    |circularResidual v| ≤ (Real.pi / 2) * ‖realPhase 1 v - 1‖ := by
  have h := realPhase_chord_lower (circularResidual v) (circularResidual_bound v)
  rwa [circularResidual_phase] at h

def affineLattice (a h : ℝ) : Set ℝ := Set.range (fun k : ℤ => a + h * (k : ℝ))

theorem realPhase_difference_chord (u x θ : ℝ) :
    ‖realPhase 1 (u * x - θ) - 1‖ = ‖realPhase u x - realPhase 1 θ‖ := by
  have hc : realPhase 1 θ ≠ 0 := by rw [realPhase]; exact Complex.exp_ne_zero _
  have he : realPhase 1 (u * x - θ) = realPhase u x / realPhase 1 θ := by
    simp only [realPhase, one_mul]
    rw [show ((u * x - θ : ℝ) : ℂ) * Complex.I =
      ((u * x : ℝ) : ℂ) * Complex.I - (θ : ℂ) * Complex.I by push_cast; ring, Complex.exp_sub]
  have hd : realPhase 1 (u * x - θ) - 1 =
      (realPhase u x - realPhase 1 θ) / realPhase 1 θ := by rw [he]; field_simp
  rw [hd, norm_div, realPhase_norm, div_one]

theorem affineLattice_distance_phase_bound (u x θ : ℝ) (hu : 0 < u) :
    Metric.infDist x (affineLattice (θ / u) (2 * Real.pi / u)) ≤
      (Real.pi / (2 * u)) * ‖realPhase u x - realPhase 1 θ‖ := by
  let k := round ((u * x - θ) / (2 * Real.pi))
  have hm : θ / u + (2 * Real.pi / u) * (k : ℝ) ∈ affineLattice (θ / u) (2 * Real.pi / u) := ⟨k, rfl⟩
  have hd := Metric.infDist_le_dist_of_mem (x := x) hm
  rw [Real.dist_eq] at hd
  have he : x - (θ / u + (2 * Real.pi / u) * (k : ℝ)) = circularResidual (u * x - θ) / u := by
    dsimp only [circularResidual, k]
    field_simp <;> ring
  rw [he, abs_div, abs_of_pos hu] at hd
  have hb := div_le_div_of_nonneg_right (circularResidual_chord_bound (u * x - θ)) hu.le
  rw [realPhase_difference_chord] at hb
  convert hd.trans hb using 1 <;> ring

theorem affineLattice_squared_distance_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u θ : ℝ) (hu : 0 < u) :
    Integrable (fun x => Metric.infDist x (affineLattice (θ / u) (2 * Real.pi / u)) ^ 2) μ := by
  have hi := (phase_squared_deviation_integrable μ u (realPhase 1 θ) (realPhase_norm _ _)).const_mul
    ((Real.pi / (2 * u)) ^ 2)
  apply hi.mono' (((Metric.continuous_infDist_pt _).pow 2).aestronglyMeasurable)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ Metric.infDist_nonneg (affineLattice_distance_phase_bound u x θ hu) 2
  simpa only [mul_pow] using h

theorem affineLattice_squared_distance_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (hu : 0 < u) :
    (∫ x, Metric.infDist x (affineLattice (Complex.arg (charFun μ u) / u) (2 * Real.pi / u)) ^ 2 ∂μ) ≤
      (Real.pi ^ 2 / (2 * u ^ 2)) * (1 - ‖charFun μ u‖) := by
  let θ := Complex.arg (charFun μ u)
  have hi := (phase_squared_deviation_integrable μ u (realPhase 1 θ) (realPhase_norm _ _)).const_mul
    ((Real.pi / (2 * u)) ^ 2)
  have hb := integral_mono (affineLattice_squared_distance_integrable μ u θ hu) hi (fun x => by
    have h := pow_le_pow_left₀ Metric.infDist_nonneg (affineLattice_distance_phase_bound u x θ hu) 2
    simpa only [mul_pow] using h)
  rw [integral_const_mul] at hb
  have he : realPhase 1 θ = Complex.exp ((Complex.arg (charFun μ u) : ℂ) * Complex.I) := by
    simp only [realPhase, one_mul, θ]
  rw [he, phase_concentration_identity] at hb
  convert hb using 1 <;> ring

theorem near_lattice_of_large_characteristic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u δ : ℝ) (hu : 1 / 2 ≤ u) (huT : u ≤ 1000) (hδ : 0 ≤ δ)
    (hlarge : 1 - δ ≤ ‖charFun μ u‖) :
    ∃ a h : ℝ, Real.pi / 500 ≤ h ∧ h ≤ 4 * Real.pi ∧
      Integrable (fun x => Metric.infDist x (affineLattice a h) ^ 2) μ ∧
      (∫ x, Metric.infDist x (affineLattice a h) ^ 2 ∂μ) ≤ 2 * Real.pi ^ 2 * δ := by
  have hu0 : 0 < u := by linarith
  let a := Complex.arg (charFun μ u) / u
  let h := 2 * Real.pi / u
  have hlow : Real.pi / 500 ≤ h := by
    apply (le_div_iff₀ hu0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left huT Real.pi_pos.le]
  have hupp : h ≤ 4 * Real.pi := by
    apply (div_le_iff₀ hu0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hu Real.pi_pos.le]
  refine ⟨a, h, hlow, hupp, affineLattice_squared_distance_integrable μ u _ hu0, ?_⟩
  have hbound := affineLattice_squared_distance_bound μ u hu0
  have hc : Real.pi ^ 2 / (2 * u ^ 2) ≤ 2 * Real.pi ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * u ^ 2)).mpr
    have hu2 : (1 / 4 : ℝ) ≤ u ^ 2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_left hu2 (sq_nonneg Real.pi)]
  have hp : 0 ≤ 1 - ‖charFun μ u‖ := sub_nonneg.mpr (norm_charFun_le_one u)
  have hloss : 1 - ‖charFun μ u‖ ≤ δ := by linarith
  exact hbound.trans (mul_le_mul hc hloss hp (by positivity))

end BerryEsseen
