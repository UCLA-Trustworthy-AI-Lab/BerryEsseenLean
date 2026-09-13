import BerryEsseen.Constants
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Support

/-! A concrete measure-theoretic statement of the requested theorem.
These are definitions of the target, NOT declarations that the target is true. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BerryEsseen

structure StandardizedLaw where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  first_integrable : Integrable (fun x : ℝ => x) measure
  second_integrable : Integrable (fun x : ℝ => x ^ 2) measure
  third_integrable : Integrable (fun x : ℝ => |x| ^ 3) measure
  mean_zero : (∫ x, x ∂measure) = 0
  second_one : (∫ x, x ^ 2 ∂measure) = 1

attribute [instance] StandardizedLaw.probability

def thirdMoment (P : StandardizedLaw) : ℝ := ∫ x, |x| ^ 3 ∂P.measure

theorem thirdMoment_ge_one (P : StandardizedLaw) : 1 ≤ thirdMoment P := by
  have hi : Integrable (fun x : ℝ => 2 / 3 * |x| ^ 3 + 1 / 3) P.measure :=
    (P.third_integrable.const_mul (2 / 3)).add (integrable_const (1 / 3))
  have hbound := integral_mono P.second_integrable hi (fun x => by
    have h := mul_nonneg (sq_nonneg (|x| - 1)) (by positivity : 0 ≤ 2 * |x| + 1)
    nlinarith [sq_abs x])
  rw [integral_add (P.third_integrable.const_mul (2 / 3)) (integrable_const (1 / 3)),
    integral_const_mul, P.second_one] at hbound
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hbound
  change 1 ≤ ∫ x, |x| ^ 3 ∂P.measure
  linarith

theorem thirdMoment_pos (P : StandardizedLaw) : 0 < thirdMoment P :=
  lt_of_lt_of_le (by norm_num) (thirdMoment_ge_one P)

/-- Distribution of the unnormalized sum, using products and measurable maps. -/
def iidSumLaw (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (μ.prod (iidSumLaw μ n)).map (fun xy : ℝ × ℝ => xy.1 + xy.2)

instance iidSumLaw_isProbabilityMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (iidSumLaw μ n) := by
  induction n with
  | zero => dsimp [iidSumLaw]; infer_instance
  | succ n ih =>
    letI := ih
    exact Measure.isProbabilityMeasure_map (by fun_prop)

def normalCDF (x : ℝ) : ℝ := ((gaussianReal 0 1) (Iic x)).toReal

def discrepancy (P : StandardizedLaw) (n : ℕ) (x : ℝ) : ℝ :=
  |((iidSumLaw P.measure n) (Iic (Real.sqrt (n : ℝ) * x))).toReal - normalCDF x|

def BoundAt (P : StandardizedLaw) (n : ℕ) : Prop :=
  ∀ x : ℝ, discrepancy P n x ≤ cE * thirdMoment P / Real.sqrt (n : ℝ)

/-- Universal N precedes the law P; P may vary with n. -/
def MainClaim : Prop := ∃ N : ℕ, 1 ≤ N ∧ ∀ n ≥ N, ∀ P : StandardizedLaw, BoundAt P n

def explicitThreshold : ℕ := 2 * ⌈Real.exp ((10 : ℝ) ^ 17)⌉₊

def ExplicitClaim : Prop :=
  ∀ n ≥ explicitThreshold, ∀ P : StandardizedLaw, BoundAt P n

theorem explicitThreshold_pos : 1 ≤ explicitThreshold := by
  have h : 0 < ⌈Real.exp ((10 : ℝ) ^ 17)⌉₊ := Nat.ceil_pos.2 (Real.exp_pos _)
  unfold explicitThreshold
  omega

/-- Only an implication: this does not furnish the missing proof of ExplicitClaim. -/
theorem mainClaim_of_explicit (h : ExplicitClaim) : MainClaim :=
  ⟨explicitThreshold, explicitThreshold_pos, h⟩

end BerryEsseen
