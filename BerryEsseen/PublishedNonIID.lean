import BerryEsseen.ExactMomentInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def CenteredFourthLaw.absThirdMoment (P : CenteredFourthLaw) : ℝ := ∫ x, |x| ^ 3 ∂P.measure

theorem CenteredFourthLaw.absThirdMoment_nonneg (P : CenteredFourthLaw) : 0 ≤ P.absThirdMoment :=
  integral_nonneg (fun x => pow_nonneg (abs_nonneg x) 3)

theorem CenteredFourthLaw.absThirdMoment_bound (P : CenteredFourthLaw) (ε : ℝ)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) : P.absThirdMoment ≤ ε * P.secondMoment := by
  unfold absThirdMoment secondMoment
  rw [← integral_const_mul]
  apply integral_mono_ae (by simpa only [abs_pow] using (P.integrable_pow 3 (by omega)).abs)
    ((P.integrable_pow 2 (by omega)).const_mul ε)
  filter_upwards [hP] with x hx
  calc
    |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    _ ≤ ε * x ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg x)

def noiseListSum : List CenteredFourthLaw → CenteredFourthLaw
  | [] => CenteredFourthLaw.zero
  | P :: L => P.conv (noiseListSum L)

def noiseListThirdBudget (L : List CenteredFourthLaw) : ℝ := (L.map CenteredFourthLaw.absThirdMoment).sum

theorem noiseListThirdBudget_nonneg (L : List CenteredFourthLaw) : 0 ≤ noiseListThirdBudget L := by
  induction L with
  | nil => simp [noiseListThirdBudget]
  | cons P L ih => simpa only [noiseListThirdBudget, List.map_cons, List.sum_cons] using add_nonneg P.absThirdMoment_nonneg ih

theorem noiseListSum_variance (L : List CenteredFourthLaw) :
    (noiseListSum L).secondMoment = (L.map CenteredFourthLaw.secondMoment).sum := by
  induction L with
  | nil => simp [noiseListSum, CenteredFourthLaw.secondMoment, CenteredFourthLaw.zero]
  | cons P L ih => rw [noiseListSum, CenteredFourthLaw.secondMoment_conv, ih, List.map_cons, List.sum_cons]

theorem noiseListSum_append_measure (L K : List CenteredFourthLaw) :
    (noiseListSum (L ++ K)).measure = (noiseListSum L).measure ∗ (noiseListSum K).measure := by
  induction L with
  | nil => simp [noiseListSum, CenteredFourthLaw.zero]
  | cons P L ih =>
    simp only [List.cons_append, noiseListSum, CenteredFourthLaw.conv]
    rw [ih, Measure.conv_assoc]

theorem noiseListSum_replicate_measure (P : CenteredFourthLaw) (n : ℕ) :
    (noiseListSum (List.replicate n P)).measure = iidSumLaw P.measure n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, noiseListSum, CenteredFourthLaw.conv, iidSumLaw, ih]
    rfl

theorem noiseListSum_two_blocks_measure (P Q : CenteredFourthLaw) (n k : ℕ) :
    (noiseListSum (List.replicate (n - k) P ++ List.replicate k Q)).measure = (twoNoiseBlock P Q n k).measure := by
  rw [noiseListSum_append_measure, noiseListSum_replicate_measure, noiseListSum_replicate_measure]
  simp only [twoNoiseBlock, CenteredFourthLaw.conv, CenteredFourthLaw.iid_measure]

/-- Shevtsova (2013), printed p.124, the general independent-summand bound
Delta_n <= 0.5583 ell_n. Expressed for the actual finite convolution, with
arbitrary total positive variance by the standard rescaling of all summands.
The fourth-moment hypotheses here are stronger than the published third-moment
hypotheses. No local-mass assertion is assumed. -/
structure PublishedNonIIDBound : Prop where
  bound : ∀ (L : List CenteredFourthLaw), L ≠ [] →
    0 < (noiseListSum L).secondMoment → ∀ t : ℝ,
      |cdf (noiseListSum L).measure t - normalCDF (t / Real.sqrt (noiseListSum L).secondMoment)| ≤
        (0.5583 : ℝ) * noiseListThirdBudget L / Real.sqrt (noiseListSum L).secondMoment ^ 3

theorem twoNoiseBlock_normal_bound (S : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (ht : 0 < (twoNoiseBlock P Q n k).secondMoment) (x : ℝ) :
    |cdf (twoNoiseBlock P Q n k).measure x - normalCDF (x / Real.sqrt (twoNoiseBlock P Q n k).secondMoment)| ≤
      (0.56 : ℝ) * ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment := by
  let L := List.replicate (n - k) P ++ List.replicate k Q
  have hLne : L ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [L, List.length_append, List.length_replicate, List.length_nil] at hh
    omega
  have hμ : (noiseListSum L).measure = (twoNoiseBlock P Q n k).measure := noiseListSum_two_blocks_measure P Q n k
  have hv : (noiseListSum L).secondMoment = (twoNoiseBlock P Q n k).secondMoment := by
    unfold CenteredFourthLaw.secondMoment
    rw [hμ]
  have hbound := S.bound L hLne (by rwa [hv]) x
  rw [hμ, hv] at hbound
  have hbudget : noiseListThirdBudget L ≤ ε * (twoNoiseBlock P Q n k).secondMoment := by
    simp only [L, noiseListThirdBudget, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
      nsmul_eq_mul, twoNoiseBlock_variance]
    have h0 := mul_le_mul_of_nonneg_left (P.absThirdMoment_bound ε hP) (Nat.cast_nonneg (n - k) : (0 : ℝ) ≤ (n - k : ℕ))
    have h1 := mul_le_mul_of_nonneg_left (Q.absThirdMoment_bound ε hQ) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith only [h0, h1]
  have hs := Real.sqrt_pos.2 ht
  have hbudget0 := noiseListThirdBudget_nonneg L
  have hnum : (0.5583 : ℝ) * noiseListThirdBudget L ≤ (0.56 : ℝ) * ε * (twoNoiseBlock P Q n k).secondMoment := by
    nlinarith [mul_nonneg hε ht.le]
  apply hbound.trans
  have h := div_le_div_of_nonneg_right hnum (pow_nonneg hs.le 3)
  apply h.trans_eq
  field_simp [hs.ne']
  rw [Real.sq_sqrt ht.le]

end BerryEsseen
