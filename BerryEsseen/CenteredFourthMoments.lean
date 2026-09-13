import BerryEsseen.SumMoments

/-! Actual centered convolution moments, noise-block budgets, and an absolute-moment lower bound. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem integrable_pow_of_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x ^ 4) μ) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun x : ℝ => x ^ k) μ := by
  apply ((integrable_const (1 : ℝ)).add hi).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_pow]
  change |x| ^ k ≤ 1 + x ^ 4
  have hfour : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  by_cases hx : |x| ≤ 1
  · have hb := pow_le_one₀ (abs_nonneg x) hx (n := k)
    have h4 : 0 ≤ x ^ 4 := by positivity
    linarith
  · have hb := pow_le_pow_right₀ (by linarith : 1 ≤ |x|) hk
    rw [hfour] at hb
    linarith

structure CenteredFourthLaw where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  fourth_integrable : Integrable (fun x : ℝ => x ^ 4) measure
  mean_zero : (∫ x, x ∂measure) = 0

attribute [instance] CenteredFourthLaw.probability

theorem CenteredFourthLaw.integrable_pow (P : CenteredFourthLaw) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun x : ℝ => x ^ k) P.measure := integrable_pow_of_fourth P.measure P.fourth_integrable k hk

theorem CenteredFourthLaw.first_integrable (P : CenteredFourthLaw) : Integrable (fun x : ℝ => x) P.measure := by
  simpa only [pow_one] using P.integrable_pow 1 (by omega)

def CenteredFourthLaw.secondMoment (P : CenteredFourthLaw) : ℝ := ∫ x, x ^ 2 ∂P.measure

def CenteredFourthLaw.fourthMoment (P : CenteredFourthLaw) : ℝ := ∫ x, x ^ 4 ∂P.measure

theorem CenteredFourthLaw.secondMoment_nonneg (P : CenteredFourthLaw) : 0 ≤ P.secondMoment :=
  integral_nonneg (fun x => sq_nonneg x)

theorem CenteredFourthLaw.fourth_conv_integrable (P Q : CenteredFourthLaw) :
    Integrable (fun x : ℝ => x ^ 4) (P.measure ∗ Q.measure) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
  have hx := P.fourth_integrable.comp_fst Q.measure
  have hy := Q.fourth_integrable.comp_snd P.measure
  have h31 := ((P.integrable_pow 3 (by omega)).mul_prod Q.first_integrable).const_mul 4
  have h22 := ((P.integrable_pow 2 (by omega)).mul_prod (Q.integrable_pow 2 (by omega))).const_mul 6
  have h13 := (P.first_integrable.mul_prod (Q.integrable_pow 3 (by omega))).const_mul 4
  convert (((hx.add h31).add h22).add h13).add hy using 1
  funext x
  dsimp
  ring

def CenteredFourthLaw.conv (P Q : CenteredFourthLaw) : CenteredFourthLaw where
  measure := P.measure ∗ Q.measure
  probability := inferInstance
  fourth_integrable := P.fourth_conv_integrable Q
  mean_zero := by
    rw [Measure.conv, integral_map (by fun_prop) (by fun_prop),
      integral_add (P.first_integrable.comp_fst Q.measure) (Q.first_integrable.comp_snd P.measure),
      integral_fun_fst (fun x : ℝ => x), integral_fun_snd (fun x : ℝ => x), P.mean_zero, Q.mean_zero]
    simp

theorem CenteredFourthLaw.secondMoment_conv (P Q : CenteredFourthLaw) :
    (P.conv Q).secondMoment = P.secondMoment + Q.secondMoment := by
  have hx := (P.integrable_pow 2 (by omega)).comp_fst Q.measure
  have hy := (Q.integrable_pow 2 (by omega)).comp_snd P.measure
  have hxy := (P.first_integrable.mul_prod Q.first_integrable).const_mul 2
  have hsum : Integrable (fun x : ℝ × ℝ => x.1 ^ 2 + 2 * (x.1 * x.2)) (P.measure.prod Q.measure) := hx.add hxy
  change (∫ x, x ^ 2 ∂(P.measure ∗ Q.measure)) = _
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ × ℝ => (x.1 + x.2) ^ 2) = (fun x => x.1 ^ 2 + 2 * (x.1 * x.2) + x.2 ^ 2) := by funext x; ring
  rw [he, integral_add hsum hy, integral_add hx hxy,
    integral_fun_fst (fun x : ℝ => x ^ 2), integral_fun_snd (fun x : ℝ => x ^ 2), integral_const_mul,
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x), P.mean_zero, Q.mean_zero]
  simp only [secondMoment, mul_zero, add_zero, probReal_univ, one_smul]

theorem CenteredFourthLaw.fourthMoment_conv (P Q : CenteredFourthLaw) :
    (P.conv Q).fourthMoment = P.fourthMoment + Q.fourthMoment + 6 * P.secondMoment * Q.secondMoment := by
  have hx := P.fourth_integrable.comp_fst Q.measure
  have hy := Q.fourth_integrable.comp_snd P.measure
  have h31 := ((P.integrable_pow 3 (by omega)).mul_prod Q.first_integrable).const_mul 4
  have h22 := ((P.integrable_pow 2 (by omega)).mul_prod (Q.integrable_pow 2 (by omega))).const_mul 6
  have h13 := (P.first_integrable.mul_prod (Q.integrable_pow 3 (by omega))).const_mul 4
  have hA : Integrable (fun x : ℝ × ℝ => x.1 ^ 4 + 4 * (x.1 ^ 3 * x.2)) (P.measure.prod Q.measure) := hx.add h31
  have hB : Integrable (fun x : ℝ × ℝ => x.1 ^ 4 + 4 * (x.1 ^ 3 * x.2) + 6 * (x.1 ^ 2 * x.2 ^ 2)) (P.measure.prod Q.measure) := hA.add h22
  have hC : Integrable (fun x : ℝ × ℝ => x.1 ^ 4 + 4 * (x.1 ^ 3 * x.2) + 6 * (x.1 ^ 2 * x.2 ^ 2) + 4 * (x.1 * x.2 ^ 3)) (P.measure.prod Q.measure) := hB.add h13
  change (∫ x, x ^ 4 ∂(P.measure ∗ Q.measure)) = _
  rw [Measure.conv, integral_map (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ × ℝ => (x.1 + x.2) ^ 4) =
      (fun x => x.1 ^ 4 + 4 * (x.1 ^ 3 * x.2) + 6 * (x.1 ^ 2 * x.2 ^ 2) + 4 * (x.1 * x.2 ^ 3) + x.2 ^ 4) := by funext x; ring
  rw [he, integral_add hC hy,
    integral_add hB h13, integral_add hA h22, integral_add hx h31,
    integral_fun_fst (fun x : ℝ => x ^ 4), integral_fun_snd (fun x : ℝ => x ^ 4)]
  simp only [integral_const_mul]
  rw [integral_prod_mul (fun x : ℝ => x ^ 3) (fun x : ℝ => x),
    integral_prod_mul (fun x : ℝ => x ^ 2) (fun x : ℝ => x ^ 2),
    integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x ^ 3)]
  simp only [P.mean_zero, Q.mean_zero, mul_zero, zero_mul, add_zero, probReal_univ, one_smul]
  unfold fourthMoment secondMoment
  ring

def CenteredFourthLaw.zero : CenteredFourthLaw where
  measure := Measure.dirac 0
  probability := inferInstance
  fourth_integrable := integrable_dirac (by simp)
  mean_zero := by simp

def CenteredFourthLaw.iid (P : CenteredFourthLaw) : ℕ → CenteredFourthLaw
  | 0 => CenteredFourthLaw.zero
  | n + 1 => P.conv (P.iid n)

theorem CenteredFourthLaw.iid_measure (P : CenteredFourthLaw) (n : ℕ) :
    (P.iid n).measure = iidSumLaw P.measure n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change P.measure ∗ (P.iid n).measure = _
    rw [ih]
    rfl

theorem CenteredFourthLaw.secondMoment_iid (P : CenteredFourthLaw) (n : ℕ) :
    (P.iid n).secondMoment = (n : ℝ) * P.secondMoment := by
  induction n with
  | zero => simp [iid, secondMoment, zero]
  | succ n ih =>
    rw [iid, secondMoment_conv, ih]
    push_cast
    ring

theorem CenteredFourthLaw.fourthMoment_iid (P : CenteredFourthLaw) (n : ℕ) :
    (P.iid n).fourthMoment = (n : ℝ) * P.fourthMoment + 3 * n * ((n : ℝ) - 1) * P.secondMoment ^ 2 := by
  induction n with
  | zero => simp [iid, fourthMoment, zero]
  | succ n ih =>
    rw [iid, fourthMoment_conv, ih, secondMoment_iid]
    push_cast
    ring

theorem CenteredFourthLaw.bounded_fourthMoment (P : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hb : ∀ᵐ x ∂P.measure, |x| ≤ ε) :
    P.fourthMoment ≤ ε ^ 2 * P.secondMoment := by
  unfold fourthMoment secondMoment
  rw [← integral_const_mul]
  apply integral_mono_ae P.fourth_integrable ((P.integrable_pow 2 (by omega)).const_mul _)
  filter_upwards [hb] with x hx
  have hsq : x ^ 2 ≤ ε ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg x)
  nlinarith only [hm]

theorem CenteredFourthLaw.fourth_budget_conv (P Q : CenteredFourthLaw) (ε : ℝ)
    (hP : P.fourthMoment ≤ 3 * P.secondMoment ^ 2 + ε ^ 2 * P.secondMoment)
    (hQ : Q.fourthMoment ≤ 3 * Q.secondMoment ^ 2 + ε ^ 2 * Q.secondMoment) :
    (P.conv Q).fourthMoment ≤ 3 * (P.conv Q).secondMoment ^ 2 + ε ^ 2 * (P.conv Q).secondMoment := by
  rw [fourthMoment_conv, secondMoment_conv]
  nlinarith only [hP, hQ]

theorem CenteredFourthLaw.fourth_budget_iid (P : CenteredFourthLaw) (ε : ℝ)
    (hP : P.fourthMoment ≤ ε ^ 2 * P.secondMoment) (n : ℕ) :
    (P.iid n).fourthMoment ≤ 3 * (P.iid n).secondMoment ^ 2 + ε ^ 2 * (P.iid n).secondMoment := by
  induction n with
  | zero => simp [iid, fourthMoment, secondMoment, zero]
  | succ n ih =>
    exact fourth_budget_conv P (P.iid n) ε (by nlinarith [sq_nonneg P.secondMoment]) ih

/-- The convolution block corresponding to n-k lower labels and k upper labels. -/
def twoNoiseBlock (P Q : CenteredFourthLaw) (n k : ℕ) : CenteredFourthLaw :=
  (P.iid (n - k)).conv (Q.iid k)

theorem twoNoiseBlock_variance (P Q : CenteredFourthLaw) (n k : ℕ) :
    (twoNoiseBlock P Q n k).secondMoment = (n - k : ℕ) * P.secondMoment + k * Q.secondMoment := by
  rw [twoNoiseBlock, CenteredFourthLaw.secondMoment_conv, CenteredFourthLaw.secondMoment_iid, CenteredFourthLaw.secondMoment_iid]

theorem twoNoiseBlock_fourth_bound (P Q : CenteredFourthLaw) (n k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    (twoNoiseBlock P Q n k).fourthMoment ≤
      3 * ((n - k : ℕ) * P.secondMoment + k * Q.secondMoment) ^ 2 +
        ε ^ 2 * ((n - k : ℕ) * P.secondMoment + k * Q.secondMoment) := by
  rw [← twoNoiseBlock_variance]
  exact CenteredFourthLaw.fourth_budget_conv _ _ ε
    (P.fourth_budget_iid ε (P.bounded_fourthMoment ε hε hP) _)
    (Q.fourth_budget_iid ε (Q.bounded_fourthMoment ε hε hQ) _)

def CenteredFourthLaw.ofBounded (μ : Measure ℝ) [IsProbabilityMeasure μ] (ε : ℝ)
    (hb : ∀ᵐ x ∂μ, |x| ≤ ε) (hm : (∫ x, x ∂μ) = 0) : CenteredFourthLaw where
  measure := μ
  probability := inferInstance
  fourth_integrable := by
    apply (integrable_const (ε ^ 4)).mono' (by fun_prop)
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 4
  mean_zero := hm

def CenteredFourthLaw.absoluteMoment (P : CenteredFourthLaw) : ℝ := ∫ x, |x| ∂P.measure

theorem scalar_second_moment_split (x K : ℝ) (hK : 0 < K) : x ^ 2 ≤ K * |x| + x ^ 4 / K ^ 2 := by
  by_cases hx : |x| ≤ K
  · have hm := mul_le_mul_of_nonneg_right hx (abs_nonneg x)
    have hsq : x ^ 2 ≤ K * |x| := by simpa only [← sq, sq_abs] using hm
    exact hsq.trans (le_add_of_nonneg_right (by positivity))
  · have hsq : K ^ 2 ≤ x ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hK.le (le_of_not_ge hx) 2
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg x)
    have hdiv : x ^ 2 ≤ x ^ 4 / K ^ 2 := (le_div_iff₀ (sq_pos_of_pos hK)).2 (by nlinarith only [hm])
    exact hdiv.trans (le_add_of_nonneg_left (mul_nonneg hK.le (abs_nonneg x)))

theorem CenteredFourthLaw.absoluteMoment_lower_from_budget (P : CenteredFourthLaw) (ε : ℝ)
    (ht : 0 < P.secondMoment)
    (hfour : P.fourthMoment ≤ 3 * P.secondMoment ^ 2 + ε ^ 2 * P.secondMoment) :
    P.secondMoment / (2 * Real.sqrt (2 * (3 * P.secondMoment + ε ^ 2))) ≤ P.absoluteMoment := by
  let K := Real.sqrt (2 * (3 * P.secondMoment + ε ^ 2))
  have hK : 0 < K := Real.sqrt_pos.2 (by nlinarith [sq_nonneg ε])
  have hKsq : K ^ 2 = 2 * (3 * P.secondMoment + ε ^ 2) := Real.sq_sqrt (by nlinarith [sq_nonneg ε])
  have hIa : Integrable (fun x : ℝ => K * |x|) P.measure := P.first_integrable.abs.const_mul K
  have hIb : Integrable (fun x : ℝ => x ^ 4 / K ^ 2) P.measure := P.fourth_integrable.div_const _
  have hb := integral_mono (P.integrable_pow 2 (by omega)) (hIa.add hIb) (fun x => scalar_second_moment_split x K hK)
  change (∫ x, x ^ 2 ∂P.measure) ≤ ∫ x, K * |x| + x ^ 4 / K ^ 2 ∂P.measure at hb
  rw [integral_add hIa hIb, integral_const_mul, integral_div] at hb
  change P.secondMoment ≤ K * P.absoluteMoment + P.fourthMoment / K ^ 2 at hb
  have hmul := (le_div_iff₀ (sq_pos_of_pos hK)).1 (show P.secondMoment - K * P.absoluteMoment ≤ P.fourthMoment / K ^ 2 by linarith)
  have hstep : P.secondMoment ≤ 2 * K * P.absoluteMoment := by
    have hV : 0 < 3 * P.secondMoment + ε ^ 2 := by nlinarith [sq_nonneg ε]
    rw [hKsq] at hmul
    nlinarith only [hmul, hfour, hV]
  exact (div_le_iff₀ (mul_pos (by norm_num) hK)).2 (by nlinarith only [hstep])

end BerryEsseen
