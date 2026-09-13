import BerryEsseen.CenteredFourthMoments

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem CenteredFourthLaw.fourth_tail_bound (P : CenteredFourthLaw) (d : ℝ) (hd : 0 < d) :
    P.measure.real {x : ℝ | d ≤ |x|} ≤ P.fourthMoment / d ^ 4 := by
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (fun x : ℝ => (by positivity : 0 ≤ x ^ 4)))
    P.fourth_integrable (d ^ 4)
  have hm : P.measure.real {x : ℝ | d ≤ |x|} ≤ P.measure.real {x : ℝ | d ^ 4 ≤ x ^ 4} := by
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    have hh := pow_le_pow_left₀ hd.le hx 4
    simpa only [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)] using hh
  apply (le_div_iff₀ (pow_pos hd 4)).2
  have hmul := mul_le_mul_of_nonneg_left hm (pow_nonneg hd.le 4)
  unfold fourthMoment
  nlinarith

theorem CenteredFourthLaw.cdf_left_tail_bound (P : CenteredFourthLaw) (t d : ℝ)
    (hd : 0 < d) (ht : t ≤ -d) : cdf P.measure t ≤ P.fourthMoment / d ^ 4 := by
  apply (le_trans ?_ (P.fourth_tail_bound d hd))
  rw [cdf_eq_real]
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  change d ≤ |x|
  have hxt : x ≤ t := hx
  have hxneg : x < 0 := by linarith
  rw [abs_of_neg hxneg]
  linarith

theorem CenteredFourthLaw.cdf_right_tail_bound (P : CenteredFourthLaw) (t d : ℝ)
    (hd : 0 < d) (ht : d ≤ t) : 1 - cdf P.measure t ≤ P.fourthMoment / d ^ 4 := by
  have he : 1 - cdf P.measure t = P.measure.real (Ioi t) := by
    rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [he]
  apply (le_trans ?_ (P.fourth_tail_bound d hd))
  refine measureReal_mono ?_ (by finiteness)
  intro x hx
  change d ≤ |x|
  have htx : t < x := hx
  have hxpos : 0 < x := by linarith
  rw [abs_of_pos hxpos]
  linarith

theorem integer_block_cdf_error_bound (P : CenteredFourthLaw) (j k : ℤ) (u : ℝ)
    (hu : |u| ≤ 1 / 2) (hjk : j ≠ k) :
    |cdf P.measure ((k : ℝ) + u - j) - (if j < k then 1 else 0)| ≤
      P.fourthMoment / (|(j : ℝ) - k| - 1 / 2) ^ 4 := by
  have hu' := abs_le.1 hu
  rcases lt_or_gt_of_ne hjk with hjk | hjk
  · rw [if_pos hjk, abs_of_neg (by exact_mod_cast sub_neg.2 hjk : (j : ℝ) - k < 0)]
    have hdiff : (1 : ℝ) ≤ (k : ℝ) - j := by exact_mod_cast (show (1 : ℤ) ≤ k - j by omega)
    rw [abs_of_nonpos (by linarith [cdf_le_one P.measure ((k : ℝ) + u - j)])]
    have h := P.cdf_right_tail_bound ((k : ℝ) + u - j) ((k : ℝ) - j - 1 / 2) (by linarith) (by linarith)
    convert h using 1 <;> ring
  · rw [if_neg (not_lt_of_gt hjk), sub_zero, abs_of_nonneg (cdf_nonneg _ _),
      abs_of_pos (by exact_mod_cast sub_pos.2 hjk : 0 < (j : ℝ) - k)]
    have hdiff : (1 : ℝ) ≤ (j : ℝ) - k := by exact_mod_cast (show (1 : ℤ) ≤ j - k by omega)
    exact P.cdf_left_tail_bound ((k : ℝ) + u - j) ((j : ℝ) - k - 1 / 2) (by linarith) (by linarith)

end BerryEsseen
