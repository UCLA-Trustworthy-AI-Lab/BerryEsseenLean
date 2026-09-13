import BerryEsseen.CompactJitterFourier

/-! Integrability on every finite smoothing interval. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem normalizedJittered_charFun_continuous (P : StandardizedLaw) (n : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    Continuous (charFun (normalizedJitteredSumLaw P n h)) := by
  have hc : Continuous (charFun P.measure) :=
    continuous_iff_continuousAt.2 (fun u => (charFun_hasDerivAt P u).continuousAt)
  have he : charFun (normalizedJitteredSumLaw P n h) = fun t : ℝ =>
      (Real.sinc (h * (t / Real.sqrt (n : ℝ)) / 2) : ℂ) * charFun P.measure (t / Real.sqrt (n : ℝ)) ^ n :=
    funext (charFun_normalizedJitteredSumLaw P n h hh)
  rw [he]
  fun_prop

theorem jitterFourierError_integrableOn (P : StandardizedLaw) (n : ℕ) (hn : 2 ≤ n)
    (hβ : thirdMoment P ≤ 2) (hb : ∀ᵐ x ∂P.measure, |x| ≤ 10)
    (h : ℝ) (hh : 0 ≤ h) (L : ℝ) :
    IntegrableOn (jitterFourierError P n h) (Icc (-L) L) := by
  let a := Real.sqrt (n : ℝ) / 200
  let K := Icc (-L) L ∩ {t : ℝ | a ≤ |t|}
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := div_pos (Real.sqrt_pos.2 hnpos) (by norm_num)
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hcJ := normalizedJittered_charFun_continuous P n h hh
  have hnum : Continuous (fun t => ‖charFun (normalizedJitteredSumLaw P n h) t -
      edgeworthChar n (signedThirdMoment P) t‖) := by
    unfold edgeworthChar
    fun_prop
  have hc : ContinuousOn (jitterFourierError P n h) K :=
    hnum.continuousOn.div continuous_abs.continuousOn (fun t ht => (ha.trans_le ht.2).ne')
  have hiK : IntegrableOn (jitterFourierError P n h) K := hc.integrableOn_compact hK
  have hiA := general_jitter_low_frequency_integrable P 2 (by norm_num) hβ n hn h hh
  have hset : generalLowFrequencyRange 2 n = Icc (-a) a := by
    unfold generalLowFrequencyRange
    congr 1 <;> dsimp [a] <;> ring
  rw [hset] at hiA
  apply (hiA.union hiK).mono_set
  intro t ht
  by_cases hlow : |t| ≤ a
  · exact Or.inl (abs_le.1 hlow)
  · exact Or.inr ⟨ht, (lt_of_not_ge hlow).le⟩

end BerryEsseen
