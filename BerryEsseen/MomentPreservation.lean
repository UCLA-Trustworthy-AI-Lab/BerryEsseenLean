import BerryEsseen.MomentCompactness

/-! Preservation of the first two moments under a uniform third-moment
bound. Truncation errors and limiting integrals are proved explicitly. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
namespace BerryEsseen

def clippedReal (A x : ℝ) : ℝ := max (-A) (min x A)

theorem clippedReal_abs_le (A x : ℝ) (hA : 0 ≤ A) : |clippedReal A x| ≤ A := by
  apply abs_le.2
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

def clippedRealBCF (A : ℝ) (hA : 0 ≤ A) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (clippedReal A)
    (by unfold clippedReal; fun_prop) A (fun x => by
      rw [Real.norm_eq_abs]; exact clippedReal_abs_le A x hA)

theorem clippedReal_error (A x : ℝ) (hA : 0 < A) : |x - clippedReal A x| ≤ x ^ 2 / A := by
  apply (le_div_iff₀ hA).2
  unfold clippedReal
  by_cases hlow : x < -A
  · rw [min_eq_left (by linarith : x ≤ A), max_eq_left hlow.le,
      abs_of_nonpos (by linarith : x - -A ≤ 0)]
    nlinarith [sq_nonneg (x + A)]
  · by_cases hhigh : A < x
    · rw [min_eq_right hhigh.le, max_eq_right (by linarith : -A ≤ A),
        abs_of_nonneg (by linarith : 0 ≤ x - A)]
      nlinarith [sq_nonneg (x - A)]
    · rw [min_eq_left (le_of_not_gt hhigh), max_eq_right (le_of_not_gt hlow)]
      simp [sq_nonneg]

theorem clippedReal_integral_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₁ : Integrable (fun x : ℝ => x) μ) (h₂ : Integrable (fun x : ℝ => x ^ 2) μ)
    (A : ℝ) (hA : 0 < A) :
    |(∫ x, x ∂μ) - ∫ x, clippedReal A x ∂μ| ≤ (∫ x, x ^ 2 ∂μ) / A := by
  have ht : Integrable (clippedReal A) μ := (clippedRealBCF A hA.le).integrable μ
  rw [← integral_sub h₁ ht]
  have hn := norm_integral_le_integral_norm (f := fun x => x - clippedReal A x) (μ := μ)
  simp only [Real.norm_eq_abs] at hn
  apply hn.trans
  rw [← integral_div]
  exact integral_mono (h₁.sub ht).abs (h₂.div_const A) (fun x => clippedReal_error A x hA)

theorem integrable_first_of_second (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₂ : Integrable (fun x : ℝ => x ^ 2) μ) : Integrable (fun x : ℝ => x) μ := by
  apply (h₂.add (integrable_const (1 : ℝ))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  change |x| ≤ x ^ 2 + 1
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

theorem standardized_weak_limit_first_second_integrable (P : ℕ → StandardizedLaw)
    (μ : ProbabilityMeasure ℝ) (hμ : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 μ)) :
    Integrable (fun x : ℝ => x) (μ : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ) ∧ (∫ x, x ^ 2 ∂(μ : Measure ℝ)) ≤ 1 := by
  have hh := weak_limit_integrable_moment_bound μ (fun j => (P j).toProbabilityMeasure) hμ
    (fun x : ℝ => x ^ 2) (by fun_prop) (fun x => sq_nonneg x) 1
    (fun j => (P j).second_integrable) (fun j => (P j).second_one.le)
  exact ⟨integrable_first_of_second (μ : Measure ℝ) hh.1, hh⟩

theorem standardized_weak_limit_mean (P : ℕ → StandardizedLaw)
    (μ : ProbabilityMeasure ℝ) (hμ : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 μ)) :
    (∫ x, x ∂(μ : Measure ℝ)) = 0 := by
  obtain ⟨hi₁, hi₂, hm₂⟩ := standardized_weak_limit_first_second_integrable P μ hμ
  have hbound (A : ℝ) (hA : 0 < A) : |∫ x, x ∂(μ : Measure ℝ)| ≤ 2 / A := by
    have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ) (clippedRealBCF A hA.le)
    have hcl : |∫ x, clippedReal A x ∂(μ : Measure ℝ)| ≤ 1 / A := by
      apply le_of_tendsto hc.abs
      filter_upwards [] with j
      have hh := clippedReal_integral_error (P j).measure (P j).first_integrable
        (P j).second_integrable A hA
      simpa only [(P j).mean_zero, (P j).second_one, zero_sub, abs_neg] using hh
    have he := clippedReal_integral_error (μ : Measure ℝ) hi₁ hi₂ A hA
    have he' := he.trans (div_le_div_of_nonneg_right hm₂ hA.le)
    have ht := abs_add_le ((∫ x, x ∂(μ : Measure ℝ)) - ∫ x, clippedReal A x ∂(μ : Measure ℝ))
      (∫ x, clippedReal A x ∂(μ : Measure ℝ))
    rw [sub_add_cancel] at ht
    calc
      |∫ x, x ∂(μ : Measure ℝ)| ≤ _ := ht
      _ ≤ 1 / A + 1 / A := add_le_add he' hcl
      _ = 2 / A := by ring
  have hzero : |∫ x, x ∂(μ : Measure ℝ)| ≤ 0 := by
    have hlim : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1)
    exact ge_of_tendsto hlim (Eventually.of_forall (fun n => hbound ((n : ℝ) + 1) (by positivity)))
  exact abs_eq_zero.1 (le_antisymm hzero (abs_nonneg _))

def clippedSquare (A x : ℝ) : ℝ := min (x ^ 2) (A ^ 2)

def clippedSquareBCF (A : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (clippedSquare A)
    (by unfold clippedSquare; fun_prop) (A ^ 2) (fun x => by
      rw [Real.norm_eq_abs, clippedSquare, abs_of_nonneg (le_min (sq_nonneg x) (sq_nonneg A))]
      exact min_le_right _ _)

theorem clippedSquare_error (A x : ℝ) (hA : 0 < A) :
    x ^ 2 - clippedSquare A x ≤ |x| ^ 3 / A := by
  apply (le_div_iff₀ hA).2
  unfold clippedSquare
  by_cases hx : x ^ 2 ≤ A ^ 2
  · rw [min_eq_left hx]
    simp only [sub_self, zero_mul]
    positivity
  · rw [min_eq_right (le_of_not_ge hx)]
    have ha : A ≤ |x| := by nlinarith [sq_abs x, abs_nonneg x]
    have hh := mul_le_mul_of_nonneg_right ha (sq_nonneg x)
    nlinarith [sq_abs x, mul_nonneg hA.le (sq_nonneg A)]

theorem standardized_clippedSquare_lower (P : StandardizedLaw) (A : ℝ) (hA : 0 < A) :
    1 - thirdMoment P / A ≤ ∫ x, clippedSquare A x ∂P.measure := by
  have hi : Integrable (clippedSquare A) P.measure := (clippedSquareBCF A).integrable P.measure
  have hh := integral_mono (P.second_integrable.sub hi) (P.third_integrable.div_const A)
    (fun x => clippedSquare_error A x hA)
  change (∫ x, x ^ 2 - clippedSquare A x ∂P.measure) ≤ (∫ x, |x| ^ 3 / A ∂P.measure) at hh
  rw [integral_sub P.second_integrable hi, P.second_one, integral_div] at hh
  change 1 - (∫ x, |x| ^ 3 ∂P.measure) / A ≤ _
  linarith

theorem standardized_weak_limit_second (P : ℕ → StandardizedLaw) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 μ)) (B : ℝ)
    (hB : ∀ j, thirdMoment (P j) ≤ B) : (∫ x, x ^ 2 ∂(μ : Measure ℝ)) = 1 := by
  obtain ⟨_, hi₂, hm₂⟩ := standardized_weak_limit_first_second_integrable P μ hμ
  have hbound (A : ℝ) (hA : 0 < A) : 1 - B / A ≤ ∫ x, x ^ 2 ∂(μ : Measure ℝ) := by
    have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ) (clippedSquareBCF A)
    have hcl : 1 - B / A ≤ ∫ x, clippedSquare A x ∂(μ : Measure ℝ) := by
      apply ge_of_tendsto hc
      filter_upwards [] with j
      have hh := standardized_clippedSquare_lower (P j) A hA
      have hd := div_le_div_of_nonneg_right (hB j) hA.le
      change 1 - B / A ≤ ∫ x, clippedSquare A x ∂(P j).measure
      linarith
    exact hcl.trans (integral_mono ((clippedSquareBCF A).integrable _) hi₂
      (fun x => min_le_left _ _))
  have hlim : Tendsto (fun n : ℕ => 1 - B / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have hh : Tendsto (fun n : ℕ => B / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat B).comp (tendsto_add_atTop_nat 1)
    simpa using hh.const_sub 1
  have hlow : 1 ≤ ∫ x, x ^ 2 ∂(μ : Measure ℝ) :=
    le_of_tendsto hlim (Eventually.of_forall (fun n => hbound ((n : ℝ) + 1) (by positivity)))
  exact le_antisymm hm₂ hlow

/-- The precise compactness statement used in the attainment proof. The
third moments of the sequence converge to b, while the limit law has third
moment at most b; equality is obtained later from extremality. -/
theorem standardized_moment_subsequence (P : ℕ → StandardizedLaw) (B : ℝ)
    (hB : ∀ j, thirdMoment (P j) ≤ B) :
    ∃ (Q : StandardizedLaw) (u : ℕ → ℕ) (b : ℝ), StrictMono u ∧ 1 ≤ b ∧ b ≤ B ∧
      thirdMoment Q ≤ b ∧
      Tendsto (fun j => (P (u j)).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure) ∧
      Tendsto (fun j => thirdMoment (P (u j))) atTop (𝓝 b) := by
  obtain ⟨μ, u, hu, hμ⟩ := standardized_weak_subsequence P
  obtain ⟨b, hb, v, hv, hβ⟩ := isCompact_Icc.isSeqCompact
    (fun j => show thirdMoment (P (u j)) ∈ Icc 1 B from ⟨thirdMoment_ge_one _, hB _⟩)
  let P' : ℕ → StandardizedLaw := fun j => P (u (v j))
  have hw : Tendsto (fun j => (P' j).toProbabilityMeasure) atTop (𝓝 μ) := hμ.comp hv.tendsto_atTop
  have hB' : ∀ j, thirdMoment (P' j) ≤ B := fun j => hB _
  obtain ⟨hi₁, hi₂, _⟩ := standardized_weak_limit_first_second_integrable P' μ hw
  have hm := standardized_weak_limit_mean P' μ hw
  have hv₂ := standardized_weak_limit_second P' μ hw B hB'
  have hβ' : Tendsto (fun j => ∫ x, |x| ^ 3 ∂((P' j).toProbabilityMeasure : Measure ℝ))
      atTop (𝓝 b) := hβ
  have hthird := weak_limit_moment_le_of_tendsto μ (fun j => (P' j).toProbabilityMeasure) hw
    (fun x : ℝ => |x| ^ 3) (by fun_prop) (fun x => by positivity)
    (fun j => (P' j).third_integrable) b hβ'
  let Q : StandardizedLaw := ⟨(μ : Measure ℝ), inferInstance, hi₁, hi₂, hthird.1, hm, hv₂⟩
  exact ⟨Q, u ∘ v, b, hu.comp hv, hb.1, hb.2, hthird.2, hw, hβ⟩

end BerryEsseen
