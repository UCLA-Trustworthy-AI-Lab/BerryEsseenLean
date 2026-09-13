import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.GeneralClusterJitter
import BerryEsseen.SmallVarianceNeighborhood
import BerryEsseen.SupportGeometry
import BerryEsseen.GeneralAccumulatedVariance

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem scaledSumCDFSup_eq_third_mul_normalized_sup (P : StandardizedLaw) (n : ℕ) :
    scaledSumCDFSup P n = thirdMoment P * sSup (range (normalizedDiscrepancy P n)) := by
  change scaledSumCDFSup P n = thirdMoment P • (⨆ x : ℝ, normalizedDiscrepancy P n x)
  rw [Real.smul_iSup_of_nonneg (thirdMoment_pos P).le (fun x : ℝ => normalizedDiscrepancy P n x)]
  unfold scaledSumCDFSup
  congr 2
  funext x
  unfold normalizedDiscrepancy discrepancy normalizedSumCDF
  rw [cdf_eq_real]
  dsimp only [Measure.real]
  simp only [smul_eq_mul]
  field_simp [(thirdMoment_pos P).ne']

theorem cluster_scaledSumCDFSup_eq_third_mul_raw (P Q : CenteredFourthLaw)
    (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) (hn : 1 ≤ n) :
    scaledSumCDFSup (standardizedTwoClusterLaw P Q p hp) n =
      thirdMoment (standardizedTwoClusterLaw P Q p hp) * rawNormalizedConstant (twoClusterMeasure P Q p) n := by
  rw [rawNormalizedConstant_twoCluster P Q p hp n hn]
  exact scaledSumCDFSup_eq_third_mul_normalized_sup _ _

theorem bernoulli_esseen_endpoint_parameters (p : ℝ) (hp : p ∈ Ioo 0 1)
    (he : p = pE ∨ p = 1 - pE) :
    Real.sqrt (p * (1 - p)) = sigmaE ∧
      thirdMoment (standardizedBernoulliLaw p hp) = betaE ∧
      |(1 - 2 * p) / Real.sqrt (p * (1 - p))| = kappaE := by
  have hd : 1 - 2 * pE = qE - pE := by unfold qE; ring
  rcases he with rfl | rfl
  · refine ⟨rfl, ?_, ?_⟩
    · rw [standardizedBernoulli_third]
      rfl
    · rw [hd]
      exact abs_of_pos kappaE_pos
  · have hv : (1 - pE) * (1 - (1 - pE)) = pE * qE := by unfold qE; ring
    have hd' : 1 - 2 * (1 - pE) = -(qE - pE) := by unfold qE; ring
    refine ⟨congrArg Real.sqrt hv, ?_, ?_⟩
    · rw [standardizedBernoulli_third, hv]
      unfold betaE sigmaE qE
      congr 1
      ring
    · rw [hv, hd', neg_div, abs_neg]
      exact abs_of_pos kappaE_pos

theorem bernoulli_esseen_endpoint_peak_identity (p : ℝ) (hp : p ∈ Ioo 0 1)
    (he : p = pE ∨ p = 1 - pE) :
    (1 / Real.sqrt (p * (1 - p)) / 2 +
      |(1 - 2 * p) / Real.sqrt (p * (1 - p))| / 6) * phi0 =
      thirdMoment (standardizedBernoulliLaw p hp) * cE := by
  obtain ⟨hs, hβ, hκ⟩ := bernoulli_esseen_endpoint_parameters p hp he
  rw [hκ, hs, hβ, mul_comm betaE cE]
  exact esseen_peak_identity

/-- A nonnegative sequence must vanish if every positive subsequence forces
an eventual strict deficit in another sequence converging to its limiting ceiling. -/
theorem nonnegative_tendsto_zero_of_subsequence_gap (a f : ℕ → ℝ) (L : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hf : Tendsto f atTop (𝓝 L))
    (hgap : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ lam > 0, (∀ j, lam ≤ a (φ j)) →
      ∃ δ > 0, ∀ᶠ j in atTop, f (φ j) ≤ L - δ) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    exact Eventually.of_forall (fun j => hl.trans_le (ha j))
  · intro lam hlam
    by_contra h
    have hfreq : ∃ᶠ j in atTop, lam ≤ a j := by
      simpa only [Filter.Frequently, not_le] using h
    obtain ⟨φ, hφ, hφa⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨δ, hδ, hd⟩ := hgap φ hφ lam hlam hφa
    have hle := le_of_tendsto (hf.comp hφ.tendsto_atTop) hd
    linarith

theorem cluster_scaled_cdf_sup_tendsto_of_raw_normalized_tendsto
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (C : ℝ)
    (hR : Tendsto (fun j => rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j)) atTop (𝓝 C)) :
    Tendsto (fun j => scaledSumCDFSup (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)) atTop
      (𝓝 (thirdMoment (standardizedBernoulliLaw p₀ hp₀) * C)) := by
  have hβ := standardizedTwoCluster_third_tendsto P Q p ε hp p₀ hp₀ hplim hε hεlim hP hQ
  apply (hβ.mul hR).congr'
  filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hj
  exact (cluster_scaledSumCDFSup_eq_third_mul_raw (P j) (Q j) (p j) (hp j) (n j) hj).symm

theorem accumulated_cluster_variance_tendsto_zero_of_open_parameters
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Ioo 0 1)
    (he : p₀ = pE ∨ p₀ = 1 - pE)
    (hplim : Tendsto p atTop (𝓝 p₀)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hR : Tendsto (fun j => rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j)) atTop (𝓝 cE)) :
    Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0) := by
  have hF := cluster_scaled_cdf_sup_tendsto_of_raw_normalized_tendsto P Q p ε hp p₀ hp₀
    hplim hε hεlim hP hQ n hn cE hR
  apply nonnegative_tendsto_zero_of_subsequence_gap _ _ _
    (fun j => accumulatedNoiseVariance_nonneg (P j) (Q j) (p j) ⟨(hp j).1.le, (hp j).2.le⟩ (n j)) hF
  intro φ hφ lam hlam hφlam
  obtain ⟨δ, hδ, hgap⟩ := general_cluster_strict_scaled_cdf_gap W S I
    (P ∘ φ) (Q ∘ φ) (p ∘ φ) (ε ∘ φ) (fun j => hp (φ j)) p₀ hp₀
    (hplim.comp hφ.tendsto_atTop) (fun j => hε (φ j)) (hεlim.comp hφ.tendsto_atTop)
    (fun j => hP (φ j)) (fun j => hQ (φ j)) (n ∘ φ) (hn.comp hφ.tendsto_atTop)
    lam hlam (Eventually.of_forall hφlam)
  refine ⟨δ, hδ, ?_⟩
  simpa only [Function.comp_apply, bernoulli_esseen_endpoint_peak_identity p₀ hp₀ he] using hgap

/-- The consequent of manuscript Lemma accumulated-cluster-variance, at both
Esseen parameters. All requirements on the initial finitely many indices are removed. -/
theorem accumulated_cluster_variance_tendsto_zero
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (p₀ : ℝ) (he : p₀ ∈ ({pE, 1 - pE} : Set ℝ))
    (hplim : Tendsto p atTop (𝓝 p₀)) (hεlim : Tendsto ε atTop (𝓝 0))
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hR : Tendsto (fun j => rawNormalizedConstant (twoClusterMeasure (P j) (Q j) (p j)) (n j)) atTop (𝓝 cE)) :
    Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0) := by
  have he' : p₀ = pE ∨ p₀ = 1 - pE := by simpa only [mem_insert_iff, mem_singleton_iff] using he
  have hp₀ : p₀ ∈ Ioo 0 1 := by
    rcases he' with rfl | rfl
    · exact ⟨pE_pos, pE_lt_half.trans (by norm_num)⟩
    · constructor <;> linarith [pE_pos, pE_lt_half]
  have hε : ∀ j, 0 ≤ ε j := by
    intro j
    obtain ⟨x, hx⟩ := (hP j).exists
    exact (abs_nonneg x).trans hx
  have hpe : ∀ᶠ j in atTop, p j ∈ Ioo 0 1 := hplim.eventually (isOpen_Ioo.mem_nhds hp₀)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hpe
  have hshift := tendsto_add_atTop_nat J
  apply (tendsto_add_atTop_iff_nat J).mp
  exact accumulated_cluster_variance_tendsto_zero_of_open_parameters W S I
    (fun j => P (j + J)) (fun j => Q (j + J)) (fun j => p (j + J)) (fun j => ε (j + J))
    (fun j => hJ (j + J) (by omega)) p₀ hp₀ he'
    (hplim.comp hshift) (fun j => hε (j + J)) (hεlim.comp hshift)
    (fun j => hP (j + J)) (fun j => hQ (j + J))
    (fun j => n (j + J)) (hn.comp hshift) (hR.comp hshift)

end BerryEsseen
