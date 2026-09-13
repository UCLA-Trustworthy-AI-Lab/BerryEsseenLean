import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptFarSequence
import BerryEsseen.ManuscriptCentralInteger
import BerryEsseen.SmallVarianceNeighborhood

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

/-- The actual Bernoulli supremum equals the prefactor used in the original
central comparison. This identity contains no stability estimate. -/
theorem manuscript_raw_bernoulli_prefactor (p : ℝ) (hp : p ∈ Ioo 0 1)
    (n : ℕ) (hn : 1 ≤ n) :
    rawNormalizedConstant (bernoulliMeasure p) n =
      Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 /
        (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) * binomialKolmogorov p n := by
  rw [rawNormalizedConstant_bernoulli p hp n hn, binomialNormalizedConstant,
    manuscript_binomial_prefactor p hp n,
    mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

/-- Sequential compactness bridge for the original Lemma 3.3. The Bernoulli
limit is an explicit intermediate premise to be supplied by its proved
binomial asymptotic theorem; no new external or published result is asserted.
Bounded standardized cells use the central loss, while escaping cells use
the ordinary binomial envelope tail. -/
theorem manuscript_small_variance_bad_sequence_impossible
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : ℕ → CenteredFourthLaw) (p ε : ℕ → ℝ)
    (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hplim : Tendsto p atTop (𝓝 pE)) (hε : ∀ j, 0 ≤ ε j) (hεlim : Tendsto ε atTop (𝓝 0))
    (hεp : ∀ j, ε j ≤ p j) (hεq : ∀ j, ε j ≤ 1 - p j)
    (hP : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ ε j)
    (hQ : ∀ j, ∀ᵐ x ∂(Q j).measure, |x| ≤ ε j)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hlam : Tendsto (fun j => accumulatedNoiseVariance (P j) (Q j) (p j) (n j)) atTop (𝓝 0))
    (hlampos : ∀ j, 0 < accumulatedNoiseVariance (P j) (Q j) (p j) (n j))
    (hRb : Tendsto (fun j => rawNormalizedConstant (bernoulliMeasure (p j)) (n j)) atTop (𝓝 cE))
    (k : ℕ → ℤ) (u d : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 1 / 2)
    (hdpos : ∀ j, 0 < d j) (hdlim : Tendsto d atTop (𝓝 0))
    (hbad : ∀ j,
      rawNormalizedConstant (bernoulliMeasure (p j)) (n j) -
        min (d j * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) /
          Real.sqrt (3 * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) / (2 / 5) + (ε j) ^ 2)) (d j) <
      normalizedDiscrepancy (standardizedTwoClusterLaw (P j) (Q j) (p j) (hp j)) (n j)
        (((k j : ℝ) + u j - (n j : ℝ) * p j) /
          Real.sqrt ((n j : ℝ) * clusterVariance (P j) (Q j) (p j)))) : False := by
  let z := fun j => binomialZ (p j) (n j) (k j)
  have hn1 : ∀ j, 1 ≤ n j := fun j => by have := hn2 j; omega
  by_cases hbounded : ∃ M : ℝ, ∃ᶠ j in atTop, |z j| ≤ M
  · obtain ⟨M, hM⟩ := hbounded
    have hMf : ∃ᶠ j in atTop, z j ∈ Icc (-M) M := hM.mono (fun _ hj => abs_le.mp hj)
    obtain ⟨z₀, hz₀, φ, hφ, hz⟩ :=
      (isCompact_Icc : IsCompact (Icc (-M) M)).isSeqCompact.subseq_of_frequently_in hMf
    have hφtop := hφ.tendsto_atTop
    obtain ⟨c, hc, hbound⟩ := manuscript_small_variance_central_integer_sequence W S B
      (P ∘ φ) (Q ∘ φ) (p ∘ φ) (ε ∘ φ) (fun j => hp (φ j)) (fun j => hcentral (φ j))
      (hplim.comp hφtop) (fun j => hε (φ j)) (hεlim.comp hφtop)
      (fun j => hεp (φ j)) (fun j => hεq (φ j))
      (fun j => hP (φ j)) (fun j => hQ (φ j)) (n ∘ φ) (hn.comp hφtop)
      (fun j => hn2 (φ j)) (hlam.comp hφtop) (fun j => hlampos (φ j)) (k ∘ φ) z₀ hz
    obtain ⟨j, hjbound, hjd⟩ := (hbound.and ((hdlim.comp hφtop).eventually (gt_mem_nhds hc))).exists
    have hgood := hjbound (u (φ j)) (hu (φ j))
    simp only [Function.comp_apply] at hgood hjd
    rw [← manuscript_raw_bernoulli_prefactor (p (φ j)) (hp (φ j)) (n (φ j)) (hn1 (φ j))] at hgood
    have hmul := mul_le_mul_of_nonneg_right hjd.le (hlampos (φ j)).le
    have hdiv := div_le_div_of_nonneg_right hmul
      (Real.sqrt_nonneg (3 * accumulatedNoiseVariance (P (φ j)) (Q (φ j)) (p (φ j)) (n (φ j)) /
        (2 / 5) + ε (φ j) ^ 2))
    have hmin := (min_le_left
      (d (φ j) * accumulatedNoiseVariance (P (φ j)) (Q (φ j)) (p (φ j)) (n (φ j)) /
        Real.sqrt (3 * accumulatedNoiseVariance (P (φ j)) (Q (φ j)) (p (φ j)) (n (φ j)) / (2 / 5) + ε (φ j) ^ 2))
      (d (φ j))).trans hdiv
    have hbadj := hbad (φ j)
    linarith
  · have hzfar : Tendsto (fun j => |z j|) atTop atTop := by
      apply tendsto_atTop.2
      intro M
      have hnot : ¬ ∃ᶠ j in atTop, |z j| ≤ M := fun h => hbounded ⟨M, h⟩
      filter_upwards [not_frequently.mp hnot] with j hj
      exact (lt_of_not_ge hj).le
    obtain ⟨γ, hγ, hfar⟩ := manuscript_twoCluster_far_sequence W S B P Q p ε hp hcentral hplim hε hεlim
      hεp hεq hP hQ n hn hn2 hlam k hzfar
    obtain ⟨j, hjfar, hjRb, hjd⟩ :=
      (hfar.and ((hRb.eventually (lt_mem_nhds (show cE - γ / 2 < cE by linarith))).and
        (hdlim.eventually (gt_mem_nhds (show (0 : ℝ) < γ / 2 by linarith))))).exists
    have hgood := hjfar (u j) (hu j)
    have hmin := min_le_right
      (d j * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) /
        Real.sqrt (3 * accumulatedNoiseVariance (P j) (Q j) (p j) (n j) / (2 / 5) + ε j ^ 2)) (d j)
    have hbadj := hbad j
    linarith

end BerryEsseen
