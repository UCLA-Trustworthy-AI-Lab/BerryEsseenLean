import BerryEsseen.RepresentedVariance
import BerryEsseen.CentralRounding
import BerryEsseen.MainReduction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem represented_selected_extremizers_impossible (H : ClassicalBerryEsseenBounds)
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound)
    (R : RepresentedSelectedExtremizers) : False := by
  let m := fun j => R.X.n j + 1
  let σ := fun j => Real.sqrt (clusterVariance (R.lower j) (R.upper j) (R.p j))
  let T := fun j => σ j * R.X.t j + (m j : ℝ) * R.p j
  let k := fun j => centralRoundedCell (m j) (T j)
  have hm : Tendsto m atTop atTop := (tendsto_add_atTop_nat 1).comp R.X.n_tendsto
  have hm2 : ∀ j, 2 ≤ m j := fun j => by have := R.X.n_ge_two j; dsimp only [m]; omega
  have hm1 : ∀ j, 1 ≤ m j := fun j => by have := hm2 j; omega
  have hT : Tendsto (fun j => (T j - (m j : ℝ) * R.p j) / Real.sqrt (m j : ℝ)) atTop (𝓝 0) := by
    have h := R.scale_tendsto.mul R.X.threshold
    simpa only [T, m, σ, add_sub_cancel_right, mul_div_assoc, mul_zero, Nat.cast_add, Nat.cast_one] using h
  have hround := central_rounding_sequence R.p R.p_central R.p_tendsto m hm hm1 T hT
  have hbound := small_variance_central_sequence W S B R.lower R.upper R.p R.epsilon R.p_open R.p_central R.p_tendsto
    R.epsilon_nonneg R.epsilon_tendsto R.epsilon_le_p R.epsilon_le_q R.noise_lower R.noise_upper m hm hm2
    (R.successor_accumulated_noise_tendsto H W S B I) k (fun j => centralRoundedCell_le (m j) (T j)) hround.2
  obtain ⟨j, hjbound, hjround⟩ := (hbound.and hround.1).exists
  have hD := hjbound (T j - (k j : ℝ)) hjround
  have hσ : 0 < σ j := Real.sqrt_pos.2 (clusterVariance_pos _ _ _ (R.p_open j))
  have hr : 0 < Real.sqrt (m j : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < m j by have := hm1 j; omega))
  have he : (((k j : ℝ) + (T j - (k j : ℝ)) - (m j : ℝ) * R.p j) /
      Real.sqrt ((m j : ℝ) * clusterVariance (R.lower j) (R.upper j) (R.p j))) =
      R.X.t j / Real.sqrt (m j : ℝ) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    change ((k j : ℝ) + (σ j * R.X.t j + (m j : ℝ) * R.p j - (k j : ℝ)) - (m j : ℝ) * R.p j) /
      (Real.sqrt (m j : ℝ) * σ j) = R.X.t j / Real.sqrt (m j : ℝ)
    field_simp [hσ.ne', hr.ne']
    ring
  rw [he, R.law_eq j] at hD
  simp only [m, Nat.cast_add, Nat.cast_one] at hD
  rw [← abs_signedRatio_eq_normalized] at hD
  have hv := R.X.violate j
  rw [← R.X.attain j] at hv
  exact (not_le_of_gt (hv.trans_le (le_abs_self _))) hD

/-- Existence of a universal finite threshold for the Esseen bound. Only the
explicitly cited published inputs are premises; no manuscript local lemma is
assumed. This theorem does not supply the appendix's explicit threshold. -/
theorem main_theorem (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (E : PublishedEsseenMoment) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) : MainClaim := by
  classical
  by_contra hmain
  obtain ⟨R⟩ := exists_representedSelected_of_not_main H W S E hmain
  exact represented_selected_extremizers_impossible H W S B I R

/-- The standardized local stability conclusion follows as a corollary of the
independently proved global theorem. It is not an input to main_theorem. -/
theorem standardized_two_cluster_stability (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (E : PublishedEsseenMoment) (B : PublishedBernoulliBound) (I : PublishedNonIIDBound) :
    StandardizedTwoClusterStability := by
  obtain ⟨N, hN, hbound⟩ := main_theorem H W S E B I
  exact ⟨1, by norm_num, N, fun n hn P _ _ => hbound n hn P⟩

end BerryEsseen
