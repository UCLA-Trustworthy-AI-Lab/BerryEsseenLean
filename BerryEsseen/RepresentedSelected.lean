import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.SelectedClusters
import BerryEsseen.ClusterRepresentation
import BerryEsseen.TwoClusterLocalMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

structure RepresentedSelectedExtremizers where
  X : SelectedExtremizers
  lower : ℕ → CenteredFourthLaw
  upper : ℕ → CenteredFourthLaw
  p : ℕ → ℝ
  epsilon : ℕ → ℝ
  p_open : ∀ j, p j ∈ Ioo 0 1
  p_central : ∀ j, p j ∈ Icc (2 / 5) (3 / 5)
  p_tendsto : Tendsto p atTop (𝓝 pE)
  epsilon_nonneg : ∀ j, 0 ≤ epsilon j
  epsilon_tendsto : Tendsto epsilon atTop (𝓝 0)
  epsilon_le_p : ∀ j, epsilon j ≤ p j
  epsilon_le_q : ∀ j, epsilon j ≤ 1 - p j
  noise_lower : ∀ j, ∀ᵐ x ∂(lower j).measure, |x| ≤ epsilon j
  noise_upper : ∀ j, ∀ᵐ x ∂(upper j).measure, |x| ≤ epsilon j
  law_eq : ∀ j, standardizedTwoClusterLaw (lower j) (upper j) (p j) (p_open j) = X.P j

theorem represented_selected_extremizers (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (X : SelectedExtremizers) : Nonempty RepresentedSelectedExtremizers := by
  obtain ⟨Y, hconf, hprob⟩ := selected_extremizers_with_shrinking_clusters H W S X
  let p := fun j => (Y.P j).measure.real (Ioi ((-aE + bE) / 2))
  have hp : ∀ j, p j ∈ Ioo 0 1 := by
    intro j
    have h := hprob j
    constructor <;> dsimp only [p] <;> linarith [h.1, h.2]
  have hspan : bE - -aE = hE := by linarith [span_identity]
  have hgap (j : ℕ) : 2 * shrinkingClusterRadius j < bE - -aE := by
    rw [hspan]
    have h := shrinkingClusterRadius_le j
    linarith [hE_pos]
  have hex (j : ℕ) := standardized_two_cluster_representation (Y.P j) (-aE) bE (shrinkingClusterRadius j)
    (shrinkingClusterRadius_pos j).le (hgap j) (by
      filter_upwards [(Y.P j).measure.support_mem_ae] with x hx
      exact hconf j hx) (hp j)
  choose P Q d hd hdb hP hQ hLaw using hex
  let ε := fun j => 2 * shrinkingClusterRadius j / d j
  have hε0 : ∀ j, 0 ≤ ε j := by intro j; exact div_nonneg (mul_nonneg (by norm_num) (shrinkingClusterRadius_pos j).le) (hd j).le
  have hdlo : ∀ j, hE / 2 ≤ d j := by
    intro j
    have h := (hdb j).1
    rw [hspan] at h
    have hh := shrinkingClusterRadius_le j
    linarith [hE_pos]
  have hεbound : ∀ j, ε j ≤ 4 * shrinkingClusterRadius j / hE := by
    intro j
    have hh := div_le_div₀ (by have := shrinkingClusterRadius_pos j; positivity : 0 ≤ 2 * shrinkingClusterRadius j)
      (le_refl (2 * shrinkingClusterRadius j)) (by have := hE_pos; positivity : 0 < hE / 2) (hdlo j)
    change ε j ≤ 2 * shrinkingClusterRadius j / (hE / 2) at hh
    convert hh using 1 <;> ring
  have hεlim : Tendsto ε atTop (𝓝 0) := squeeze_zero hε0 hεbound (by
    simpa only [mul_zero, zero_div] using (shrinkingClusterRadius_tendsto.const_mul 4).div_const hE)
  have hεsmall : ∀ j, ε j ≤ 1 / 25 := by
    intro j
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (shrinkingClusterRadius_le j) (by norm_num : (0 : ℝ) ≤ 4)) hE_pos.le
    have he : 4 * (hE / 100) / hE = (1 / 25 : ℝ) := by field_simp [hE_pos.ne']; norm_num
    rw [he] at h
    exact (hεbound j).trans h
  refine ⟨{
    X := Y
    lower := P
    upper := Q
    p := p
    epsilon := ε
    p_open := hp
    p_central := hprob
    p_tendsto := weak_esseen_halfline_mass_tendsto Y.P Y.weak _ (by constructor <;> linarith [aE_pos, bE_pos])
    epsilon_nonneg := hε0
    epsilon_tendsto := hεlim
    epsilon_le_p := ?_
    epsilon_le_q := ?_
    noise_lower := hP
    noise_upper := hQ
    law_eq := hLaw
  }⟩
  · intro j
    have h := (hprob j).1
    have hε := hεsmall j
    dsimp only [p]
    linarith
  · intro j
    have h := (hprob j).2
    have hε := hεsmall j
    dsimp only [p]
    linarith

theorem exists_representedSelected_of_not_main (H : ClassicalBerryEsseenBounds)
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (hmain : ¬ MainClaim) :
    Nonempty RepresentedSelectedExtremizers := by
  obtain ⟨X⟩ := exists_selectedExtremizers_of_not_main H W S E hmain
  exact represented_selected_extremizers H W S X

end BerryEsseen
