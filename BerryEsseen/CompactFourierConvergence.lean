import BerryEsseen.CharacteristicCurvature
import BerryEsseen.ManuscriptGeneralCompactCoupling
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Compact uniform convergence of q and q'' for weakly convergent standardized
laws with uniformly bounded third moments. No fourth moments are assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem uniform_on_compact_of_common_lipschitz (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (C : NNReal)
    (hLip : ∀ j, LipschitzWith C (f j))
    (hpoint : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 (g x)))
    (K : Set ℝ) (hK : IsCompact K) : TendstoUniformlyOn f g atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let F : ℕ → K → ℝ := fun j x => f j x
  let G : K → ℝ := fun x => g x
  have hFL : ∀ j, LipschitzWith C (F j) := by
    intro j
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hLip j).dist_le_mul x.val y.val
  have heq : Equicontinuous F := (LipschitzWith.uniformEquicontinuous F C hFL).equicontinuous
  have hp : Tendsto F atTop (𝓝 G) := tendsto_pi_nhds.2 (fun x => hpoint x)
  have hu := (heq.tendsto_uniformFun_iff_pi atTop G).2 hp
  have hU := UniformFun.tendsto_iff_tendstoUniformly.1 hu
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.2 hU

theorem compact_characteristicSquare_convergence (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun j => characteristicSquare (P j)) (characteristicSquare Q) atTop K :=
  manuscript_compact_square_from_wassersteinThree P Q hW3 K hK

theorem compact_characteristicSquareCurvature_convergence (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hW3 : Tendsto (fun j => wassersteinThree (P j).measure Q.measure) atTop (𝓝 0))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun j => characteristicSquareCurvature (P j))
      (characteristicSquareCurvature Q) atTop K :=
  manuscript_compact_curvature_from_wassersteinThree P Q hW3 K hK

end BerryEsseen
