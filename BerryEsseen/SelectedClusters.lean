import BerryEsseen.SelectedExtremizers
import BerryEsseen.SmallVarianceSequence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem esseen_upper_mass_at (x : ℝ) (hx : x ∈ Ioo (-aE) bE) :
    esseenLaw.measure (Ioi x) = ENNReal.ofReal pE := by
  change esseenMeasure (Ioi x) = _
  have ha : ¬ x < -aE := not_lt_of_ge hx.1.le
  simp [esseenMeasure, Measure.dirac_apply', ha, hx.2]

theorem weak_esseen_halfline_mass_tendsto (P : ℕ → StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (x : ℝ) (hx : x ∈ Ioo (-aE) bE) :
    Tendsto (fun j => (P j).measure.real (Ioi x)) atTop (𝓝 pE) := by
  have hzero : esseenLaw.measure (frontier (Ioi x)) = 0 := by
    rw [frontier_Ioi]
    change esseenMeasure {x} = 0
    have ha : -aE ≠ x := ne_of_lt hx.1
    have hb : bE ≠ x := ne_of_gt hx.2
    simp [esseenMeasure, Measure.dirac_apply', ha, hb]
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw hzero
  change Tendsto (fun j => (P j).measure (Ioi x)) atTop (𝓝 (esseenLaw.measure (Ioi x))) at hm
  rw [esseen_upper_mass_at x hx] at hm
  have ht := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hm
  simpa only [Measure.real, Function.comp_apply, ENNReal.toReal_ofReal pE_pos.le] using ht

def SelectedExtremizers.reindex (X : SelectedExtremizers) (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) : SelectedExtremizers where
  P := X.P ∘ f
  n := X.n ∘ f
  t := X.t ∘ f
  n_tendsto := X.n_tendsto.comp hf
  n_ge_two := fun j => X.n_ge_two (f j)
  attain := fun j => X.attain (f j)
  violate := fun j => X.violate (f j)
  drop := X.drop.comp hf
  weak := X.weak.comp hf
  threshold := X.threshold.comp hf
  support := fun j => X.support (f j)

def shrinkingClusterRadius (j : ℕ) : ℝ := (hE / 100) / ((j : ℝ) + 1)

theorem shrinkingClusterRadius_pos (j : ℕ) : 0 < shrinkingClusterRadius j := by
  have := hE_pos
  unfold shrinkingClusterRadius
  positivity

theorem shrinkingClusterRadius_le (j : ℕ) : shrinkingClusterRadius j ≤ hE / 100 := by
  unfold shrinkingClusterRadius
  apply (div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) j, mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hE_pos.le]

theorem shrinkingClusterRadius_tendsto : Tendsto shrinkingClusterRadius atTop (𝓝 0) :=
  (tendsto_const_nhds (x := hE / 100)).div_atTop
    ((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))

theorem selected_extremizers_with_shrinking_clusters (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (X : SelectedExtremizers) :
    ∃ Y : SelectedExtremizers, (∀ j, (Y.P j).measure.support ⊆
      Icc (-aE - shrinkingClusterRadius j) (-aE + shrinkingClusterRadius j) ∪
      Icc (bE - shrinkingClusterRadius j) (bE + shrinkingClusterRadius j)) ∧
      ∀ j, (Y.P j).measure.real (Ioi ((-aE + bE) / 2)) ∈ Icc (2 / 5) (3 / 5) := by
  have hmid : (-aE + bE) / 2 ∈ Ioo (-aE) bE := by
    constructor <;> linarith [aE_pos, bE_pos]
  have hplim := weak_esseen_halfline_mass_tendsto X.P X.weak _ hmid
  have hp : ∀ᶠ j in atTop, (X.P j).measure.real (Ioi ((-aE + bE) / 2)) ∈ Icc (2 / 5) (3 / 5) := by
    filter_upwards [hplim.eventually (lt_mem_nhds pE_bounds.1),
      hplim.eventually (gt_mem_nhds (by linarith [pE_bounds.2] : pE < 3 / 5))] with j hj hk
    exact ⟨hj.le, hk.le⟩
  have hex (j : ℕ) : ∃ i : ℕ, j ≤ i ∧ (X.P i).measure.support ⊆
      Ioo (-aE - shrinkingClusterRadius j) (-aE + shrinkingClusterRadius j) ∪
      Ioo (bE - shrinkingClusterRadius j) (bE + shrinkingClusterRadius j) ∧
      (X.P i).measure.real (Ioi ((-aE + bE) / 2)) ∈ Icc (2 / 5) (3 / 5) := by
    have hev := (eventually_ge_atTop j).and ((X.confined H W S _ (shrinkingClusterRadius_pos j)).and hp)
    exact hev.exists
  choose f hf hconf hprob using hex
  have hfTendsto : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  refine ⟨X.reindex f hfTendsto, ?_, ?_⟩
  · intro j x hx
    rcases hconf j hx with hx | hx
    · exact Or.inl ⟨hx.1.le, hx.2.le⟩
    · exact Or.inr ⟨hx.1.le, hx.2.le⟩
  · exact hprob

end BerryEsseen
