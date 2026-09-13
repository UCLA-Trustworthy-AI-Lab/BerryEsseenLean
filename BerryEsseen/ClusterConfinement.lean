import BerryEsseen.SupportSeparation
import BerryEsseen.SupportGeometry

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem weak_support_point_approximation (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 Q.toProbabilityMeasure))
    (K : Set ℝ) (hK : IsCompact K) (hbound : ∀ j, (P j).measure.support ⊆ K)
    (x : ℝ) (hx : x ∈ Q.measure.support) :
    ∃ v : ℕ → ℝ, (∀ j, v j ∈ (P j).measure.support) ∧ Tendsto v atTop (𝓝 x) := by
  have hex (j : ℕ) : ∃ v ∈ (P j).measure.support,
      IsMinOn (fun y : ℝ => dist y x) (P j).measure.support v := by
    exact (hK.of_isClosed_subset (P j).measure.isClosed_support (hbound j)).exists_isMinOn
      ((P j).measure.nonempty_support (IsProbabilityMeasure.ne_zero _)) (by fun_prop)
  choose v hv hmin using hex
  refine ⟨v, hv, Metric.tendsto_nhds.2 ?_⟩
  intro ε hε
  have hpos : 0 < Q.measure (Metric.ball x ε) :=
    (Measure.mem_support_iff_forall x).1 hx _ (Metric.ball_mem_nhds x hε)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hw (G := Metric.ball x ε) Metric.isOpen_ball
  change Q.measure (Metric.ball x ε) ≤ atTop.liminf (fun j => (P j).measure (Metric.ball x ε)) at hport
  filter_upwards [eventually_lt_of_lt_liminf (hpos.trans_le hport)] with j hj
  obtain ⟨y, hyball, hysupp⟩ := (P j).measure.nonempty_inter_support_of_pos hj
  exact (hmin j hysupp).trans_lt (Metric.mem_ball.1 hyball)

theorem esseen_two_atom_geometry (y : ℝ)
    (hI : y ∈ Icc (-(Real.sqrt 10 / 2 * aE)) (Real.sqrt 10 / 2 * bE))
    (hA : y = -aE ∨ hE ≤ |y - (-aE)|) (hB : y = bE ∨ hE ≤ |y - bE|) :
    y = -aE ∨ y = bE := by
  let r := pE + sigmaE * y
  have hsa : sigmaE * aE = pE := by unfold aE; field_simp [sigmaE_pos.ne']
  have hsb : sigmaE * bE = qE := by unfold bE; field_simp [sigmaE_pos.ne']
  have hsh : sigmaE * hE = 1 := by unfold hE; field_simp [sigmaE_pos.ne']
  have hl := mul_le_mul_of_nonneg_left hI.1 sigmaE_pos.le
  have hu := mul_le_mul_of_nonneg_left hI.2 sigmaE_pos.le
  have hea : sigmaE * (Real.sqrt 10 / 2 * aE) = Real.sqrt 10 / 2 * pE := by
    calc _ = Real.sqrt 10 / 2 * (sigmaE * aE) := by ring
         _ = _ := by rw [hsa]
  have heb : sigmaE * (Real.sqrt 10 / 2 * bE) = Real.sqrt 10 / 2 * qE := by
    calc _ = Real.sqrt 10 / 2 * (sigmaE * bE) := by ring
         _ = _ := by rw [hsb]
  rw [mul_neg, hea] at hl
  rw [heb] at hu
  have hlo : -1 < r := by dsimp [r]; linarith [affine_endpoints_inside.1]
  have hhi : r < 2 := by dsimp [r]; linarith [affine_endpoints_inside.2]
  have hrA : r = sigmaE * (y - (-aE)) := by dsimp [r]; nlinarith [hsa]
  have hrB : r - 1 = sigmaE * (y - bE) := by dsimp [r]; nlinarith [hsb, pE_add_qE]
  have hzero : r = 0 ∨ 1 ≤ |r| := by
    rcases hA with hA | hA
    · left
      rw [hrA, hA, sub_self, mul_zero]
    · right
      have ht := mul_le_mul_of_nonneg_left hA sigmaE_pos.le
      rw [hsh] at ht
      simpa only [hrA, abs_mul, abs_of_pos sigmaE_pos] using ht
  have hone : r = 1 ∨ 1 ≤ |r - 1| := by
    rcases hB with hB | hB
    · left
      have ht : r - 1 = 0 := by rw [hrB, hB, sub_self, mul_zero]
      linarith
    · right
      have ht := mul_le_mul_of_nonneg_left hB sigmaE_pos.le
      rw [hsh] at ht
      simpa only [hrB, abs_mul, abs_of_pos sigmaE_pos] using ht
  rcases two_atom_geometry r hlo hhi hzero hone with hr | hr
  · left
    apply (mul_left_cancel₀ sigmaE_pos.ne')
    rw [mul_neg, hsa]
    dsimp [r] at hr
    linarith
  · right
    apply (mul_left_cancel₀ sigmaE_pos.ne')
    rw [hsb]
    dsimp [r] at hr
    linarith [pE_add_qE]

theorem extremizer_support_limits_are_atoms
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (v : ℕ → ℝ) (y : ℝ) (hvsupp : ∀ j, v j ∈ (P j).measure.support)
    (hy : Tendsto v atTop (𝓝 y)) : y = -aE ∨ y = bE := by
  have hI := extremizer_support_limit_interval H P n t hn (fun j => by have := hn2 j; omega)
    hattain hv hd hw hz hsupp v y hvsupp hy
  have ha : -aE ∈ esseenLaw.measure.support := by change -aE ∈ esseenMeasure.support; rw [esseen_support]; simp
  have hb : bE ∈ esseenLaw.measure.support := by change bE ∈ esseenMeasure.support; rw [esseen_support]; simp
  obtain ⟨va, hvasupp, hva⟩ := weak_support_point_approximation P esseenLaw hw (Icc (-10) 10) isCompact_Icc hsupp (-aE) ha
  obtain ⟨vb, hvbsupp, hvb⟩ := weak_support_point_approximation P esseenLaw hw (Icc (-10) 10) isCompact_Icc hsupp bE hb
  exact esseen_two_atom_geometry y hI
    (extremizer_support_limit_separation H W S P n t hn hn2 hattain hv hw hz hsupp v va y (-aE) hvsupp hvasupp hy hva)
    (extremizer_support_limit_separation H W S P n t hn hn2 hattain hv hw hz hsupp v vb y bE hvsupp hvbsupp hy hvb)

theorem extremizer_uniform_two_cluster_confinement
    (H : ClassicalBerryEsseenBounds) (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw) (n : ℕ → ℕ) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hattain : ∀ j, signedRatio (P j) (n j) (t j) = extremalConstant (n j + 1))
    (hv : ∀ j, cE < extremalConstant (n j + 1))
    (hd : Tendsto (fun j => scaledDrop extremalConstant (n j + 1)) atTop (𝓝 0))
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure))
    (hz : Tendsto (fun j => t j / Real.sqrt (n j + 1 : ℝ)) atTop (𝓝 0))
    (hsupp : ∀ j, (P j).measure.support ⊆ Icc (-10) 10)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j in atTop, (P j).measure.support ⊆
      Ioo (-aE - η) (-aE + η) ∪ Ioo (bE - η) (bE + η) := by
  apply uniform_confinement (fun j => (P j).measure.support) (Icc (-10) 10) {-aE, bE}
    isCompact_Icc hsupp
  · intro u hu v hvsupp y hy
    have hlim := extremizer_support_limits_are_atoms H W S (P ∘ u) (n ∘ u) (t ∘ u)
      (hn.comp hu.tendsto_atTop) (fun j => hn2 _) (fun j => hattain _) (fun j => hv _)
      (hd.comp hu.tendsto_atTop) (hw.comp hu.tendsto_atTop) (hz.comp hu.tendsto_atTop)
      (fun j => hsupp _) v y hvsupp hy
    simpa only [mem_insert_iff, mem_singleton_iff] using hlim
  · exact isOpen_Ioo.union isOpen_Ioo
  · intro x hx
    rcases mem_insert_iff.1 hx with rfl | hx
    · exact Or.inl ⟨by linarith, by linarith⟩
    · rw [mem_singleton_iff.1 hx]
      exact Or.inr ⟨by linarith, by linarith⟩

theorem esseen_upper_cluster_mass : esseenLaw.measure (Ioi 0) = ENNReal.ofReal pE := by
  change esseenMeasure (Ioi 0) = _
  have ha : ¬ (0 : ℝ) < -aE := by linarith [aE_pos]
  simp [esseenMeasure, Measure.dirac_apply', ha, bE_pos]

theorem weak_esseen_upper_cluster_mass_tendsto (P : ℕ → StandardizedLaw)
    (hw : Tendsto (fun j => (P j).toProbabilityMeasure) atTop (𝓝 esseenLaw.toProbabilityMeasure)) :
    Tendsto (fun j => ((P j).measure (Ioi 0)).toReal) atTop (𝓝 pE) := by
  have hzero : esseenLaw.measure (frontier (Ioi (0 : ℝ))) = 0 := by
    rw [frontier_Ioi]
    change esseenMeasure {0} = 0
    have ha : -aE ≠ 0 := by linarith [aE_pos]
    have hb : bE ≠ 0 := bE_pos.ne'
    simp [esseenMeasure, Measure.dirac_apply', ha, hb]
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw hzero
  change Tendsto (fun j => (P j).measure (Ioi 0)) atTop (𝓝 (esseenLaw.measure (Ioi 0))) at hm
  rw [esseen_upper_cluster_mass] at hm
  have ht := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hm
  simpa only [Function.comp_def, ENNReal.toReal_ofReal pE_pos.le] using ht

end BerryEsseen
