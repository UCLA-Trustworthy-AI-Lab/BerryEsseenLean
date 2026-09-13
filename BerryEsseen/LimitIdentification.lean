import BerryEsseen.PublishedEsseenMoment
import BerryEsseen.EsseenEnvelopes
import BerryEsseen.LimitEnvelopes

/-! Actual measure, envelope and limit arguments for Esseen extremizers. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

theorem bounded_violation_limit_esseen_or_reflection
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Filter.Tendsto (fun j => (P j).toProbabilityMeasure) Filter.atTop (nhds Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Filter.Tendsto n Filter.atTop Filter.atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : IsMaximalSpan Q h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (z : ℕ → ℝ) (hviol : ∀ j, cE * thirdMoment (P j) ≤
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) (z j) - normalCDF (z j))) :
    Q.measure = esseenLaw.measure ∨ Q.measure = (reflectedLaw esseenLaw).measure := by
  have hl := bounded_violation_limit_moment_lower W S P Q hw hβ hb n hn hn2 h hh.1 hzero z hviol
  have hu := esseen_absolute_moment_bound E Q h hh
  apply esseen_absolute_moment_equality E Q h hh
  apply le_antisymm hu
  rw [cE_eq] at hl
  nlinarith [phi0_pos]

theorem esseen_classification_of_sharp_lower (E : PublishedEsseenMoment)
    (Q : StandardizedLaw) (h : ℝ) (hh : IsMaximalSpan Q h)
    (hl : cE * thirdMoment Q ≤ (h / 2 + |signedThirdMoment Q| / 6) * phi0) :
    (Q = esseenLaw ∨ Q = reflectedLaw esseenLaw) ∧ h = hE := by
  have hu := esseen_absolute_moment_bound E Q h hh
  have heq : |signedThirdMoment Q| + 3 * h = cStar * thirdMoment Q := by
    apply le_antisymm hu
    rw [cE_eq] at hl
    nlinarith [phi0_pos]
  rcases esseen_absolute_moment_equality E Q h hh heq with hQ | hQ
  · have he := standardizedLaw_eq_of_measure_eq Q esseenLaw hQ
    subst Q
    rw [thirdMoment_esseen, signedThirdMoment_esseen, abs_of_pos kappaE_pos] at heq
    exact ⟨Or.inl rfl, by linarith [esseen_moment_span_identity]⟩
  · have he := standardizedLaw_eq_of_measure_eq Q (reflectedLaw esseenLaw) hQ
    subst Q
    rw [reflectedLaw_thirdMoment, reflectedLaw_signedThirdMoment, thirdMoment_esseen,
      signedThirdMoment_esseen, abs_neg, abs_of_pos kappaE_pos] at heq
    exact ⟨Or.inr rfl, by linarith [esseen_moment_span_identity]⟩

theorem bounded_violation_limit_esseen
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Filter.Tendsto (fun j => (P j).toProbabilityMeasure) Filter.atTop (nhds Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Filter.Tendsto n Filter.atTop Filter.atTop) (hn2 : ∀ j, 2 ≤ n j)
    (h : ℝ) (hh : IsMaximalSpan Q h)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup Q.measure → Real.sinc (h * r / 2) = 0)
    (z : ℕ → ℝ) (hviol : ∀ j, cE * thirdMoment (P j) ≤
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) (z j) - normalCDF (z j))) :
    Q = esseenLaw ∧ h = hE := by
  have hl := bounded_violation_limit_moment_lower W S P Q hw hβ hb n hn hn2 h hh.1 hzero z hviol
  obtain ⟨hclass, he⟩ := esseen_classification_of_sharp_lower E Q h hh hl
  refine ⟨?_, he⟩
  rcases hclass with hQ | hQ
  · exact hQ
  · exfalso
    subst Q
    subst h
    let δ : ℝ := kappaE / 3 * phi0
    have hδ : 0 < δ := mul_pos (div_pos kappaE_pos (by norm_num)) phi0_pos
    have hlim : Filter.Tendsto (fun j => cE * thirdMoment (P j)) Filter.atTop (nhds (cE * betaE)) := by
      simpa only [reflectedLaw_thirdMoment, thirdMoment_esseen] using
        (bounded_thirdMoment_tendsto P (reflectedLaw esseenLaw) hw 10 (by norm_num) hb).const_mul cE
    have hbad : cE * betaE ≤ cE * betaE - δ + δ / 2 := by
      apply le_of_tendsto hlim
      filter_upwards [bounded_jitter_limit_envelopes W S P (reflectedLaw esseenLaw) hw hβ hb n hn hn2
        hE hE_pos.le hzero (δ / 2) (by linarith)] with j hj
      have hu := (hj (z j)).2
      rw [reflectedLaw_signedThirdMoment, signedThirdMoment_esseen] at hu
      exact (hviol j).trans (hu.trans (add_le_add (reflected_esseen_envelope_gap (z j)) le_rfl))
    linarith

theorem bounded_violation_threshold_tendsto_zero
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (P : ℕ → StandardizedLaw)
    (hw : Filter.Tendsto (fun j => (P j).toProbabilityMeasure) Filter.atTop (nhds esseenLaw.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Filter.Tendsto n Filter.atTop Filter.atTop) (hn2 : ∀ j, 2 ≤ n j)
    (hzero : ∀ r, r ≠ 0 → r ∈ resonanceSubgroup esseenLaw.measure → Real.sinc (hE * r / 2) = 0)
    (z : ℕ → ℝ) (hviol : ∀ j, cE * thirdMoment (P j) ≤
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) (z j) - normalCDF (z j))) :
    Filter.Tendsto z Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun j => cE * thirdMoment (P j)) Filter.atTop (nhds (cE * betaE)) := by
    simpa only [thirdMoment_esseen] using
      (bounded_thirdMoment_tendsto P esseenLaw hw 10 (by norm_num) hb).const_mul cE
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : ℝ := cE * betaE * (1 - Real.exp (-ε ^ 2 / 2))
  have hbpos : 0 < betaE := by rw [← thirdMoment_esseen]; exact thirdMoment_pos _
  have he : Real.exp (-ε ^ 2 / 2) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [sq_pos_of_pos hε])
  have hδ : 0 < δ := mul_pos (mul_pos cE_pos hbpos) (by linarith)
  have hclose := hlim.eventually (lt_mem_nhds (by linarith : cE * betaE - δ / 3 < cE * betaE))
  filter_upwards [hclose, bounded_jitter_limit_envelopes W S P esseenLaw hw hβ hb n hn hn2
    hE hE_pos.le hzero (δ / 3) (by linarith)] with j hj hjenv
  rw [Real.dist_eq, sub_zero]
  by_contra hx
  have haway := positive_esseen_envelope_away ε (z j) hε.le (le_of_not_gt hx)
  have hu := (hjenv (z j)).2
  rw [signedThirdMoment_esseen] at hu
  have hlow := hviol j
  dsimp [δ] at *
  nlinarith

theorem bounded_violation_limit_identification
    (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment)
    (P : ℕ → StandardizedLaw) (Q : StandardizedLaw)
    (hw : Filter.Tendsto (fun j => (P j).toProbabilityMeasure) Filter.atTop (nhds Q.toProbabilityMeasure))
    (hβ : ∀ j, thirdMoment (P j) ≤ 2) (hb : ∀ j, ∀ᵐ x ∂(P j).measure, |x| ≤ 10)
    (n : ℕ → ℕ) (hn : Filter.Tendsto n Filter.atTop Filter.atTop) (hn2 : ∀ j, 2 ≤ n j)
    (z : ℕ → ℝ) (hviol : ∀ j, cE * thirdMoment (P j) ≤
      Real.sqrt (n j : ℝ) * (normalizedSumCDF (P j) (n j) (z j) - normalCDF (z j))) :
    Q = esseenLaw ∧ Filter.Tendsto z Filter.atTop (nhds 0) := by
  obtain ⟨h, hh, hspan, hmax, hcancel⟩ := manuscript_exists_span_and_resonance_multiplier Q
  have hzero (r : ℝ) (hr : r ≠ 0) (hres : r ∈ resonanceSubgroup Q.measure) :
      Real.sinc (h * r / 2) = 0 :=
    hcancel r hr ((mem_resonanceSubgroup_iff Q.measure r).1 hres)
  obtain ⟨hQ, he⟩ := bounded_violation_limit_esseen W S E P Q hw hβ hb n hn hn2
    h ⟨hh, hspan, hmax⟩ hzero z hviol
  refine ⟨hQ, ?_⟩
  subst Q
  subst h
  exact bounded_violation_threshold_tendsto_zero W S P hw hβ hb n hn hn2 hzero z hviol

end BerryEsseen
