import BerryEsseen.EsseenLaw

/-! Esseen (1956), as stated in Mattner--Shevtsova (2019), p. 491, (1.6)--(1.8).
An explicit published premise, with reflection and absolute-value consequences proved below. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BerryEsseen

def IsMaximalSpan (P : StandardizedLaw) (h : ℝ) : Prop :=
  0 ≤ h ∧ (0 < h → IsLatticeSpan P.measure h) ∧
    ∀ d : ℝ, IsLatticeSpan P.measure d → d ≤ h

theorem reflected_maximal_span (P : StandardizedLaw) (h : ℝ)
    (hh : IsMaximalSpan P h) : IsMaximalSpan (reflectedLaw P) h := by
  refine ⟨hh.1, fun hp => reflected_lattice_span P h (hh.2.1 hp), ?_⟩
  intro d hd
  apply hh.2.2 d
  have ht := reflected_lattice_span (reflectedLaw P) d hd
  change IsLatticeSpan ((P.measure.map (fun x => -x)).map (fun x => -x)) d at ht
  rwa [reflected_measure_twice] at ht

structure PublishedEsseenMoment : Prop where
  bound : ∀ (P : StandardizedLaw) (h : ℝ), IsMaximalSpan P h →
    signedThirdMoment P + 3 * h ≤ cStar * thirdMoment P
  equality : ∀ (P : StandardizedLaw) (h : ℝ), IsMaximalSpan P h →
    signedThirdMoment P + 3 * h = cStar * thirdMoment P →
      P.measure = esseenLaw.measure

theorem esseen_absolute_moment_bound (E : PublishedEsseenMoment)
    (P : StandardizedLaw) (h : ℝ) (hh : IsMaximalSpan P h) :
    |signedThirdMoment P| + 3 * h ≤ cStar * thirdMoment P := by
  by_cases hk : 0 ≤ signedThirdMoment P
  · rw [abs_of_nonneg hk]
    exact E.bound P h hh
  · rw [abs_of_neg (lt_of_not_ge hk)]
    have ht := E.bound (reflectedLaw P) h (reflected_maximal_span P h hh)
    simpa only [reflectedLaw_signedThirdMoment, reflectedLaw_thirdMoment] using ht

theorem esseen_absolute_moment_equality (E : PublishedEsseenMoment)
    (P : StandardizedLaw) (h : ℝ) (hh : IsMaximalSpan P h)
    (heq : |signedThirdMoment P| + 3 * h = cStar * thirdMoment P) :
    P.measure = esseenLaw.measure ∨ P.measure = (reflectedLaw esseenLaw).measure := by
  by_cases hk : 0 ≤ signedThirdMoment P
  · left
    exact E.equality P h hh (by simpa only [abs_of_nonneg hk] using heq)
  · right
    have ht : signedThirdMoment (reflectedLaw P) + 3 * h = cStar * thirdMoment (reflectedLaw P) := by
      simpa only [reflectedLaw_signedThirdMoment, reflectedLaw_thirdMoment,
        abs_of_neg (lt_of_not_ge hk)] using heq
    have he := E.equality (reflectedLaw P) h (reflected_maximal_span P h hh) ht
    have hm := congrArg (fun μ : Measure ℝ => μ.map (fun x => -x)) he
    change (P.measure.map (fun x => -x)).map (fun x => -x) = _ at hm
    rwa [reflected_measure_twice] at hm

end BerryEsseen
