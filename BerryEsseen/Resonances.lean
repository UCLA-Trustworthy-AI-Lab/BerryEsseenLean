import BerryEsseen.JitterCharacteristic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.Order.Archimedean

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

def realPhase (u x : ℝ) : ℂ := Complex.exp ((u * x : ℝ) * Complex.I)

theorem realPhase_norm (u x : ℝ) : ‖realPhase u x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem realPhase_add (u v x : ℝ) : realPhase (u + v) x = realPhase u x * realPhase v x := by
  unfold realPhase
  rw [show (((u + v) * x : ℝ) : ℂ) * Complex.I =
    ((u * x : ℝ) : ℂ) * Complex.I + ((v * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]

theorem realPhase_neg (u x : ℝ) : realPhase (-u) x = (realPhase u x)⁻¹ := by
  unfold realPhase
  rw [show (((-u) * x : ℝ) : ℂ) * Complex.I = -(((u * x : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_neg]

theorem charFun_eq_integral_realPhase (μ : Measure ℝ) (u : ℝ) :
    charFun μ u = ∫ x, realPhase u x ∂μ := by
  rw [charFun_apply_real]
  simp only [realPhase, Complex.ofReal_mul]

theorem norm_charFun_eq_one_iff_phase_constant (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    ‖charFun μ u‖ = 1 ↔ ∃ c : ℂ, ∀ᵐ x ∂μ, realPhase u x = c := by
  constructor
  · intro hnorm
    have hd := ae_eq_const_or_norm_integral_lt_of_norm_le_const
      (μ := μ) (f := realPhase u) (C := (1 : ℝ))
      (ae_of_all _ (fun x => (realPhase_norm u x).le))
    simp only [average_eq_integral, probReal_univ, one_mul,
      ← charFun_eq_integral_realPhase, hnorm, lt_self_iff_false, or_false] at hd
    exact ⟨charFun μ u, hd⟩
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx⟩ := hc.exists
    rw [charFun_eq_integral_realPhase, integral_congr_ae hc, integral_const, probReal_univ, one_smul,
      ← hx, realPhase_norm]

def resonanceSubgroup (μ : Measure ℝ) : AddSubgroup ℝ where
  carrier := {u | ∃ c : ℂ, ∀ᵐ x ∂μ, realPhase u x = c}
  zero_mem' := ⟨1, ae_of_all _ (fun x => by simp [realPhase])⟩
  add_mem' := by
    rintro u v ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    filter_upwards [hc, hd] with x hx hy
    rw [realPhase_add, hx, hy]
  neg_mem' := by
    rintro u ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [hc] with x hx
    rw [realPhase_neg, hx]

theorem mem_resonanceSubgroup_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    u ∈ resonanceSubgroup μ ↔ ‖charFun μ u‖ = 1 :=
  (norm_charFun_eq_one_iff_phase_constant μ u).symm

theorem resonance_phase_on_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (hu : u ∈ resonanceSubgroup μ) :
    ∀ x ∈ μ.support, realPhase u x = charFun μ u := by
  obtain ⟨c, hc⟩ := hu
  have hcf : charFun μ u = c := by
    rw [charFun_eq_integral_realPhase, integral_congr_ae hc, integral_const, probReal_univ, one_smul]
  have hclosed : IsClosed {x : ℝ | realPhase u x = c} :=
    isClosed_eq (by unfold realPhase; fun_prop) continuous_const
  intro x hx
  rw [hcf]
  exact μ.support_subset_of_isClosed hclosed hc hx

theorem standardized_support_nontrivial (P : StandardizedLaw) : P.measure.support.Nontrivial := by
  by_contra h
  have hsub : P.measure.support.Subsingleton := Set.not_nontrivial_iff.1 h
  obtain ⟨a, ha⟩ := P.measure.nonempty_support (IsProbabilityMeasure.ne_zero P.measure)
  have hae : ∀ᵐ x ∂P.measure, x = a := by
    filter_upwards [P.measure.support_mem_ae] with x hx
    exact hsub hx ha
  have hm : a = 0 := by
    have he := integral_congr_ae hae
    rw [P.mean_zero, integral_const, probReal_univ, smul_eq_mul, one_mul] at he
    exact he.symm
  have hsq : (∫ x : ℝ, x ^ 2 ∂P.measure) = 0 := by
    calc
      _ = ∫ _ : ℝ, a ^ 2 ∂P.measure := integral_congr_ae (hae.mono (fun x hx => by rw [hx]))
      _ = 0 := by simp [hm]
  linarith [P.second_one]

theorem realPhase_eq_one_iff (u x : ℝ) :
    realPhase u x = 1 ↔ ∃ k : ℤ, u * x = (k : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨k, ?_⟩
    have hi := congrArg Complex.im hk
    simpa using hi
  · rintro ⟨k, hk⟩
    apply Complex.exp_eq_one_iff.2
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    ring

theorem resonance_support_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (hu : u ∈ resonanceSubgroup μ) (a b : ℝ) (ha : a ∈ μ.support) (hb : b ∈ μ.support) :
    ∃ k : ℤ, u * (a - b) = (k : ℝ) * (2 * Real.pi) := by
  apply (realPhase_eq_one_iff u (a - b)).1
  have he : realPhase u (a - b) = realPhase u a / realPhase u b := by
    unfold realPhase
    rw [show (((u * (a - b) : ℝ) : ℂ) * Complex.I) =
      ((u * a : ℝ) : ℂ) * Complex.I - ((u * b : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_sub]
  rw [he, resonance_phase_on_support μ u hu a ha, resonance_phase_on_support μ u hu b hb]
  apply div_self
  have hn : ‖charFun μ u‖ = 1 := (mem_resonanceSubgroup_iff μ u).1 hu
  intro hc
  simp [hc] at hn

theorem resonance_gap (P : StandardizedLaw) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ resonanceSubgroup P.measure, u ≠ 0 → δ ≤ |u| := by
  obtain ⟨a, ha, b, hb, hab⟩ := standardized_support_nontrivial P
  have hd : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 hab)
  refine ⟨2 * Real.pi / |a - b|, div_pos Real.two_pi_pos hd, ?_⟩
  intro u hu hu0
  obtain ⟨k, hk⟩ := resonance_support_difference P.measure u hu a b ha hb
  have hk0 : k ≠ 0 := by
    intro hk0
    simp only [hk0, Int.cast_zero, zero_mul] at hk
    exact (mul_ne_zero hu0 (sub_ne_zero.2 hab)) hk
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hki : (1 : ℤ) ≤ |k| := by have := abs_pos.2 hk0; omega
    exact_mod_cast hki
  have habs := congrArg abs hk
  rw [abs_mul, abs_mul, abs_of_pos Real.two_pi_pos] at habs
  apply (div_le_iff₀ hd).2
  nlinarith [Real.pi_pos]

theorem resonanceSubgroup_cyclic (P : StandardizedLaw) :
    ∃ a : ℝ, resonanceSubgroup P.measure = AddSubgroup.zmultiples a := by
  obtain ⟨δ, hδ, hgap⟩ := resonance_gap P
  have hdis : Disjoint (resonanceSubgroup P.measure : Set ℝ) (Ioo 0 δ) := by
    apply Set.disjoint_left.2
    intro u hu hut
    have h := hgap u hu hut.1.ne'
    rw [abs_of_pos hut.1] at h
    exact (not_lt_of_ge h) hut.2
  obtain ⟨a, ha⟩ := AddSubgroup.cyclic_of_isolated_zero hδ hdis
  exact ⟨a, by simpa only [← AddSubgroup.zmultiples_eq_closure] using ha⟩

def IsLatticeSpan (μ : Measure ℝ) (h : ℝ) : Prop :=
  0 < h ∧ ∃ a : ℝ, ∀ x ∈ μ.support, ∃ k : ℤ, x = a + (k : ℝ) * h

theorem latticeSpan_gives_resonance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ℝ) (hh : IsLatticeSpan μ h) : 2 * Real.pi / h ∈ resonanceSubgroup μ := by
  obtain ⟨hh, a, ha⟩ := hh
  refine ⟨realPhase (2 * Real.pi / h) a, ?_⟩
  filter_upwards [μ.support_mem_ae] with x hx
  obtain ⟨k, hk⟩ := ha x hx
  have hperiod : realPhase (2 * Real.pi / h) ((k : ℝ) * h) = 1 := by
    apply (realPhase_eq_one_iff _ _).2
    refine ⟨k, ?_⟩
    field_simp
  rw [hk]
  have he : realPhase (2 * Real.pi / h) (a + (k : ℝ) * h) =
      realPhase (2 * Real.pi / h) a * realPhase (2 * Real.pi / h) ((k : ℝ) * h) := by
    unfold realPhase
    rw [show (((2 * Real.pi / h * (a + (k : ℝ) * h) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi / h * a : ℝ) : ℂ) * Complex.I +
      ((2 * Real.pi / h * ((k : ℝ) * h) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add]
  rw [he, hperiod, mul_one]

theorem positive_resonance_gives_span (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (u : ℝ) (hu : 0 < u) (hres : u ∈ resonanceSubgroup μ) :
    IsLatticeSpan μ (2 * Real.pi / u) := by
  obtain ⟨a, ha⟩ := μ.nonempty_support (IsProbabilityMeasure.ne_zero μ)
  refine ⟨div_pos Real.two_pi_pos hu, a, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := resonance_support_difference μ u hres x a hx ha
  refine ⟨k, ?_⟩
  apply (mul_right_injective₀ hu.ne')
  field_simp
  nlinarith [hk]

theorem resonanceSubgroup_nonnegative_generator (P : StandardizedLaw) :
    ∃ a : ℝ, 0 ≤ a ∧ resonanceSubgroup P.measure = AddSubgroup.zmultiples a := by
  obtain ⟨a, ha⟩ := resonanceSubgroup_cyclic P
  refine ⟨|a|, abs_nonneg a, ?_⟩
  by_cases ha0 : 0 ≤ a
  · rwa [abs_of_nonneg ha0]
  · rw [abs_of_neg (lt_of_not_ge ha0), AddSubgroup.zmultiples_neg]
    exact ha

theorem maximal_span_of_positive_generator (P : StandardizedLaw) (a : ℝ) (ha : 0 < a)
    (hgen : resonanceSubgroup P.measure = AddSubgroup.zmultiples a) :
    IsLatticeSpan P.measure (2 * Real.pi / a) ∧
      ∀ d : ℝ, IsLatticeSpan P.measure d → d ≤ 2 * Real.pi / a := by
  have hares : a ∈ resonanceSubgroup P.measure := by
    rw [hgen]
    exact AddSubgroup.mem_zmultiples_iff.2 ⟨1, by simp⟩
  refine ⟨positive_resonance_gives_span P.measure a ha hares, ?_⟩
  intro d hd
  have hres := latticeSpan_gives_resonance P.measure d hd
  rw [hgen, AddSubgroup.mem_zmultiples_iff] at hres
  obtain ⟨k, hk⟩ := hres
  rw [zsmul_eq_mul] at hk
  have hkpos : 0 < (k : ℝ) := by
    have he : 0 < (k : ℝ) * a := by rw [hk]; exact div_pos Real.two_pi_pos hd.1
    exact (mul_pos_iff_of_pos_right ha).1 he
  have hkone : (1 : ℝ) ≤ k := by
    have hki : (0 : ℤ) < k := by exact_mod_cast hkpos
    exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hprod : a ≤ 2 * Real.pi / d := by
    have h := mul_le_mul_of_nonneg_right hkone ha.le
    simpa only [one_mul, hk] using h
  have hmul := (le_div_iff₀ hd.1).1 hprod
  apply (le_div_iff₀ ha).2
  nlinarith

theorem lattice_span_dichotomy (P : StandardizedLaw) :
    (resonanceSubgroup P.measure = ⊥ ∧ ∀ d : ℝ, ¬ IsLatticeSpan P.measure d) ∨
    ∃ h : ℝ, IsLatticeSpan P.measure h ∧
      (∀ d : ℝ, IsLatticeSpan P.measure d → d ≤ h) ∧
      resonanceSubgroup P.measure = AddSubgroup.zmultiples (2 * Real.pi / h) := by
  obtain ⟨a, ha0, hgen⟩ := resonanceSubgroup_nonnegative_generator P
  rcases eq_or_lt_of_le ha0 with haz | ha
  · left
    have hbot : resonanceSubgroup P.measure = ⊥ := by simpa [← haz] using hgen
    refine ⟨hbot, ?_⟩
    intro d hd
    have hr := latticeSpan_gives_resonance P.measure d hd
    rw [hbot, AddSubgroup.mem_bot] at hr
    exact (div_pos Real.two_pi_pos hd.1).ne' hr
  · right
    obtain ⟨hspan, hmax⟩ := maximal_span_of_positive_generator P a ha hgen
    refine ⟨2 * Real.pi / a, hspan, hmax, ?_⟩
    have he : 2 * Real.pi / (2 * Real.pi / a) = a := by field_simp
    rwa [he]

theorem exists_span_and_resonance_multiplier (P : StandardizedLaw) :
    ∃ h : ℝ, 0 ≤ h ∧ (0 < h → IsLatticeSpan P.measure h) ∧
      (∀ d : ℝ, IsLatticeSpan P.measure d → d ≤ h) ∧
      ∀ u : ℝ, u ≠ 0 → ‖charFun P.measure u‖ = 1 → Real.sinc (h * u / 2) = 0 := by
  rcases lattice_span_dichotomy P with ⟨hbot, hnonlat⟩ | ⟨h, hspan, hmax, hgen⟩
  · refine ⟨0, le_rfl, fun h => False.elim (lt_irrefl _ h), ?_, ?_⟩
    · intro d hd
      exact False.elim (hnonlat d hd)
    · intro u hu hnorm
      have hmem := (mem_resonanceSubgroup_iff P.measure u).2 hnorm
      rw [hbot, AddSubgroup.mem_bot] at hmem
      exact False.elim (hu hmem)
  · refine ⟨h, hspan.1.le, fun _ => hspan, hmax, ?_⟩
    intro u hu hnorm
    have hmem := (mem_resonanceSubgroup_iff P.measure u).2 hnorm
    rw [hgen, AddSubgroup.mem_zmultiples_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [zsmul_eq_mul] at hk
    have hk0 : k ≠ 0 := by intro hk0; simp [hk0] at hk; exact hu hk.symm
    have he : u = 2 * Real.pi * (k : ℝ) / h := by rw [← hk]; ring
    rw [he]
    exact spanJitter_multiplier_resonance_zero h hspan.1 k hk0

end BerryEsseen
