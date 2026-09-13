import BerryEsseen.EffectiveFiniteLatticeMoments
import Mathlib.Algebra.GCDMonoid.Finset

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem finite_positive_atoms_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hs : μ.support ⊆ (F : Set ℝ)) (hatom : ∀ x ∈ F, τ ≤ μ.real {x}) :
    μ.support = (F : Set ℝ) := by
  apply Subset.antisymm hs
  intro x hx
  have hnz : μ {x} ≠ 0 := by
    intro hz
    have hr : μ.real {x} = 0 := by simp [Measure.real, hz]
    have hp := hatom x hx
    linarith
  obtain ⟨y, hy, hyS⟩ := μ.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hnz)
  have he : y = x := mem_singleton_iff.mp hy
  rwa [← he]

theorem lattice_pair_natural_step (μ : Measure ℝ) (h : ℝ) (hlat : IsLatticeSpan μ h)
    (x y : ℝ) (hx : x ∈ μ.support) (hy : y ∈ μ.support) (hxy : y ≤ x) :
    ∃ d : ℕ, x = y + h * (d : ℝ) := by
  obtain ⟨hh, a, ha⟩ := hlat
  obtain ⟨kx, hkx⟩ := ha x hx
  obtain ⟨ky, hky⟩ := ha y hy
  have he : x - y = ((kx - ky : ℤ) : ℝ) * h := by push_cast; linarith only [hkx, hky]
  have hnonneg : 0 ≤ ((kx - ky : ℤ) : ℝ) := by
    by_contra hn
    have hp := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hh
    nlinarith only [hp, he, hxy]
  have hint : 0 ≤ kx - ky := by exact_mod_cast hnonneg
  lift (kx - ky) to ℕ using hint with d hd
  refine ⟨d, ?_⟩
  push_cast at he
  nlinarith only [he]

theorem finite_lattice_natural_labels (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (h : ℝ) (hs : μ.support = (F : Set ℝ))
    (hb : ∀ x ∈ F, |x| < 13) (hlo : Real.pi / 500 ≤ h) (hlat : IsLatticeSpan μ h) :
    ∃ (z : ℝ) (d : ℝ → ℕ), z ∈ F ∧ d z = 0 ∧
      ∀ x ∈ F, x = z + h * (d x : ℝ) ∧ d x ≤ 5000 := by
  classical
  have hF : F.Nonempty := by
    obtain ⟨x, hx⟩ := μ.nonempty_support (IsProbabilityMeasure.ne_zero μ)
    refine ⟨x, ?_⟩
    change x ∈ (F : Set ℝ)
    rwa [← hs]
  let z := F.min' hF
  have hz : z ∈ F := Finset.min'_mem F hF
  have hstep : ∀ x : ℝ, ∃ d : ℕ, x ∈ F → x = z + h * (d : ℝ) ∧ d ≤ 5000 := by
    intro x
    by_cases hx : x ∈ F
    · have hxS : x ∈ μ.support := by rw [hs]; exact hx
      have hzS : z ∈ μ.support := by rw [hs]; exact hz
      obtain ⟨d, hd⟩ := lattice_pair_natural_step μ h hlat x z hxS hzS (Finset.min'_le F x hx)
      refine ⟨d, fun _ => ⟨hd, ?_⟩⟩
      have hxb := hb x hx
      have hzb := hb z hz
      have hprod := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg d)
      have hdReal : (d : ℝ) ≤ 5000 := by
        have hp := Real.pi_gt_d2
        have hb := mul_le_mul_of_nonneg_right hp.le (Nat.cast_nonneg d)
        nlinarith [le_abs_self x, neg_le_abs z]
      exact_mod_cast hdReal
    · exact ⟨0, fun hx' => False.elim (hx hx')⟩
  choose d hd using hstep
  have hz0 : d z = 0 := by
    have he := (hd z hz).1
    have he0 : h * (d z : ℝ) = 0 := by linarith
    have hd0 : (d z : ℝ) = 0 := (mul_eq_zero.mp he0).resolve_left hlat.1.ne'
    exact_mod_cast hd0
  exact ⟨z, d, hz, hz0, hd⟩

/-- Retain the original nearest-rounding integer range; absolute support bounds
alone discard the manuscript's coefficient budget. -/
theorem manuscript_lattice_rounding_index_span (a h : ℝ)
    (hlo : Real.pi / 500 ≤ h) (i j : ℤ)
    (hi : i ∈ latticeRoundingIndices a h) (hj : j ∈ latticeRoundingIndices a h) :
    i - j < 2000 := by
  have hc := latticeRoundingIndices_card a h hlo
  rw [latticeRoundingIndices, Int.card_Icc] at hc
  rw [latticeRoundingIndices, Finset.mem_Icc] at hi hj
  omega

theorem manuscript_finite_lattice_natural_labels (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (a h₀ h : ℝ) (hs : μ.support = (F : Set ℝ))
    (hF : F ⊆ latticeRoundingPoints a h₀) (hlo : Real.pi / 500 ≤ h₀)
    (hh : h₀ ≤ h) (hlat : IsLatticeSpan μ h) :
    ∃ (z : ℝ) (d : ℝ → ℕ), z ∈ F ∧ d z = 0 ∧
      ∀ x ∈ F, x = z + h * (d x : ℝ) ∧ d x < 2000 := by
  classical
  have hFne : F.Nonempty := by
    obtain ⟨x, hx⟩ := μ.nonempty_support (IsProbabilityMeasure.ne_zero μ)
    exact ⟨x, by simpa only [hs, Finset.mem_coe] using hx⟩
  let z := F.min' hFne
  have hz : z ∈ F := Finset.min'_mem F hFne
  have h₀pos : 0 < h₀ := (div_pos Real.pi_pos (by norm_num)).trans_le hlo
  have hstep : ∀ x : ℝ, ∃ d : ℕ, x ∈ F → x = z + h * (d : ℝ) ∧ d < 2000 := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨d, hd⟩ := lattice_pair_natural_step μ h hlat x z
        (by rw [hs]; exact hx) (by rw [hs]; exact hz) (Finset.min'_le F x hx)
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hF hx)
      obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp (hF hz)
      have hij := manuscript_lattice_rounding_index_span a h₀ hlo i j hi hj
      have hijR : (i : ℝ) - (j : ℝ) < 2000 := by exact_mod_cast hij
      have hxz : x - z < h₀ * 2000 := by
        have hm := mul_lt_mul_of_pos_left hijR h₀pos
        nlinarith only [hm, hix, hjz]
      have hp := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg d)
      have hdR : (d : ℝ) < 2000 := by
        apply (mul_lt_mul_iff_right₀ h₀pos).mp
        nlinarith only [hp, hd, hxz]
      exact ⟨d, fun _ => ⟨hd, by exact_mod_cast hdR⟩⟩
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose d hd using hstep
  have hz0 : d z = 0 := by
    have he := (hd z hz).1
    have he0 : h * (d z : ℝ) = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp he0).resolve_left hlat.1.ne'
  exact ⟨z, d, hz, hz0, hd⟩

theorem maximal_lattice_label_gcd_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (z h : ℝ) (d : ℝ → ℕ) (hh : 0 < h)
    (hs : μ.support ⊆ (F : Set ℝ)) (hd : ∀ x ∈ F, x = z + h * (d x : ℝ))
    (hmax : ∀ t : ℝ, IsLatticeSpan μ t → t ≤ h) : (F.image d).gcd id = 1 := by
  classical
  let D := F.image d
  let G : ℕ := D.gcd id
  have hdiv (x : ℝ) (hx : x ∈ F) : G ∣ d x :=
    Finset.gcd_dvd (f := id) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hG : 0 < G := by
    by_contra hbad
    have hz : G = 0 := by omega
    have hspan : IsLatticeSpan μ (2 * h) := by
      refine ⟨by positivity, z, ?_⟩
      intro x hx
      have hxF := hs hx
      have hd0 : d x = 0 := by
        have hv := hdiv x hxF
        rw [hz, zero_dvd_iff] at hv
        exact hv
      refine ⟨0, ?_⟩
      rw [hd x hxF, hd0]
      simp
    have hm := hmax (2 * h) hspan
    linarith
  have hspan : IsLatticeSpan μ (h * (G : ℝ)) := by
    refine ⟨mul_pos hh (by exact_mod_cast hG), z, ?_⟩
    intro x hx
    have hxF := hs hx
    obtain ⟨k, hk⟩ := hdiv x hxF
    refine ⟨(k : ℤ), ?_⟩
    rw [hd x hxF, hk]
    push_cast
    ring
  have hGle : (G : ℝ) ≤ 1 := by
    have hm := hmax (h * (G : ℝ)) hspan
    apply le_of_mul_le_mul_left (a := h) _ hh
    nlinarith only [hm]
  have hGnat : G ≤ 1 := by exact_mod_cast hGle
  change G = 1
  omega

end BerryEsseen
