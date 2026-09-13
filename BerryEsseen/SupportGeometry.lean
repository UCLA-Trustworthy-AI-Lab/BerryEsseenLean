import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! The geometric and compactness steps at the end of Section 5. -/
open Filter Set
open scoped Topology
namespace BerryEsseen

theorem two_atom_geometry (r : ℝ) (hlo : -1 < r) (hhi : r < 2)
    (hzero : r = 0 ∨ 1 ≤ |r|)
    (hone : r = 1 ∨ 1 ≤ |r - 1|) : r = 0 ∨ r = 1 := by
  rcases hzero with h | h
  · exact Or.inl h
  rcases hone with h' | h'
  · exact Or.inr h'
  rcases le_abs.1 h with hr | hr
  · have habs : |r - 1| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
    exact False.elim ((not_lt_of_ge h') habs)
  · linarith

/-- Nonzero limiting contact increments contradict flatness. -/
theorem no_positive_contact_increment (u : ℕ → ℝ) (φ d : ℝ)
    (hφ : 0 < φ) (hd : 0 < d)
    (hflat : Tendsto u atTop (𝓝 0))
    (hcontact : Tendsto u atTop (𝓝 (φ * d))) : False := by
  have h := tendsto_nhds_unique hflat hcontact
  have hp := mul_pos hφ hd
  linarith

/-- All support limits are atoms: compactness upgrades this to uniform confinement.
`S j` may be any sets, not necessarily finite or discrete. -/
theorem uniform_confinement (S : ℕ → Set ℝ) (K : Set ℝ) (A : Set ℝ)
    (hK : IsCompact K) (hS : ∀ j, S j ⊆ K)
    (hlim : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (x : ℕ → ℝ),
      (∀ j, x j ∈ S (φ j)) → ∀ y, Tendsto x atTop (𝓝 y) → y ∈ A)
    (U : Set ℝ) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∀ᶠ j in atTop, S j ⊆ U := by
  by_contra h
  have hfreq : ∃ᶠ j in atTop, ¬ S j ⊆ U := by simpa only [Filter.Frequently, not_not] using h
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hfreq
  have hex (j : ℕ) : ∃ x, x ∈ S (φ j) ∧ x ∉ U := by
    simpa only [Set.not_subset] using hbad j
  choose x hx hout using hex
  obtain ⟨y, hyK, ψ, hψ, hxy⟩ := hK.tendsto_subseq (fun j => hS (φ j) (hx j))
  have hyA : y ∈ A := hlim (φ ∘ ψ) (hφ.comp hψ) (x ∘ ψ)
    (fun j => hx (ψ j)) y hxy
  have hev : ∀ᶠ j in atTop, x (ψ j) ∈ U := hxy.eventually (hU.mem_nhds (hAU hyA))
  obtain ⟨j, hj⟩ := hev.exists
  exact hout (ψ j) hj

/-- Specialization to the neighborhoods used in Proposition 3.1. -/
theorem uniform_two_cluster_confinement (S : ℕ → Set ℝ) (L : ℝ)
    (hS : ∀ j, S j ⊆ Icc (-L) L)
    (hlim : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (x : ℕ → ℝ),
      (∀ j, x j ∈ S (φ j)) → ∀ y, Tendsto x atTop (𝓝 y) → y = 0 ∨ y = 1)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j in atTop, S j ⊆ Ioo (-η) η ∪ Ioo (1 - η) (1 + η) := by
  apply uniform_confinement S (Icc (-L) L) {0, 1} isCompact_Icc hS
  · intro φ hφ x hx y hy
    simpa using hlim φ hφ x hx y hy
  · exact isOpen_Ioo.union isOpen_Ioo
  · intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Or.inl ⟨by linarith, hη⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

end BerryEsseen
