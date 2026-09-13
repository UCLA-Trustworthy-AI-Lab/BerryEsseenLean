import BerryEsseen.CompactFourierConvergence
import BerryEsseen.SupportGeometry
import BerryEsseen.TaylorBounds
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Moving maxima and the quadratic envelopes used at nonzero resonances. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem compact_maximizers_converge (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (K : Set ℝ) (hK : IsCompact K) (a : ℝ) (ha : a ∈ K)
    (hg : Continuous g) (hstrict : ∀ x ∈ K, x ≠ a → g x < g a)
    (hu : TendstoUniformlyOn f g atTop K)
    (m : ℕ → ℝ) (hm : ∀ j, m j ∈ K) (hmax : ∀ j, IsMaxOn (f j) K (m j)) :
    Tendsto m atTop (𝓝 a) := by
  have hlim : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ (x : ℕ → ℝ),
      (∀ j, x j ∈ ({m (φ j)} : Set ℝ)) → ∀ y, Tendsto x atTop (𝓝 y) → y ∈ ({a} : Set ℝ) := by
    intro φ hφ x hx y hxy
    have hxe (j : ℕ) : x j = m (φ j) := hx j
    have hxK : ∀ᶠ j in atTop, x j ∈ K := .of_forall (fun j => by rw [hxe j]; exact hm (φ j))
    have hyK : y ∈ K := hK.isClosed.mem_of_tendsto hxy hxK
    have hxw : Tendsto x atTop (𝓝[K] y) := tendsto_nhdsWithin_iff.2 ⟨hxy, hxK⟩
    have hval := (hu.seq_tendstoUniformlyOn φ hφ.tendsto_atTop).tendsto_comp
      hg.continuousAt.continuousWithinAt hxw
    have hat := (hu.tendsto_at ha).comp hφ.tendsto_atTop
    have hle : g a ≤ g y := le_of_tendsto_of_tendsto hat hval (.of_forall (fun j => by
      change f (φ j) a ≤ f (φ j) (x j)
      rw [hxe j]
      exact hmax (φ j) ha))
    apply mem_singleton_iff.2
    by_contra hya
    exact (not_lt_of_ge hle) (hstrict y hyK hya)
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := uniform_confinement (fun j => ({m j} : Set ℝ)) K {a} hK
    (fun j x hx => by rw [mem_singleton_iff] at hx; rw [hx]; exact hm j) hlim
    (Metric.ball a ε) Metric.isOpen_ball (singleton_subset_iff.2 (Metric.mem_ball_self hε))
  filter_upwards [he] with j hj
  exact hj (mem_singleton (m j))

theorem exists_convergent_compact_maximizers (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (K : Set ℝ) (hK : IsCompact K) (a : ℝ) (ha : a ∈ K)
    (hf : ∀ j, ContinuousOn (f j) K) (hg : Continuous g)
    (hstrict : ∀ x ∈ K, x ≠ a → g x < g a) (hu : TendstoUniformlyOn f g atTop K) :
    ∃ m : ℕ → ℝ, (∀ j, m j ∈ K ∧ IsMaxOn (f j) K (m j)) ∧ Tendsto m atTop (𝓝 a) := by
  choose m hm hmax using fun j => hK.exists_isMaxOn ⟨a, ha⟩ (hf j)
  exact ⟨m, fun j => ⟨hm j, hmax j⟩, compact_maximizers_converge f g K hK a ha hg hstrict hu m hm hmax⟩

theorem quadratic_upper_at_critical_point (f f₁ f₂ : ℝ → ℝ) (L R m u : ℝ)
    (hm : m ∈ Icc L R) (hu : u ∈ Icc L R)
    (h₁ : ∀ x ∈ Icc L R, HasDerivAt f (f₁ x) x)
    (h₂ : ∀ x ∈ Icc L R, HasDerivAt f₁ (f₂ x) x)
    (hcurv : ∀ x ∈ Icc L R, f₂ x ≤ -1) (hcrit : f₁ m = 0) :
    f u ≤ f m - (u - m) ^ 2 / 2 := by
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) : m + (u - m) * t ∈ Icc L R := by
    have h := (convex_Icc L R) hm hu (sub_nonneg.2 ht.2) ht.1
      (show 1 - t + t = (1 : ℝ) by ring)
    convert h using 1 <;> (simp only [smul_eq_mul]; ring)
  let F : ℝ → ℝ := fun t => f (m + (u - m) * t)
  let F₁ : ℝ → ℝ := fun t => (u - m) * f₁ (m + (u - m) * t)
  let F₂ : ℝ → ℝ := fun t => (u - m) ^ 2 * f₂ (m + (u - m) * t)
  have hd1 : ∀ t ∈ Icc 0 1, HasDerivAt F (F₁ t) t := by
    intro t ht
    simpa [F, F₁] using hasDerivAt_scaled_affine_comp f _ m (u - m) t 0 (h₁ _ (hseg t ht))
  have hd2 : ∀ t ∈ Icc 0 1, HasDerivAt F₁ (F₂ t) t := by
    intro t ht
    simpa [F₁, F₂] using hasDerivAt_scaled_affine_comp f₁ _ m (u - m) t 1 (h₂ _ (hseg t ht))
  have hc : ∀ t ∈ Icc 0 1, F₂ t ≤ -(u - m) ^ 2 := by
    intro t ht
    have h := mul_le_mul_of_nonneg_left (hcurv _ (hseg t ht)) (sq_nonneg (u - m))
    simpa [F₂] using h
  have h := taylor_second_upper F F₁ F₂ (-(u - m) ^ 2) hd1 hd2 hc 1 (by norm_num)
  simp [F, F₁, hcrit] at h
  linarith

theorem norm_pow_gaussian_of_square_bound (z : ℂ) (d : ℝ)
    (h : ‖z‖ ^ 2 ≤ 1 - d ^ 2 / 2) (n : ℕ) :
    ‖z‖ ^ n ≤ Real.exp (-(n : ℝ) * d ^ 2 / 4) := by
  have he := Real.add_one_le_exp (-d ^ 2 / 2)
  have heq : Real.exp (-d ^ 2 / 4) ^ 2 = Real.exp (-d ^ 2 / 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hn : ‖z‖ ≤ Real.exp (-d ^ 2 / 4) := by nlinarith [norm_nonneg z, Real.exp_pos (-d ^ 2 / 4)]
  have hp := pow_le_pow_left₀ (norm_nonneg z) hn n
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

theorem characteristic_peak_envelope (P : StandardizedLaw) (L R m : ℝ)
    (hm : m ∈ Ioo L R) (hmax : IsMaxOn (characteristicSquare P) (Icc L R) m)
    (hcurv : ∀ x ∈ Icc L R, characteristicSquareCurvature P x ≤ -1)
    (u : ℝ) (hu : u ∈ Icc L R) (n : ℕ) :
    ‖charFun P.measure u‖ ^ n ≤ Real.exp (-(n : ℝ) * (u - m) ^ 2 / 4) := by
  have hc : characteristicSquareSlope P m = 0 :=
    (hmax.isLocalMax (Icc_mem_nhds hm.1 hm.2)).hasDerivAt_eq_zero (characteristicSquare_hasDerivAt P m)
  have hq := quadratic_upper_at_critical_point (characteristicSquare P) (characteristicSquareSlope P)
    (characteristicSquareCurvature P) L R m u ⟨hm.1.le, hm.2.le⟩ hu
    (fun x _ => characteristicSquare_hasDerivAt P x)
    (fun x _ => characteristicSquareSlope_hasDerivAt P x) hcurv hc
  have hm1 : characteristicSquare P m ≤ 1 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le_one (μ := P.measure) m) 2
    simpa [characteristicSquare] using h
  apply norm_pow_gaussian_of_square_bound
  change characteristicSquare P u ≤ _
  linarith

end BerryEsseen
