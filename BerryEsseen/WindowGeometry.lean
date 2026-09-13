import BerryEsseen.IntegerWindow
import BerryEsseen.AppliedClusterBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem central_integer_window_geometry (p δ R L x : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) (hL : L ≤ n)
    (hlarge : 2 * (R + 1) ≤ δ * Real.sqrt (n : ℝ))
    (hx : |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ)) :
    0 ≤ x - max 1 (Real.sqrt L) ∧ x + max 1 (Real.sqrt L) ≤ n ∧
    ∀ k ∈ integerWindow x (max 1 (Real.sqrt L)), k ≤ n ∧
      |(k : ℝ) - n * p| ≤ (R + 1) * Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hr0 := Real.sqrt_nonneg (n : ℝ)
  have hr1 : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  have hrad : max 1 (Real.sqrt L) ≤ Real.sqrt (n : ℝ) := max_le hr1 (Real.sqrt_le_sqrt hL)
  have hscale := mul_le_mul_of_nonneg_right hlarge hr0
  have hcentral : (R + 1) * Real.sqrt (n : ℝ) ≤ δ * n := by
    have he : δ * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = δ * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]
    rw [he] at hscale
    nlinarith only [hscale, mul_nonneg (by linarith : 0 ≤ R + 1) hr0]
  have hpx := mul_le_mul_of_nonneg_left hp hn0
  have hqx := mul_le_mul_of_nonneg_left hq hn0
  have hx' := abs_le.1 hx
  have hlo : 0 ≤ x - max 1 (Real.sqrt L) := by nlinarith only [hx'.1, hrad, hcentral, hpx]
  have hhi : x + max 1 (Real.sqrt L) ≤ n := by nlinarith only [hx'.2, hrad, hcentral, hqx]
  refine ⟨hlo, hhi, ?_⟩
  intro k hk
  refine ⟨integerWindow_le_sample x _ n hhi k hk, ?_⟩
  have hkx := integerWindow_distance x _ hlo (by positivity) k hk
  have he : (k : ℝ) - n * p = ((k : ℝ) - x) + (x - n * p) := by ring
  rw [he]
  have htri := abs_add_le ((k : ℝ) - x) (x - n * p)
  nlinarith only [htri, hkx, hx, hrad]

theorem binomialZ_bound_from_raw (p δ M : ℝ) (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ 1 - p)
    (hM : 0 ≤ M) (n k : ℕ) (hn : 1 ≤ n)
    (hraw : |(k : ℝ) - n * p| ≤ M * Real.sqrt (n : ℝ)) :
    |binomialZ p n k| ≤ M / δ := by
  have hp0 := hδ.trans_le hp
  have hq0 := hδ.trans_le hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hvar : δ ^ 2 ≤ p * (1 - p) := by nlinarith [mul_le_mul hp hq hδ.le hp0.le]
  have hroot : δ * Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * p * (1 - p)) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have h := mul_le_mul_of_nonneg_left hvar hn0.le
    nlinarith [Real.sq_sqrt hn0.le]
  have hs : 0 < Real.sqrt ((n : ℝ) * p * (1 - p)) := Real.sqrt_pos.2 (by positivity)
  unfold binomialZ
  simp only [Int.cast_natCast]
  rw [abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).2
  have h := mul_le_mul_of_nonneg_left hroot (div_nonneg hM hδ.le)
  have he : M / δ * (δ * Real.sqrt (n : ℝ)) = M * Real.sqrt (n : ℝ) := by field_simp
  rw [he] at h
  exact hraw.trans h

theorem noise_variance_central_half_double (P Q : CenteredFourthLaw) (p δ M : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hM : 0 ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hcentral : |(k : ℝ) - n * p| ≤ M * Real.sqrt (n : ℝ))
    (hlarge : 2 * M ≤ δ * Real.sqrt (n : ℝ)) :
    accumulatedNoiseVariance P Q p n / 2 ≤ (twoNoiseBlock P Q n k).secondMoment ∧
    (twoNoiseBlock P Q n k).secondMoment ≤ 2 * accumulatedNoiseVariance P Q p n := by
  have hlam := accumulatedNoiseVariance_nonneg P Q p ⟨by linarith, by linarith⟩ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden := mul_pos hδ (Real.sqrt_pos.2 hn0)
  have hclose := noise_variance_central_bound P Q p δ M hδ hp hq hM n k hn hk hcentral
  have herr : M * accumulatedNoiseVariance P Q p n / (δ * Real.sqrt (n : ℝ)) ≤
      accumulatedNoiseVariance P Q p n / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_le_mul_of_nonneg_right hlarge hlam]
  have h := abs_le.1 (hclose.trans herr)
  constructor <;> linarith

end BerryEsseen
