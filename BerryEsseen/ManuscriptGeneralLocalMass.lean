import BerryEsseen.LocalMassAssembly
import BerryEsseen.WindowGeometry
import BerryEsseen.ReflectionBounds

/-! The printed proof of the qualitative local-mass lemma: the original
endpoint radius, the [L/2,3L/2] variance window, and an upper-endpoint left
limit on the entire open interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def manuscriptGeneralLocalA (Lstar a b : ℝ) : ℝ :=
  Real.sqrt 2 * (max 1 (1 / Real.sqrt Lstar) + max |a| |b| / Real.sqrt Lstar)

def manuscriptGeneralLocalC1 (Lstar a b : ℝ) : ℝ :=
  (b - a) * Real.sqrt (2 / 3) * standardNormalDensity (manuscriptGeneralLocalA Lstar a b)

def manuscriptGeneralLocalEpsilon (Lstar a b : ℝ) : ℝ :=
  manuscriptGeneralLocalC1 Lstar a b / (4 * Real.sqrt 2 * (0.56 : ℝ))

theorem manuscriptGeneralLocalA_nonneg (Lstar a b : ℝ) :
    0 ≤ manuscriptGeneralLocalA Lstar a b := by
  unfold manuscriptGeneralLocalA
  have hm : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  positivity

theorem manuscriptGeneralLocalC1_pos (Lstar a b : ℝ) (hab : a < b) :
    0 < manuscriptGeneralLocalC1 Lstar a b := by
  unfold manuscriptGeneralLocalC1
  exact mul_pos (mul_pos (sub_pos.mpr hab) (Real.sqrt_pos.mpr (by norm_num)))
    (standardNormalDensity_pos _)

theorem manuscriptGeneralLocalEpsilon_pos (Lstar a b : ℝ) (hab : a < b) :
    0 < manuscriptGeneralLocalEpsilon Lstar a b := by
  unfold manuscriptGeneralLocalEpsilon
  exact div_pos (manuscriptGeneralLocalC1_pos Lstar a b hab) (by positivity)

theorem manuscript_general_window_endpoint (Lstar L t x k a b : ℝ)
    (hstar : 0 < Lstar) (hL : Lstar ≤ L) (ht : L / 2 ≤ t)
    (hk : |k - x| ≤ max 1 (Real.sqrt L)) :
    |(x + a - k) / Real.sqrt t| ≤ manuscriptGeneralLocalA Lstar a b := by
  have hL0 : 0 < L := hstar.trans_le hL
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.mpr hstar
  have hR := Real.sqrt_pos.mpr hL0
  have hT := Real.sqrt_pos.mpr ht0
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hratio : 1 ≤ Real.sqrt L / Real.sqrt Lstar :=
    (le_div_iff₀ hs).mpr (by simpa using Real.sqrt_le_sqrt hL)
  let m := max 1 (1 / Real.sqrt Lstar)
  let d := max |a| |b| / Real.sqrt Lstar
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm2 : 1 / Real.sqrt Lstar ≤ m := le_max_right _ _
  have hm0 : 0 ≤ m := by linarith
  have hd0 : 0 ≤ d := div_nonneg ((abs_nonneg a).trans (le_max_left _ _)) hs.le
  have hrad : max 1 (Real.sqrt L) ≤ m * Real.sqrt L := by
    apply max_le
    · have hh := mul_le_mul_of_nonneg_right hm2 hR.le
      have he : (1 / Real.sqrt Lstar) * Real.sqrt L = Real.sqrt L / Real.sqrt Lstar := by ring
      rw [he] at hh
      exact hratio.trans hh
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 hR.le
  have ha : |a| ≤ d * Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hratio
      ((abs_nonneg a).trans (le_max_left |a| |b|))
    dsimp only [d]
    calc
      |a| ≤ max |a| |b| := le_max_left _ _
      _ ≤ max |a| |b| * (Real.sqrt L / Real.sqrt Lstar) := by simpa using hh
      _ = _ := by ring
  have hdist : |x + a - k| ≤ (m + d) * Real.sqrt L := by
    have he : x + a - k = -(k - x) + a := by ring
    rw [he]
    have hh := abs_add_le (-(k - x)) a
    rw [abs_neg] at hh
    nlinarith only [hh, hk.trans hrad, ha]
  have hscale : Real.sqrt L ≤ Real.sqrt 2 * Real.sqrt t := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sq_sqrt hL0.le, Real.sq_sqrt ht0.le,
      mul_pos htwo hT, sq_nonneg (Real.sqrt L - Real.sqrt 2 * Real.sqrt t)]
  have hmul := mul_le_mul_of_nonneg_left hscale (add_nonneg hm0 hd0)
  rw [abs_div, abs_of_pos hT]
  apply (div_le_iff₀ hT).mpr
  unfold manuscriptGeneralLocalA
  change |x + a - k| ≤ Real.sqrt 2 * (m + d) * Real.sqrt t
  nlinarith only [hdist, hmul]

theorem manuscript_general_noise_variance_window (P Q : CenteredFourthLaw)
    (p δ M : ℝ) (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hM : 0 ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hcentral : |(k : ℝ) - n * p| ≤ M * Real.sqrt (n : ℝ))
    (hlarge : 2 * M ≤ δ * Real.sqrt (n : ℝ)) :
    accumulatedNoiseVariance P Q p n / 2 ≤ (twoNoiseBlock P Q n k).secondMoment ∧
    (twoNoiseBlock P Q n k).secondMoment ≤ 3 * accumulatedNoiseVariance P Q p n / 2 := by
  have hL := accumulatedNoiseVariance_nonneg P Q p ⟨by linarith, by linarith⟩ n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden := mul_pos hδ (Real.sqrt_pos.mpr hn0)
  have hclose := noise_variance_central_bound P Q p δ M hδ hp hq hM n k hn hk hcentral
  have herr : M * accumulatedNoiseVariance P Q p n / (δ * Real.sqrt (n : ℝ)) ≤
      accumulatedNoiseVariance P Q p n / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlarge hL]
  have hh := abs_le.mp (hclose.trans herr)
  constructor <;> linarith only [hh.1, hh.2]

theorem manuscript_general_noise_open_interval (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ᵐ y ∂P.measure, |y| ≤ ε) (hQ : ∀ᵐ y ∂Q.measure, |y| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (ht : 0 < (twoNoiseBlock P Q n k).secondMoment) (a b : ℝ) (hab : a < b) :
    normalCDF (b / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) -
      normalCDF (a / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) -
      2 * ((0.56 : ℝ) * ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) ≤
        (twoNoiseBlock P Q n k).measure.real (Ioo a b) := by
  have hall := twoNoiseBlock_normal_bound I P Q ε hε hP hQ n k hn hk ht
  have hb := strictCDF_uniform_bound (twoNoiseBlock P Q n k).measure
    (fun x => normalCDF (x / Real.sqrt (twoNoiseBlock P Q n k).secondMoment))
    (normalCDF_continuous.comp (by fun_prop)) 1
    ((0.56 : ℝ) * ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment)
    (fun x => by simpa only [one_mul] using hall x) b
  have ha := (abs_le.mp (hall a)).2
  rw [← strictCDF_sub_cdf_open_interval _ a b hab]
  simp only [one_mul] at hb
  linarith only [(abs_le.mp hb).1, ha]

theorem manuscript_general_gaussian_interval (Lstar L t x k a b : ℝ)
    (hstar : 0 < Lstar) (hL : Lstar ≤ L) (htlo : L / 2 ≤ t)
    (hthi : t ≤ 3 * L / 2) (hab : a < b)
    (hk : |k - x| ≤ max 1 (Real.sqrt L)) :
    manuscriptGeneralLocalC1 Lstar a b / Real.sqrt L ≤
      normalCDF ((x + b - k) / Real.sqrt t) - normalCDF ((x + a - k) / Real.sqrt t) := by
  have hL0 := hstar.trans_le hL
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.mpr ht0
  have hsL := Real.sqrt_pos.mpr hL0
  have ha := manuscript_general_window_endpoint Lstar L t x k a b hstar hL htlo hk
  have hb := manuscript_general_window_endpoint Lstar L t x k b a hstar hL htlo hk
  have hswap : manuscriptGeneralLocalA Lstar b a = manuscriptGeneralLocalA Lstar a b := by
    unfold manuscriptGeneralLocalA
    rw [max_comm |b| |a|]
  rw [hswap] at hb
  let A := manuscriptGeneralLocalA Lstar a b
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hs23 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 / 3 by norm_num)
  have hr : Real.sqrt (2 / 3 : ℝ) * Real.sqrt t ≤ Real.sqrt L := by
    nlinarith only [Real.sq_sqrt ht0.le, Real.sq_sqrt hL0.le, hsq, hthi, mul_pos hs23 hs, hsL.le]
  have hn := normalCDF_interval_central_lower A ((x + a - k) / Real.sqrt t)
    ((x + b - k) / Real.sqrt t) (manuscriptGeneralLocalA_nonneg Lstar a b) ha hb
    (div_le_div_of_nonneg_right (by linarith : x + a - k ≤ x + b - k) hs.le)
  have hD : centralDensityFloor A = standardNormalDensity A := by
    rw [standardNormalDensity_formula]
    rfl
  rw [hD] at hn
  have hcoef : manuscriptGeneralLocalC1 Lstar a b * Real.sqrt t ≤
      (b - a) * standardNormalDensity A * Real.sqrt L := by
    have hm := mul_le_mul_of_nonneg_left hr
      (mul_nonneg (sub_pos.mpr hab).le (standardNormalDensity_pos A).le)
    unfold manuscriptGeneralLocalC1
    change (b - a) * Real.sqrt (2 / 3) * standardNormalDensity A * Real.sqrt t ≤ _
    nlinarith only [hm]
  have hfrac : manuscriptGeneralLocalC1 Lstar a b / Real.sqrt L ≤
      ((b - a) / Real.sqrt t) * standardNormalDensity A := by
    apply (div_le_iff₀ hsL).mpr
    apply (le_of_mul_le_mul_right · hs)
    · convert hcoef using 1 <;> field_simp <;> ring
  apply hfrac.trans
  convert hn using 1 <;> ring

theorem manuscript_general_noise_open_budget (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ᵐ y ∂P.measure, |y| ≤ ε) (hQ : ∀ᵐ y ∂Q.measure, |y| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (Lstar L x a b : ℝ)
    (hstar : 0 < Lstar) (hL : Lstar ≤ L) (hab : a < b)
    (htlo : L / 2 ≤ (twoNoiseBlock P Q n k).secondMoment)
    (hthi : (twoNoiseBlock P Q n k).secondMoment ≤ 3 * L / 2)
    (hxk : |(k : ℝ) - x| ≤ max 1 (Real.sqrt L)) :
    (manuscriptGeneralLocalC1 Lstar a b - 2 * Real.sqrt 2 * (0.56 : ℝ) * ε) / Real.sqrt L ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo (x + a - k) (x + b - k)) := by
  let t := (twoNoiseBlock P Q n k).secondMoment
  have hL0 := hstar.trans_le hL
  have ht0 : 0 < t := by dsimp [t]; linarith
  have hs := Real.sqrt_pos.mpr ht0
  have hsL := Real.sqrt_pos.mpr hL0
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hG := manuscript_general_gaussian_interval Lstar L t x k a b hstar hL htlo hthi hab hxk
  have hBE := manuscript_general_noise_open_interval I P Q ε hε hP hQ n k hn hk ht0
    (x + a - k) (x + b - k) (by linarith)
  have hscale : Real.sqrt L ≤ Real.sqrt 2 * Real.sqrt t := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sq_sqrt hL0.le, Real.sq_sqrt ht0.le,
      mul_pos htwo hs, sq_nonneg (Real.sqrt L - Real.sqrt 2 * Real.sqrt t)]
  have herror : (0.56 : ℝ) * ε / Real.sqrt t ≤ Real.sqrt 2 * (0.56 : ℝ) * ε / Real.sqrt L := by
    apply (div_le_div_iff₀ hs hsL).mpr
    have hm := mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.56) hε)
    nlinarith only [hm]
  change _ ≤ (twoNoiseBlock P Q n k).measure.real _
  change _ ≤ (twoNoiseBlock P Q n k).measure.real _ at hBE
  have he : (manuscriptGeneralLocalC1 Lstar a b - 2 * Real.sqrt 2 * (0.56 : ℝ) * ε) / Real.sqrt L =
      manuscriptGeneralLocalC1 Lstar a b / Real.sqrt L -
      2 * (Real.sqrt 2 * (0.56 : ℝ) * ε / Real.sqrt L) := by ring
  rw [he]
  linarith only [hG, hBE, herror]

theorem manuscript_general_noise_block_window (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ∀ᵐ y ∂P.measure, |y| ≤ ε) (hQ : ∀ᵐ y ∂Q.measure, |y| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (Lstar L x a b : ℝ)
    (hstar : 0 < Lstar) (hL : Lstar ≤ L) (hab : a < b)
    (htlo : L / 2 ≤ (twoNoiseBlock P Q n k).secondMoment)
    (hthi : (twoNoiseBlock P Q n k).secondMoment ≤ 3 * L / 2)
    (hxk : |(k : ℝ) - x| ≤ max 1 (Real.sqrt L))
    (heps : ε ≤ manuscriptGeneralLocalEpsilon Lstar a b) :
    manuscriptGeneralLocalC1 Lstar a b / (2 * Real.sqrt L) ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo (x + a - k) (x + b - k)) := by
  have hh := manuscript_general_noise_open_budget I P Q ε hε hP hQ n k hn hk
    Lstar L x a b hstar hL hab htlo hthi hxk
  have he : ε * (4 * Real.sqrt 2 * (0.56 : ℝ)) ≤ manuscriptGeneralLocalC1 Lstar a b :=
    (le_div_iff₀ (by positivity)).mp heps
  have hb : manuscriptGeneralLocalC1 Lstar a b / 2 ≤
      manuscriptGeneralLocalC1 Lstar a b - 2 * Real.sqrt 2 * (0.56 : ℝ) * ε := by
    nlinarith only [he]
  have hdiv := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg L)
  have hdiv' : manuscriptGeneralLocalC1 Lstar a b / (2 * Real.sqrt L) ≤
      (manuscriptGeneralLocalC1 Lstar a b - 2 * Real.sqrt 2 * (0.56 : ℝ) * ε) / Real.sqrt L := by
    convert hdiv using 1 <;> ring
  exact hdiv'.trans hh

/-- The original proof uses the integer window bound R+2. -/
theorem manuscript_general_integer_window_geometry (p δ R L x : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ 1 - p) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) (hL : L ≤ n)
    (hlarge : 2 * (R + 2) ≤ δ * Real.sqrt (n : ℝ))
    (hx : |x - (n : ℝ) * p| ≤ R * Real.sqrt (n : ℝ)) :
    0 ≤ x - max 1 (Real.sqrt L) ∧ x + max 1 (Real.sqrt L) ≤ n ∧
    ∀ k ∈ integerWindow x (max 1 (Real.sqrt L)), k ≤ n ∧
      |(k : ℝ) - n * p| ≤ (R + 2) * Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  have hr0 := Real.sqrt_nonneg (n : ℝ)
  have hr1 : 1 ≤ Real.sqrt (n : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  have hrad0 : max 1 (Real.sqrt L) ≤ 1 + Real.sqrt (n : ℝ) := by
    apply max_le
    · linarith
    · have := Real.sqrt_le_sqrt hL; linarith
  have hrad : max 1 (Real.sqrt L) ≤ 2 * Real.sqrt (n : ℝ) := by
    linarith only [hrad0, hr1]
  have hscale := mul_le_mul_of_nonneg_right hlarge hr0
  have hcentral : (R + 2) * Real.sqrt (n : ℝ) ≤ δ * n := by
    have he : δ * Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = δ * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]
    rw [he] at hscale
    nlinarith only [hscale, mul_nonneg (by linarith : 0 ≤ R + 2) hr0]
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


end BerryEsseen
