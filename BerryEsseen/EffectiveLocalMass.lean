import BerryEsseen.EffectiveSmallVariance
import BerryEsseen.TwoClusterLocalMass

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

def appendixA : ℝ := (10 : ℝ) ^ 14

theorem exp_neg_le_phi0_sixty_four (x : ℝ) (hx : 1000 ≤ x) :
    Real.exp (-x) ≤ phi0 / 64 := by
  have he : (1000 : ℝ) ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h : Real.exp (-x) ≤ 1 / 1000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  linarith [phi0_effective_lower]

theorem effective_local_mass_density_budget :
    Real.exp (-appendixA) ≤ centralDensityFloor 2200000 / 64 ∧
    Real.exp (-4000000000000) ≤ Real.exp (-100) * (centralDensityFloor 2200000 / 32) := by
  have h1 := exp_neg_le_phi0_sixty_four 97580000000000 (by norm_num)
  have h2 := exp_neg_le_phi0_sixty_four 1579999999900 (by norm_num)
  have hD : 0 < Real.exp (-2420000000000) := Real.exp_pos _
  constructor
  · have h := mul_le_mul_of_nonneg_left h1 hD.le
    rw [← Real.exp_add] at h
    norm_num [appendixA, centralDensityFloor] at h ⊢
    convert h using 1 <;> ring
  · have h := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-2420000000100)).le
    rw [← Real.exp_add] at h
    have hid : Real.exp (-100) * (centralDensityFloor 2200000 / 32) =
        Real.exp (-2420000000100) * (phi0 / 32) := by
      unfold centralDensityFloor
      have he : Real.exp (-100) * Real.exp (-((2200000 : ℝ) ^ 2) / 2) = Real.exp (-2420000000100) := by
        rw [← Real.exp_add]
        norm_num
      calc
        _ = (Real.exp (-100) * Real.exp (-((2200000 : ℝ) ^ 2) / 2)) * (phi0 / 32) := by ring
        _ = _ := by rw [he]
    rw [hid]
    norm_num at h
    nlinarith [mul_pos (Real.exp_pos (-2420000000100)) phi0_pos]

theorem effective_noise_window_endpoint (lam t x k a : ℝ)
    (hlam : 1 / (10 : ℝ) ^ 12 ≤ lam) (ht : lam / 2 ≤ t)
    (hxk : |k - x| ≤ max 1 (Real.sqrt lam)) (ha : |a| ≤ 1 / 2) :
    |((x + a) - k) / Real.sqrt t| ≤ 2200000 := by
  have hL : 0 < lam := by linarith
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.mpr ht0
  have htsq := Real.sq_sqrt ht0.le
  have hLsq := Real.sq_sqrt hL.le
  have hnum : |(x + a) - k| ≤ max 1 (Real.sqrt lam) + 1 / 2 := by
    have htri := abs_add_le (x - k) a
    rw [abs_sub_comm x k] at htri
    have he : (x + a) - k = (x - k) + a := by ring
    rw [he]
    linarith
  rw [abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  by_cases hsmall : Real.sqrt lam ≤ 1
  · rw [max_eq_left hsmall] at hnum
    have hroot : (0.0000007 : ℝ) ≤ Real.sqrt t := by nlinarith
    linarith
  · rw [max_eq_right (le_of_not_ge hsmall)] at hnum
    have hroot : Real.sqrt lam ≤ (3 / 2) * Real.sqrt t := by nlinarith [Real.sqrt_nonneg lam]
    have ht1 : 1 / 2 ≤ Real.sqrt t := by nlinarith [Real.sqrt_nonneg lam]
    linarith

theorem effective_noise_block_window_mass (I : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (lam x a b : ℝ)
    (hlam : 1 / (10 : ℝ) ^ 12 ≤ lam)
    (htlo : lam / 2 ≤ (twoNoiseBlock P Q n k).secondMoment)
    (hthi : (twoNoiseBlock P Q n k).secondMoment ≤ 2 * lam)
    (hxk : |(k : ℝ) - x| ≤ max 1 (Real.sqrt lam))
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    (centralDensityFloor 2200000 / 32) / Real.sqrt lam ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo ((x + a) - k) ((x + b) - k)) := by
  have hL : 0 < lam := by linarith
  have ht : 0 < (twoNoiseBlock P Q n k).secondMoment := by linarith
  have hst := Real.sqrt_pos.mpr ht
  have hsL := Real.sqrt_pos.mpr hL
  have hE := effective_local_mass_density_budget.1
  have hD := centralDensityFloor_pos (2200000 : ℝ)
  have hraw := twoNoiseBlock_open_interval_lower I P Q (Real.exp (-appendixA)) (Real.exp_pos _).le hP hQ n k hn hk ht
    2200000 ((x + a) - k) ((x + b) - k) (by norm_num) (by linarith)
    (effective_noise_window_endpoint lam _ x k a hlam htlo hxk ha)
    (effective_noise_window_endpoint lam _ x k b hlam htlo hxk hb)
  have hnum : centralDensityFloor 2200000 / 16 ≤
      (((x + b) - k) - ((x + a) - k)) / 2 * centralDensityFloor 2200000 - 1.12 * Real.exp (-appendixA) := by
    have hm := mul_le_mul_of_nonneg_right hab hD.le
    nlinarith
  have hroot : Real.sqrt (twoNoiseBlock P Q n k).secondMoment ≤ 2 * Real.sqrt lam := by
    nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt hL.le]
  have hdiv : (centralDensityFloor 2200000 / 16) / (2 * Real.sqrt lam) ≤
      ((((x + b) - k) - ((x + a) - k)) / 2 * centralDensityFloor 2200000 - 1.12 * Real.exp (-appendixA)) /
        Real.sqrt (twoNoiseBlock P Q n k).secondMoment := div_le_div₀ ((div_nonneg hD.le (by norm_num : (0 : ℝ) ≤ 16)).trans hnum) hnum hst hroot
  apply (show (centralDensityFloor 2200000 / 32) / Real.sqrt lam ≤ _ from ?_).trans hraw
  convert hdiv using 1 <;> ring

theorem effective_local_mass_pointwise (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (x a b : ℝ) (hx : |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ))
    (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    Real.exp (-4000000000000) / Real.sqrt (n : ℝ) ≤
      (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x + a) (x + b)) := by
  let lam := accumulatedNoiseVariance P Q p n
  let r := Real.sqrt (n : ℝ)
  let K := integerWindow x (max 1 (Real.sqrt lam))
  let C := centralDensityFloor 2200000 / 32
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < r := Real.sqrt_pos.mpr hn0
  have hL : 0 < lam := by change _ ≤ lam at hlam; linarith
  have hC : 0 < C := div_pos (centralDensityFloor_pos _) (by norm_num)
  have hq : (2 / 5 : ℝ) ≤ 1 - p := by linarith [hp.2]
  have hε : Real.exp (-appendixA) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num [appendixA])
  have hLn : lam ≤ n := by
    have h := accumulatedNoiseVariance_le_noise_bound P Q p (Real.exp (-appendixA)) hpcc (Real.exp_pos _).le hP hQ n
    have he2 : Real.exp (-appendixA) ^ 2 ≤ 1 := by nlinarith [Real.exp_pos (-appendixA)]
    have hm := mul_le_mul_of_nonneg_left he2 hn0.le
    nlinarith only [h, hm]
  have hroot := effective_binomial_root_lower n hn
  have hlarge : 2 * ((3 : ℝ) + 1) ≤ (2 / 5) * Real.sqrt (n : ℝ) := by norm_num at hroot ⊢; linarith
  have hgeo := central_integer_window_geometry p (2 / 5) 3 lam x (by norm_num) hp.1 hq (by norm_num)
    n hn1 hLn hlarge hx
  have hK : K ⊆ Finset.range (n + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (by have h := (hgeo.2.2 k hk).1; omega)
  have hweights : ∀ k ∈ K, Real.exp (-100) / r ≤ binomialWeight p n k := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    have hzk := binomialZ_bound_from_raw p (2 / 5) (3 + 1) (by norm_num) hp.1 hq (by norm_num) n k hn1 hkgeo.2
    exact effective_binomial_wide S p hp n hn k hkgeo.1 (by norm_num at hzk; linarith)
  have hnoise : ∀ k ∈ K, C / Real.sqrt lam ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo ((x + a) - k) ((x + b) - k)) := by
    intro k hk
    have hkgeo := hgeo.2.2 k hk
    have ht := noise_variance_central_half_double P Q p (2 / 5) (3 + 1) (by norm_num) hp.1 hq (by norm_num)
      n k hn1 hkgeo.1 hkgeo.2 hlarge
    exact effective_noise_block_window_mass I P Q hP hQ n k hn1 hkgeo.1 lam x a b hlam ht.1 ht.2
      (integerWindow_distance x _ hgeo.1 (by positivity) k hk) ha hb hab
  have hprob := twoCluster_open_interval_lower_of_blocks P Q p hpcc n (x + a) (x + b) (by linarith) K hK
    (Real.exp (-100) / r) (C / Real.sqrt lam) (by positivity) (by positivity) hweights hnoise
  have hcard : Real.sqrt lam ≤ (K.card : ℝ) := (le_max_right 1 (Real.sqrt lam)).trans
    (integerWindow_card_lower x _ hgeo.1 (le_max_left _ _))
  have hcount := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ Real.exp (-100) / r * (C / Real.sqrt lam))
  have hid : Real.sqrt lam * (Real.exp (-100) / r * (C / Real.sqrt lam)) = Real.exp (-100) * C / r := by
    field_simp [(Real.sqrt_pos.mpr hL).ne']
  rw [hid] at hcount
  have hD := div_le_div_of_nonneg_right effective_local_mass_density_budget.2 hr.le
  exact hD.trans (hcount.trans (by simpa only [mul_assoc] using hprob))

theorem effective_local_mass (S : PublishedSignedSmoothing) (I : PublishedNonIIDBound)
    (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ Real.exp (-appendixA))
    (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ Real.exp (-appendixA))
    (n : ℕ) (hn : 10 ^ 100 ≤ n) (hlam : 1 / (10 : ℝ) ^ 12 ≤ accumulatedNoiseVariance P Q p n)
    (a b : ℝ) (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) (hab : 1 / 4 ≤ b - a) :
    Real.exp (-4000000000000) / Real.sqrt (n : ℝ) ≤
      sInf (Set.range (fun x : {x : ℝ // |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ)} =>
        (iidSumLaw (twoClusterMeasure P Q p) n).real (Ioo (x.val + a) (x.val + b)))) := by
  letI : Nonempty {x : ℝ // |x - (n : ℝ) * p| ≤ 3 * Real.sqrt (n : ℝ)} :=
    ⟨⟨n * p, by simp only [sub_self, abs_zero]; positivity⟩⟩
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact effective_local_mass_pointwise S I P Q p hp hP hQ n hn hlam x.val a b x.property ha hb hab

end BerryEsseen
