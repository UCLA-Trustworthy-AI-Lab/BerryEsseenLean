import BerryEsseen.EffectiveCentralDerivative
import BerryEsseen.PublishedNonuniform
import BerryEsseen.SmallVarianceSequence

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem effective_cluster_prefactor_bounds (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ Icc (2 / 5) (9 / 20)) (hε : ε ∈ Icc 0 0.001)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε) :
    (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) ∈ Icc (1 / 2) 1 := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hr := clusterThirdAbsoluteMoment_pos P Q p hp01
  have hs := pow_pos (Real.sqrt_pos.mpr (clusterVariance_pos P Q p hp01)) 3
  have hlo := thirdMoment_ge_one (standardizedTwoClusterLaw P Q p hp01)
  have hhi := effective_standardized_cluster_moment P Q p ε hp hε hP hQ hp01
  rw [standardizedTwoClusterLaw_third] at hlo hhi
  have hlo' := (le_div_iff₀ hs).mp hlo
  have hhi' := (div_le_iff₀ hs).mp hhi
  constructor
  · apply (le_div_iff₀ hr).mpr
    nlinarith only [hhi', hs]
  · apply (div_le_one hr).mpr
    simpa only [one_mul] using hlo'

theorem effective_binomial_raw_distance (p : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (n k : ℕ) (hn : 1 ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    |(k : ℝ) - n * p| ≤ (5 / 2) * Real.sqrt (n : ℝ) := by
  have hb := effective_binomial_parameters p hp
  have hv := mul_pos hb.1.1 (sub_pos.mpr hb.1.2)
  have he := binomialZ_scaling p hb.1 n hn k
  have ht : (k : ℝ) - n * p = Real.sqrt (p * (1 - p)) * (Real.sqrt (n : ℝ) * binomialZ p n k) := by
    rw [he]
    simp only [Int.cast_natCast, mul_div_cancel₀ _ (Real.sqrt_pos.mpr hv).ne']
  rw [ht, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := mul_le_mul hb.2.2.1 (mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg (n : ℝ)))
    (by positivity : 0 ≤ Real.sqrt (n : ℝ) * |binomialZ p n k|) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith only [h]

theorem binomialNormalizedConstant_factorization (p : ℝ) (hp : p ∈ Ioo 0 1) (n : ℕ) :
    Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 / (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) *
      binomialKolmogorov p n = binomialNormalizedConstant p n := by
  have hv := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hs := (Real.sqrt_pos.mpr hv).ne'
  have hτ : 0 < p ^ 2 + (1 - p) ^ 2 := by nlinarith [sq_pos_of_pos hp.1, sq_nonneg (1 - p)]
  unfold binomialNormalizedConstant
  rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n), pow_succ, Real.sq_sqrt hv.le]
  field_simp [hv.ne', hτ.ne', hp.1.ne', (sub_pos.mpr hp.2).ne']
  <;> ring

theorem effective_central_coefficient_bounds (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n) (hz : |binomialZ p n k| ≤ 5) :
    (9 / (10 : ℝ) ^ 8) ≤ clusterCentralLossCoefficient P Q p n k ∧
    clusterCentralErrorCoefficient P Q p (2 / 5) ε n k ≤
      200 / Real.sqrt (n : ℝ) + 500000 * (accumulatedNoiseVariance P Q p n + ε ^ 2) := by
  let A := Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p
  let r := Real.sqrt (n : ℝ)
  let b := binomialWeight p n k
  let lam := accumulatedNoiseVariance P Q p n
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hA : A ∈ Icc (1 / 2) 1 := effective_cluster_prefactor_bounds P Q p ε hp ⟨hε.1, by linarith [hε.2]⟩ hP hQ
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have hb0 : 0 ≤ b := binomialWeight_nonneg p hpcc n k
  have hrb0 : 0 ≤ r * b := mul_nonneg hr.le hb0
  have hl := (effective_binomial_central S p hp n hn k hk hz).2.2
  have hu := effective_binomial_mass_upper B p hp n k (by omega)
  have hrblo : 1 / (10 : ℝ) ^ 6 ≤ r * b := by
    have h := (div_le_iff₀ hr).mp hl
    nlinarith only [h]
  have hrbhi : r * b ≤ 2 := by
    have h := (le_div_iff₀ hr).mp hu
    nlinarith only [h]
  have hAloss := mul_le_mul hA.1 hrblo (by positivity : (0 : ℝ) ≤ 1 / 10 ^ 6) (by linarith [hA.1] : 0 ≤ A)
  have hAerr := mul_le_mul hA.2 hrbhi hrb0 (by norm_num : (0 : ℝ) ≤ 1)
  have hls : 0 ≤ lam := accumulatedNoiseVariance_nonneg P Q p hpcc n
  have hv : (0.24 : ℝ) ≤ p * (1 - p) := by nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hbase : (56 * cE + 48 * phi0) / (p * (1 - p) * r) ≤ 200 / r := by
    apply (div_le_iff₀ (mul_pos (by linarith : 0 < p * (1 - p)) hr)).mpr
    have hid : 200 / r * (p * (1 - p) * r) = 200 * (p * (1 - p)) := by field_simp
    rw [hid]
    nlinarith [cE_numeric_bounds.2, phi0_lt_two_fifths]
  have hcoef : 11000 * A * (r * b) + 128 * cE * A / (2 / 5) ≤ 22132 := by
    have hh := mul_le_mul_of_nonneg_left hA.2 cE_pos.le
    nlinarith [cE_numeric_bounds.2]
  have hD : 3 * lam / (2 / 5) ^ 2 + ε ^ 2 / (2 / 5) ≤ 20 * (lam + ε ^ 2) := by
    norm_num
    nlinarith [sq_nonneg ε]
  have hm := mul_le_mul hcoef hD (by positivity : 0 ≤ 3 * lam / (2 / 5) ^ 2 + ε ^ 2 / (2 / 5)) (by norm_num : (0 : ℝ) ≤ 22132)
  constructor
  · change 9 / (10 : ℝ) ^ 8 ≤ 3 / 16 * A * (r * b)
    nlinarith only [hAloss]
  · change (56 * cE + 48 * phi0) / (p * (1 - p) * r) +
        (11000 * A * (r * b) + 128 * cE * A / (2 / 5)) * (3 * lam / (2 / 5) ^ 2 + ε ^ 2 / (2 / 5)) ≤ _
    nlinarith [sq_nonneg ε]

theorem effective_small_variance_absorption (n : ℕ) (hn : 10 ^ 100 ≤ n) (ε lam C E : ℝ)
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12)) (hlam : lam ∈ Ioc 0 (1 / (10 : ℝ) ^ 12))
    (hC : 9 / (10 : ℝ) ^ 8 ≤ C)
    (hE : E ≤ 200 / Real.sqrt (n : ℝ) + 500000 * (lam + ε ^ 2)) :
    -C * lam / Real.sqrt (3 * lam / (2 / 5) + ε ^ 2) + lam * E ≤
      -(5 / (10 : ℝ) ^ 9 * lam / Real.sqrt (5 * lam + ε ^ 2)) := by
  let q := Real.sqrt (3 * lam / (2 / 5) + ε ^ 2)
  let Q := Real.sqrt (5 * lam + ε ^ 2)
  have hq : 0 < q := Real.sqrt_pos.mpr (by have := hlam.1; positivity)
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by have := hlam.1; positivity)
  have hq2 := Real.sq_sqrt (show 0 ≤ 3 * lam / (2 / 5) + ε ^ 2 by have := hlam.1; positivity)
  have hQ2 := Real.sq_sqrt (show 0 ≤ 5 * lam + ε ^ 2 by have := hlam.1; positivity)
  have hqq : q ≤ 2 * Q := by
    change q ^ 2 = _ at hq2
    change Q ^ 2 = _ at hQ2
    nlinarith [sq_nonneg ε]
  have hε2 : ε ^ 2 ≤ 1 / (10 : ℝ) ^ 24 := by
    have h := pow_le_pow_left₀ hε.1 hε.2 2
    norm_num at h ⊢
    exact h
  have hQsmall : Q ≤ 1 / 400000 := by
    change Q ^ 2 = _ at hQ2
    nlinarith [hlam.2]
  have hr := effective_binomial_root_lower n hn
  have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 200) (by positivity : (0 : ℝ) < 10 ^ 50) hr
  have hEsmall : E ≤ 1 / 100000 := by nlinarith [hlam.2]
  have hEabs : E ≤ (1 / (10 : ℝ) ^ 8) / Q := by
    apply (le_div_iff₀ hQ).mpr
    have hh := mul_le_mul_of_nonneg_right hEsmall hQ.le
    nlinarith only [hh, hQsmall]
  have hCloss : (9 / (10 : ℝ) ^ 8) / (2 * Q) ≤ C / q :=
    div_le_div₀ (by positivity) hC hq hqq
  have hCm := mul_le_mul_of_nonneg_right hCloss hlam.1.le
  have hEm := mul_le_mul_of_nonneg_left hEabs hlam.1.le
  have hCp : 0 ≤ lam / Q := div_nonneg hlam.1.le hQ.le
  change -C * lam / q + lam * E ≤ -(5 / (10 : ℝ) ^ 9 * lam / Q)
  have hcId : (9 / (10 : ℝ) ^ 8) / (2 * Q) * lam = (9 / (2 * (10 : ℝ) ^ 8)) * (lam / Q) := by ring
  have heId : lam * ((1 / (10 : ℝ) ^ 8) / Q) = (1 / (10 : ℝ) ^ 8) * (lam / Q) := by ring
  rw [hcId] at hCm
  rw [heId] at hEm
  rw [show -C * lam / q = -(C / q * lam) by ring,
    show 5 / (10 : ℝ) ^ 9 * lam / Q = (5 / (10 : ℝ) ^ 9) * (lam / Q) by ring]
  nlinarith only [hCm, hEm, hCp]

theorem effective_small_variance_central (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 10 ^ 100 ≤ n) (hk : k ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12))
    (hz : |binomialZ p n k| ≤ 5) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n
      (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
      binomialNormalizedConstant p n -
        5 / (10 : ℝ) ^ 9 * accumulatedNoiseVariance P Q p n /
          Real.sqrt (5 * accumulatedNoiseVariance P Q p n + ε ^ 2) := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hn1 : 1 ≤ n := by omega
  have hs0 := averageNoiseVariance_nonneg P Q p hpcc
  have hsle := (averageNoiseVariance_le_accumulated P Q p hpcc n hn1).trans hlam.2
  have hv : (0.24 : ℝ) ≤ p * (1 - p) := by nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hp.2)]
  have hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16 := by linarith
  have hd := effective_central_gaussian_derivative S B p (averageNoiseVariance P Q p) hp ⟨hs0, hsle⟩ n k hn hk hz
  have hcentral := effective_binomial_raw_distance p hp n k hn1 hz
  have hroot := effective_binomial_root_lower n hn
  have hlarge : 2 * (5 / 2 : ℝ) ≤ (2 / 5) * Real.sqrt (n : ℝ) := by norm_num at hroot ⊢; linarith
  have hc := twoCluster_central_error_budget B P Q p (2 / 5) ε (5 / 2) (by norm_num) hp.1 (by linarith [hp.2])
    hε.1 (by norm_num) (by linarith [hε.2, hp.1]) (by linarith [hε.2, hp.2]) hP hQ hs n k hn1 hk hd.1 hd.2 hcentral hlarge hlam.1 u hu
  rw [binomialNormalizedConstant_factorization p hp01 n] at hc
  have hcoef := effective_central_coefficient_bounds S B P Q p ε hp hε hP hQ n k hn hk hz
  have ha := effective_small_variance_absorption n hn ε (accumulatedNoiseVariance P Q p n)
    (clusterCentralLossCoefficient P Q p n k) (clusterCentralErrorCoefficient P Q p (2 / 5) ε n k) hε hlam hcoef.1 hcoef.2
  rw [neg_mul, neg_div] at ha
  linarith only [hc, ha]

theorem effective_small_variance_far_argument (p s : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hs : s ∈ Icc 0 (1 / (10 : ℝ) ^ 12)) (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (k : ℤ) (hz : 5 < |binomialZ p n k|) (u : ℝ) (hu : |u| ≤ 1 / 2) :
    (4.9 : ℝ) ≤ |((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * (p * (1 - p) + s))| := by
  let r := Real.sqrt (n : ℝ)
  let a := Real.sqrt (p * (1 - p))
  let σ := Real.sqrt (p * (1 - p) + s)
  let z := binomialZ p n k
  have hb := effective_binomial_parameters p hp
  have hsc := effective_small_variance_scale p s hp hs
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  have ha : 0 < a := by have h := hb.2.1; change (0.48 : ℝ) ≤ a at h; linarith
  have hσ : 0 < σ := by have h := hsc.1.1; change (0.48 : ℝ) ≤ σ at h; linarith
  have hratio : (0.99 : ℝ) ≤ a / σ := by
    have h := (abs_le.mp hsc.2.2).1
    change -(5 * s) ≤ a / σ - 1 at h
    nlinarith [hs.2]
  have hprod : (4.95 : ℝ) ≤ |z| * (a / σ) := by
    have h := mul_le_mul (show (5 : ℝ) ≤ |z| from hz.le) hratio (by norm_num : (0 : ℝ) ≤ 0.99) (abs_nonneg z)
    nlinarith only [h]
  have hroot := effective_binomial_root_lower n hn
  have htail : |u / (r * σ)| ≤ 0.001 := by
    rw [abs_div, abs_of_pos (mul_pos hr hσ)]
    apply (div_le_iff₀ (mul_pos hr hσ)).mpr
    have hnr : (10000 : ℝ) ≤ r := by change _ ≤ r at hroot; norm_num at hroot; linarith
    have hmul := mul_le_mul hnr hsc.1.1 (by norm_num : (0 : ℝ) ≤ 0.48) hr.le
    change 10000 * (0.48 : ℝ) ≤ r * σ at hmul
    nlinarith only [hu, hmul]
  have hid : ((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * (p * (1 - p) + s)) =
      z * (a / σ) + u / (r * σ) := by
    dsimp only [z, a, σ, r, binomialZ]
    rw [mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_mul (Nat.cast_nonneg n)]
    field_simp [show Real.sqrt (p * (1 - p)) ≠ 0 from ha.ne']
    <;> ring
  rw [hid]
  have htri := abs_add_le (z * (a / σ) + u / (r * σ)) (-(u / (r * σ)))
  rw [← sub_eq_add_neg, add_sub_cancel_right, abs_neg, abs_mul, abs_of_pos (div_pos ha hσ)] at htri
  nlinarith only [htri, hprod, htail]

def effectiveSmallVarianceGap (lam ε : ℝ) : ℝ :=
  min (5 / (10 : ℝ) ^ 9 * lam / Real.sqrt (5 * lam + ε ^ 2)) (1 / 10)

theorem effectiveSmallVarianceGap_nonneg (lam ε : ℝ) (hlam : 0 ≤ lam) :
    0 ≤ effectiveSmallVarianceGap lam ε := by unfold effectiveSmallVarianceGap; positivity

theorem effective_small_variance_positive_pointwise (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12)) (x : ℝ) :
    normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n x ≤
      binomialNormalizedConstant p n - effectiveSmallVarianceGap (accumulatedNoiseVariance P Q p n) ε := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hpcc : p ∈ Icc 0 1 := ⟨hp01.1.le, hp01.2.le⟩
  have hn1 : 1 ≤ n := by omega
  let a := Real.sqrt ((n : ℝ) * clusterVariance P Q p)
  let t := a * x + n * p
  let k : ℤ := round t
  let u := t - k
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast (by omega : 0 < n)) (clusterVariance_pos P Q p hp01))
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hx : ((k : ℝ) + u - (n : ℝ) * p) / a = x := by
    dsimp only [u, t]
    field_simp
    <;> ring
  by_cases hz : |binomialZ p n k| ≤ 5
  · have hk := effective_binomial_central_index p hp n hn k (by linarith)
    have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.1
    have hzNat : |binomialZ p n (k.toNat : ℤ)| ≤ 5 := by rwa [hkcast]
    have hc := effective_small_variance_central S B P Q p ε hp hε hP hQ n k.toNat hn hk.2 hlam hzNat u hu
    have hkReal : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hkcast
    change normalizedDiscrepancy _ n (((k.toNat : ℝ) + u - n * p) / a) ≤ _ at hc
    rw [hkReal, hx] at hc
    apply hc.trans
    exact sub_le_sub_left (min_le_left _ _) _
  · have hs0 := averageNoiseVariance_nonneg P Q p hpcc
    have hsle := (averageNoiseVariance_le_accumulated P Q p hpcc n hn1).trans hlam.2
    have hfar := effective_small_variance_far_argument p (averageNoiseVariance P Q p) hp ⟨hs0, hsle⟩ n hn k (lt_of_not_ge hz) u hu
    have hV : p * (1 - p) + averageNoiseVariance P Q p = clusterVariance P Q p := by
      unfold clusterVariance averageNoiseVariance
      ring
    rw [hV] at hfar
    change (4.9 : ℝ) ≤ |((k : ℝ) + u - n * p) / a| at hfar
    rw [hx] at hfar
    have hD := normalizedDiscrepancy_far_four_point_nine U (standardizedTwoClusterLaw P Q p hp01) n hn1 x hfar
    have hR := effective_binomial_constant_lower S p hp n hn
    have hgap : effectiveSmallVarianceGap (accumulatedNoiseVariance P Q p n) ε ≤ 1 / 10 := min_le_right _ _
    linarith only [hD, hR, hgap]

theorem effective_small_variance_positive (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ∈ Ioc 0 (1 / (10 : ℝ) ^ 12)) :
    sSup (Set.range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) ≤
      binomialNormalizedConstant p n - effectiveSmallVarianceGap (accumulatedNoiseVariance P Q p n) ε := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact effective_small_variance_positive_pointwise S B U P Q p ε hp hε hP hQ n hn hlam x

theorem effective_small_variance (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (U : PublishedNonuniformBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ Icc (2 / 5) (9 / 20))
    (hε : ε ∈ Icc 0 (1 / (10 : ℝ) ^ 12))
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n : ℕ) (hn : 10 ^ 100 ≤ n)
    (hlam : accumulatedNoiseVariance P Q p n ≤ 1 / (10 : ℝ) ^ 12) :
    sSup (Set.range (normalizedDiscrepancy (standardizedTwoClusterLaw P Q p (effective_binomial_parameters p hp).1) n)) ≤
      binomialNormalizedConstant p n ∧ binomialNormalizedConstant p n < cE := by
  have hp01 := (effective_binomial_parameters p hp).1
  have hn1 : 1 ≤ n := by omega
  refine ⟨?_, binomialNormalizedConstant_lt_cE B p hp01 n hn1⟩
  have hl0 := accumulatedNoiseVariance_nonneg P Q p ⟨hp01.1.le, hp01.2.le⟩ n
  by_cases hz : accumulatedNoiseVariance P Q p n = 0
  · rw [zero_noise_standardizedLaw P Q p hp01 n hn1 hz, ← binomialNormalizedConstant_eq_sup p hp01 n hn1]
  · have hpositive : 0 < accumulatedNoiseVariance P Q p n := lt_of_le_of_ne hl0 (Ne.symm hz)
    have h := effective_small_variance_positive S B U P Q p ε hp hε hP hQ n hn ⟨hpositive, hlam⟩
    exact h.trans (sub_le_self _ (effectiveSmallVarianceGap_nonneg _ _ hl0))

end BerryEsseen
