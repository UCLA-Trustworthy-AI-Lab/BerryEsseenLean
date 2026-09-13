import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptUniformClusterBudgets
import BerryEsseen.ManuscriptUniformCentralDerivative
import BerryEsseen.ManuscriptBinomialLimit

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_central_integer_range (p M : ℝ) (hp : p ∈ manuscriptInitialInterval)
    (hM : 0 ≤ M) (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hz : |binomialZ p n k| ≤ M) (hlarge : 2 * M ≤ (2 / 5) * Real.sqrt (n : ℝ)) :
    0 ≤ k ∧ k ≤ n ∧ |(k : ℝ) - (n : ℝ) * p| ≤ M * Real.sqrt (n : ℝ) := by
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hv := (bernoulli_variance_tau_bounds p hpdata.1).1
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg n)
  have hs : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hv.1
  have hs1 : Real.sqrt (p * (1 - p)) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hv.2
  have hraw : |(k : ℝ) - (n : ℝ) * p| ≤ M * Real.sqrt (n : ℝ) := by
    have he := binomialZ_scaling p hpdata.1 n hn k
    have he' : (k : ℝ) - n * p = Real.sqrt (p * (1 - p)) *
        (Real.sqrt (n : ℝ) * binomialZ p n k) := by
      rw [he]
      exact (mul_div_cancel₀ _ hs.ne').symm
    rw [he', abs_mul, abs_mul, abs_of_nonneg hs.le, abs_of_nonneg hr.le]
    have hh := mul_le_mul hs1 (mul_le_mul_of_nonneg_left hz hr.le)
      (by positivity : 0 ≤ Real.sqrt (n : ℝ) * |binomialZ p n k|) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul, mul_comm M] using hh
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := mul_le_mul_of_nonneg_right hlarge hr.le
  have hpLo := mul_le_mul_of_nonneg_left hp.1 hn0.le
  have hpHi := mul_le_mul_of_nonneg_left hpdata.2.1 hn0.le
  have hk0 : (0 : ℝ) ≤ k := by
    have hh := (abs_le.mp hraw).1
    nlinarith
  have hkn : (k : ℝ) ≤ n := by
    have hh := (abs_le.mp hraw).2
    nlinarith
  exact ⟨by exact_mod_cast hk0, by exact_mod_cast hkn, hraw⟩

/-- After the central window is fixed, reduce the two noise cutoffs together.
This supplies the central constraints and a sample-size lower bound, without
any counterexample sequence or division by a lower bound on the variance. -/
theorem manuscript_uniform_central_absorption (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (M γ : ℝ) (hM : 0 ≤ M) (hγ : 0 < γ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 100 ∧
      manuscriptLeakageCoefficient * d * manuscriptNoisePolynomial d d ≤ γ ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 1 ≤ N ∧
        ∀ (P Q : CenteredFourthLaw) (p : ℝ) (hp : p ∈ manuscriptInitialInterval),
          (∀ᵐ x ∂P.measure, |x| ≤ d) → (∀ᵐ x ∂Q.measure, |x| ≤ d) →
          ∀ n, N ≤ n → ∀ k : ℤ, |binomialZ p n k| ≤ M →
            0 < accumulatedNoiseVariance P Q p n → accumulatedNoiseVariance P Q p n ≤ d →
            ∀ u : ℝ, |u| ≤ 1 / 2 →
              normalizedDiscrepancy (standardizedTwoClusterLaw P Q p
                (manuscript_initial_parameter_bounds p hp).1) n
                (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤
                rawNormalizedConstant (bernoulliMeasure p) n -
                  c * accumulatedNoiseVariance P Q p n /
                    Real.sqrt (3 * accumulatedNoiseVariance P Q p n / (2 / 5) + d ^ 2) := by
  obtain ⟨s0, hs0, b0, hb0, Nd, hNd, hder⟩ := manuscript_uniform_central_derivative W S M hM
  let c0 := (3 / 1600 : ℝ) * b0
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  let q := fun d : ℝ => Real.sqrt (3 * d / (2 / 5) + d ^ 2)
  let F4 := fun d : ℝ => 3 * (d / (2 / 5)) ^ 2 + d ^ 2 * (d / (2 / 5))
  have hF4 : Tendsto F4 (𝓝 0) (𝓝 0) := by
    simpa only [F4, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add] using
      (show ContinuousAt F4 0 by dsimp [F4]; fun_prop).tendsto
  have hcent : Tendsto (fun d => manuscriptCentralErrorMajorant * manuscriptNoisePolynomial d d * q d)
      (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d => manuscriptCentralErrorMajorant * manuscriptNoisePolynomial d d * q d) 0 := by
      dsimp [manuscriptNoisePolynomial, q]
      fun_prop
    simpa [manuscriptNoisePolynomial, q] using hh.tendsto
  have hleak : Tendsto (fun d => manuscriptLeakageCoefficient * d * manuscriptNoisePolynomial d d)
      (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d => manuscriptLeakageCoefficient * d * manuscriptNoisePolynomial d d) 0 := by
      dsimp [manuscriptNoisePolynomial]
      fun_prop
    simpa [manuscriptNoisePolynomial] using hh.tendsto
  have hevent := (hF4.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 160000))).and
    ((hcent.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c0 / 4))).and
      (hleak.eventually (gt_mem_nhds hγ)))
  obtain ⟨η, hη, hηbudget⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨d, hd, hdhi⟩ := exists_between (lt_min hη (lt_min (by norm_num : (0 : ℝ) < 1 / 100) hs0))
  have hdη : d < η := hdhi.trans_le (min_le_left _ _)
  have hd100 : d ≤ 1 / 100 := (hdhi.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hds0 : d ≤ s0 := (hdhi.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hdsmall := hηbudget (y := d) (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hd] using hdη)
  have hr : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp
    (hr.eventually_ge_atTop (max (5 * M) (4 * manuscriptNormalizationBudget * q d / c0)))
  refine ⟨d, hd, hd100, hdsmall.2.2.le, c0 / 2, by positivity, max Nd Ns,
    hNd.trans (le_max_left _ _), ?_⟩
  intro P Q p hp hP hQ n hn k hz hlampos hlamhi u hu
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hn1 : 1 ≤ n := hNd.trans ((le_max_left Nd Ns).trans hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsample := hNs n ((le_max_right Nd Ns).trans hn)
  have hlarge : 2 * M ≤ (2 / 5) * Real.sqrt (n : ℝ) := by
    have hh := (le_max_left _ _).trans hsample
    linarith
  obtain ⟨hk0, hkn, hraw⟩ := manuscript_central_integer_range p M hp hM n hn1 k hz hlarge
  let l := k.toNat
  have hlk : (l : ℤ) = k := Int.toNat_of_nonneg hk0
  have hln : l ≤ n := by exact_mod_cast (show (l : ℤ) ≤ n by simpa only [hlk] using hkn)
  have hlreal : (l : ℝ) = k := by exact_mod_cast hlk
  have hsz : averageNoiseVariance P Q p ≤ d :=
    (averageNoiseVariance_le_accumulated P Q p ⟨hpdata.1.1.le, hpdata.1.2.le⟩ n hn1).trans hlamhi
  have hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16 := by
    have hvlo := hpdata.2.2
    nlinarith [hsz.trans hd100]
  have hdε : d ≤ 2 / 5 := hd100.trans (by norm_num)
  have hdl := hder p hp n ((le_max_left Nd Ns).trans hn) (averageNoiseVariance P Q p)
    ⟨averageNoiseVariance_nonneg P Q p ⟨hpdata.1.1.le, hpdata.1.2.le⟩, hsz.trans hds0⟩ l hln
    (by simpa only [hlk] using hz)
  have hfour : (twoNoiseBlock P Q n l).fourthMoment ≤ 1 / 160000 := by
    apply (noise_fourth_uniform_bound P Q p (2 / 5) d (by norm_num) hp.1 hpdata.2.1
      hd.le hP hQ n l hln).trans
    apply le_trans _ hdsmall.1.le
    dsimp only [F4]
    gcongr
  have hcomp := manuscript_twoCluster_central_error_budget B P Q p (2 / 5) d M
    (by norm_num) hp.1 hpdata.2.1 hd.le hM (hdε.trans hp.1) (hdε.trans hpdata.2.1) hP hQ hs
    n l hn1 hln hdl.2.1 hfour hdl.2.2 (by simpa only [hlreal] using hraw) hlarge hlampos u hu
  have hc := manuscript_central_coefficients_uniform B P Q p d b0 hp hdε hb0.le hP hQ hs n l hn1 hln hdl.1
  let lam := accumulatedNoiseVariance P Q p n
  let qlam := Real.sqrt (3 * lam / (2 / 5) + d ^ 2)
  have hqlam : 0 < qlam := Real.sqrt_pos.mpr (by dsimp [lam]; positivity)
  have hqle : qlam ≤ q d := by dsimp [qlam, q]; gcongr
  have hpoly : manuscriptNoisePolynomial lam d ≤ manuscriptNoisePolynomial d d := by
    dsimp [manuscriptNoisePolynomial]
    gcongr
  have hC0 : 0 ≤ manuscriptNormalizationBudget := by unfold manuscriptNormalizationBudget; have := cE_pos; have := phi0_pos; positivity
  have hE0 : 0 ≤ manuscriptCentralErrorMajorant := by unfold manuscriptCentralErrorMajorant manuscriptLeakageCoefficient; have := cE_pos; positivity
  have hsmallN : manuscriptNormalizationBudget * q d / Real.sqrt (n : ℝ) ≤ c0 / 4 := by
    have hh := (le_max_right _ _).trans hsample
    have hh' := (div_le_iff₀ hc0).mp hh
    apply (div_le_iff₀ hrpos).mpr
    nlinarith
  have heupper : manuscriptClusterCentralErrorCoefficient P Q p (2 / 5) d n l ≤
      manuscriptNormalizationBudget / Real.sqrt (n : ℝ) +
        manuscriptCentralErrorMajorant * manuscriptNoisePolynomial d d :=
    hc.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpoly hE0))
  have hupper0 : 0 ≤ manuscriptNormalizationBudget / Real.sqrt (n : ℝ) +
      manuscriptCentralErrorMajorant * manuscriptNoisePolynomial d d := by
    unfold manuscriptNoisePolynomial
    positivity
  have hemul := (mul_le_mul_of_nonneg_right heupper hqlam.le).trans
    (mul_le_mul_of_nonneg_left hqle hupper0)
  have heq : (manuscriptNormalizationBudget / Real.sqrt (n : ℝ) +
      manuscriptCentralErrorMajorant * manuscriptNoisePolynomial d d) * q d =
      manuscriptNormalizationBudget * q d / Real.sqrt (n : ℝ) +
        manuscriptCentralErrorMajorant * manuscriptNoisePolynomial d d * q d := by ring
  rw [heq] at hemul
  have heabs : manuscriptClusterCentralErrorCoefficient P Q p (2 / 5) d n l ≤ c0 / (2 * qlam) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * qlam)).mpr
    nlinarith only [hemul, hsmallN, hdsmall.2.1.le]
  have hgap := mul_le_mul_of_nonneg_right hc.1 hlampos.le
  have hgap' := div_le_div_of_nonneg_right hgap hqlam.le
  have herr := mul_le_mul_of_nonneg_left heabs hlampos.le
  have hRb : rawNormalizedConstant (bernoulliMeasure p) n =
      Real.sqrt (n : ℝ) * (Real.sqrt (p * (1 - p)) ^ 3 /
        (p * (1 - p) * (p ^ 2 + (1 - p) ^ 2))) * binomialKolmogorov p n := by
    rw [rawNormalizedConstant_bernoulli p hpdata.1 n hn1, binomialNormalizedConstant,
      manuscript_binomial_prefactor p hpdata.1 n,
      mul_assoc (n : ℝ) p (1 - p), Real.sqrt_mul (Nat.cast_nonneg n)]
    ring
  rw [← hRb] at hcomp
  simp only [hlreal] at hcomp
  change _ ≤ _ - c0 / 2 * lam / qlam
  change _ ≤ _ - _ * lam / qlam + lam * _ at hcomp
  have heid : lam * (c0 / (2 * qlam)) = c0 / 2 * lam / qlam := by ring
  rw [heid] at herr
  change c0 * lam / qlam ≤ manuscriptClusterCentralLossCoefficient P Q p n l * lam / qlam at hgap'
  change lam * manuscriptClusterCentralErrorCoefficient P Q p (2 / 5) d n l ≤ c0 / 2 * lam / qlam at herr
  have hehalf : c0 * lam / qlam = 2 * (c0 / 2 * lam / qlam) := by ring
  rw [hehalf] at hgap'
  linarith only [hcomp, hgap', herr]

end BerryEsseen
