import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.ManuscriptUniformClusterBudgets
import BerryEsseen.ManuscriptOutsideGaussian

/-! The manuscript's fixed-window far budget, with separate treatment of
integer cells outside the binomial support by Gaussian exponential tails. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem manuscript_uniform_far_budget (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing)
    (B : PublishedBernoulliBound) (γ : ℝ) (hγ : 0 < γ) (hgap : 8 * γ = cE - phi0)
    (M : ℝ) (_hM : 0 ≤ M)
    (htail : ∀ p ∈ manuscriptInitialInterval, ∀ z : ℝ, M < |z| →
      max (binomialUpperEnvelope p z) (binomialLowerEnvelope p z) ≤ γ)
    (d : ℝ) (hd : 0 < d) (hd100 : d ≤ 1 / 100)
    (hleak : manuscriptLeakageCoefficient * d * manuscriptNoisePolynomial d d ≤ γ) :
    ∃ N : ℕ, 25 ≤ N ∧ ∀ (P Q : CenteredFourthLaw) (p : ℝ)
      (hp : p ∈ manuscriptInitialInterval),
      (∀ᵐ x ∂P.measure, |x| ≤ d) → (∀ᵐ x ∂Q.measure, |x| ≤ d) →
      ∀ n ≥ N, accumulatedNoiseVariance P Q p n ≤ d →
      ∀ k : ℤ, M < |binomialZ p n k| → ∀ u : ℝ, |u| ≤ 1 / 2 →
        normalizedDiscrepancy
          (standardizedTwoClusterLaw P Q p (manuscript_initial_parameter_bounds p hp).1) n
          (((k : ℝ) + u - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * clusterVariance P Q p)) ≤ cE - 2 * γ := by
  have hC : 0 ≤ manuscriptNormalizationBudget := by
    unfold manuscriptNormalizationBudget
    have := cE_pos
    have := phi0_pos
    positivity
  have hL : 0 ≤ manuscriptLeakageCoefficient := by
    unfold manuscriptLeakageCoefficient
    have := cE_pos
    positivity
  have hK : manuscriptInitialInterval ⊆ Ioo (0 : ℝ) 1 :=
    fun p hp => (manuscript_initial_parameter_bounds p hp).1
  obtain ⟨Nb, hNb⟩ := compact_binomial_branches W S manuscriptInitialInterval isCompact_Icc hK
    (γ / 2) (by positivity)
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_const_nhds (x := (manuscriptNormalizationBudget + 125 * phi0) * d)).div_atTop hroot
  obtain ⟨Nr, hNr⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < γ / 2)))
  obtain ⟨No, hNo25, hNo⟩ := manuscript_outside_gaussian_cutoff γ hγ
  refine ⟨max Nb (max Nr No), hNo25.trans ((le_max_right _ _).trans (le_max_right _ _)), ?_⟩
  intro P Q p hp hP hQ n hn hlam k hz u hu
  have hnNb : Nb ≤ n := (le_max_left _ _).trans hn
  have hnNr : Nr ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnNo : No ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn25 : 25 ≤ n := hNo25.trans hnNo
  have hn1 : 1 ≤ n := by omega
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hpI : p ∈ Icc 0 1 := ⟨hpdata.1.1.le, hpdata.1.2.le⟩
  have hpcentral : p ∈ Icc (2 / 5) (3 / 5) := ⟨hp.1, hp.2.trans (by norm_num)⟩
  let lam := accumulatedNoiseVariance P Q p n
  let s := averageNoiseVariance P Q p
  let r := Real.sqrt (n : ℝ)
  have hlam0 : 0 ≤ lam := accumulatedNoiseVariance_nonneg P Q p hpI n
  have hs0 : 0 ≤ s := averageNoiseVariance_nonneg P Q p hpI
  have hsbound : s ≤ lam := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hnreal hs0
  have hsmall : s ≤ p * (1 - p) / 16 := by
    have hpar := hpdata.2.2
    change lam ≤ d at hlam
    nlinarith only [hsbound, hlam, hd100, hpar]
  have hdpar : d ≤ 2 / 5 := hd100.trans (by norm_num)
  have hcoeff := manuscript_cluster_uniform_coefficients P Q p d hp hdpar hP hQ hsmall
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hrn : r ≤ (n : ℝ) := by nlinarith only [hr1, hr2, mul_le_mul_of_nonneg_left hr1 hr.le]
  have hsdiv : s ≤ d / r := by
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_right hrn hs0
    change lam ≤ d at hlam
    have he : (n : ℝ) * s = lam := rfl
    rw [he] at hh
    nlinarith only [hh, hlam]
  have hpoly0 : 0 ≤ manuscriptNoisePolynomial lam d := by
    unfold manuscriptNoisePolynomial
    positivity
  have hpoly : manuscriptNoisePolynomial lam d ≤ manuscriptNoisePolynomial d d := by
    unfold manuscriptNoisePolynomial
    change lam ≤ d at hlam
    ring_nf
    nlinarith only [hlam]
  have hleakbound : manuscriptLeakageCoefficient * lam * manuscriptNoisePolynomial lam d ≤ γ := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hlam hL) hpoly hpoly0 (mul_nonneg hL hd.le)
    exact hh.trans hleak
  by_cases hkin : 0 ≤ k ∧ k ≤ (n : ℤ)
  · have hb := manuscript_twoCluster_far_comparison B P Q p d hpdata.1
      (hdpar.trans hp.1) (hdpar.trans hpdata.2.1) hP hQ hsmall n hn1 k u hu
    have hbranches := hNb n hnNb p hp k
    have henvelope := htail p hp (binomialZ p n k) hz
    have hbu : binomialUpperBranch p n k ≤
        binomialUpperEnvelope p (binomialZ p n k) + γ / 2 := by
      linarith only [(abs_lt.mp hbranches.1).2]
    have hbl : binomialLowerBranch p n k ≤
        binomialLowerEnvelope p (binomialZ p n k) + γ / 2 := by
      linarith only [(abs_lt.mp hbranches.2).2]
    have hmax : max (binomialUpperBranch p n k) (binomialLowerBranch p n k) ≤ γ + γ / 2 := by
      apply max_le
      · have hh := (le_max_left _ _).trans henvelope
        linarith only [hbu, hh]
      · have hh := (le_max_right _ _).trans henvelope
        linarith only [hbl, hh]
    have hnorm := manuscript_normalization_error_uniform P Q p hp n hn1
    have hnormd : manuscriptNormalizationBudget * lam / r ≤ manuscriptNormalizationBudget * d / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlam hC) hr.le
    have hshift := hcoeff.2.2.2
    have hshiftd := mul_le_mul_of_nonneg_left hsdiv
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 125) phi0_pos.le)
    have hleakactual := (manuscript_scaled_leakage_uniform B P Q p d hp hd.le hdpar
      hP hQ hsmall n hn1 k).trans hleakbound
    have hsize := (hNr n hnNr).le
    change (manuscriptNormalizationBudget + 125 * phi0) * d / r ≤ γ / 2 at hsize
    have he : manuscriptNormalizationBudget * d / r + 125 * phi0 * (d / r) =
        (manuscriptNormalizationBudget + 125 * phi0) * d / r := by ring
    have herr : manuscriptNormalizationBudget * lam / r + 125 * phi0 * s ≤ γ / 2 := by
      have hh := add_le_add hnormd hshiftd
      rw [he] at hh
      exact hh.trans hsize
    change (56 * cE + 48 * phi0) / (p * (1 - p)) * r * s ≤
      manuscriptNormalizationBudget * lam / r at hnorm
    change phi0 * clusterVariance P Q p / (2 * clusterThirdAbsoluteMoment P Q p) ≤
      phi0 + 125 * phi0 * s at hshift
    nlinarith only [hb, hmax, hnorm, hshift, hleakactual, herr, hgap, hγ]
  · have hkout : k < 0 ∨ (n : ℤ) < k := by omega
    have hb := manuscript_twoCluster_outside_uniform_error B P Q p d hpdata.1 hpcentral hd.le
      hP hQ hcoeff.1 n hn25 k hkout u hu
    have hcoef : 320 * cE ≤ manuscriptLeakageCoefficient := by
      unfold manuscriptLeakageCoefficient
      nlinarith only [cE_pos]
    have hsmallleak : 320 * cE * (3 * (lam / (2 / 5)) ^ 2 + d ^ 2 * (lam / (2 / 5))) ≤ γ := by
      have he : 3 * (lam / (2 / 5 : ℝ)) ^ 2 + d ^ 2 * (lam / (2 / 5)) =
          lam * manuscriptNoisePolynomial lam d := by unfold manuscriptNoisePolynomial; ring
      rw [he]
      have hh := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hlam0 hpoly0)
      have he' : manuscriptLeakageCoefficient * (lam * manuscriptNoisePolynomial lam d) =
          manuscriptLeakageCoefficient * lam * manuscriptNoisePolynomial lam d := by ring
      rw [he'] at hh
      exact hh.trans hleakbound
    have hgauss := (hNo n hnNo).le
    nlinarith only [hb, hsmallleak, hgauss, hgap, hγ, phi0_pos]

end BerryEsseen
