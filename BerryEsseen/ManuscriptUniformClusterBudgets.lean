import BerryEsseen.ManuscriptCentralClusterBudget
import BerryEsseen.ManuscriptFarComparison
import BerryEsseen.GeneralBinomialConsequences

/-! Uniform numerical majorants on the initially fixed compact interval.
Every positive error below retains its factor of accumulated noise variance.
These are the budgets used for the manuscript's successive parameter choices. -/
noncomputable section
open MeasureTheory Set
namespace BerryEsseen

def manuscriptInitialInterval : Set ℝ := Icc (2 / 5) (9 / 20)
def manuscriptNormalizationBudget : ℝ := (56 * cE + 48 * phi0) / (2 / 5) ^ 2
def manuscriptLeakageCoefficient : ℝ := 128 * cE * 32 / (2 / 5)
def manuscriptCentralErrorMajorant : ℝ := 176000 * 32 * (5 * cE) + manuscriptLeakageCoefficient
def manuscriptNoisePolynomial (lam ε : ℝ) : ℝ := 3 * lam / (2 / 5) ^ 2 + ε ^ 2 / (2 / 5)

theorem manuscript_initial_parameter_bounds (p : ℝ) (hp : p ∈ manuscriptInitialInterval) :
    p ∈ Ioo (0 : ℝ) 1 ∧ (2 / 5 : ℝ) ≤ 1 - p ∧
      (2 / 5 : ℝ) ^ 2 ≤ p * (1 - p) := by
  have hlo := hp.1
  have hhi := hp.2
  refine ⟨⟨by linarith, by linarith⟩, by linarith, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr (show (2 / 5 : ℝ) ≤ 1 - p by linarith))]

theorem manuscript_cluster_uniform_coefficients (P Q : CenteredFourthLaw) (p ε : ℝ)
    (hp : p ∈ manuscriptInitialInterval) (hε : ε ≤ 2 / 5)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16) :
    clusterVariance P Q p ≤ 1 ∧
      (1 / 100 : ℝ) ≤ Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p ∧
      Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p ≤ 32 ∧
      phi0 * clusterVariance P Q p / (2 * clusterThirdAbsoluteMoment P Q p) ≤
        phi0 + 125 * phi0 * averageNoiseVariance P Q p := by
  let v := p * (1 - p)
  let s := averageNoiseVariance P Q p
  let τ := p ^ 2 + (1 - p) ^ 2
  let ρ := clusterThirdAbsoluteMoment P Q p
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hb := bernoulli_variance_tau_bounds p hpdata.1
  have hv : 0 < v := hb.1.1
  have hvlo : (2 / 5 : ℝ) ^ 2 ≤ v := hpdata.2.2
  have hvhi : v ≤ 1 / 4 := by dsimp [v]; nlinarith [sq_nonneg (p - 1 / 2)]
  have hs0 : 0 ≤ s := averageNoiseVariance_nonneg P Q p ⟨hpdata.1.1.le, hpdata.1.2.le⟩
  have hρ : |ρ - v * τ| ≤ 4 * s := by
    have hh := twoCluster_abs_third_error P Q p ε ⟨hpdata.1.1.le, hpdata.1.2.le⟩
      (hε.trans hp.1) (hε.trans hpdata.2.1) hP hQ
    change |ρ - v * τ| ≤ (3 + ε) * s at hh
    nlinarith [mul_le_mul_of_nonneg_right hε hs0]
  have hρ0 : 0 < ρ := clusterThirdAbsoluteMoment_pos P Q p hpdata.1
  have hden := perturbation_denominator_bounds v s τ ρ hv hb.2 hs hρ
  have hpref := perturbed_prefactor_bound v s τ ρ hb.1 hb.2 ⟨hs0, hs⟩ hρ
  have he : clusterVariance P Q p = v + s := by unfold clusterVariance s v averageNoiseVariance; ring
  rw [he]
  have hroot : (2 / 5 : ℝ) ≤ Real.sqrt (v + s) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ v + s), Real.sqrt_nonneg (v + s)]
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 5) hroot 3
  have hρhi : ρ ≤ 2 := by
    have hτhi := mul_le_mul_of_nonneg_left hb.2.2 hv.le
    have hhi := (abs_le.mp hρ).2
    change s ≤ v / 16 at hs
    nlinarith
  refine ⟨by change s ≤ v / 16 at hs; linarith, ?_, hpref.2, ?_⟩
  · apply (le_div_iff₀ hρ0).mpr
    norm_num at hcube
    nlinarith
  · have hratio : (v + s) / (2 * ρ) ≤ 1 + 125 * s := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * ρ)).mpr
      have hτlo := mul_le_mul_of_nonneg_left hb.2.1 hv.le
      have hlow := (abs_le.mp hρ).1
      have hm : 10 * s ≤ 250 * ρ * s := by
        have hρlo : 10 ≤ 250 * ρ := by linarith [hden.1]
        exact mul_le_mul_of_nonneg_right hρlo hs0
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hratio phi0_pos.le
    convert hh using 1 <;> ring

theorem manuscript_scaled_binomial_mass_bound (B : PublishedBernoulliBound)
    (p : ℝ) (hp : p ∈ manuscriptInitialInterval) (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    Real.sqrt (n : ℝ) * binomialWeight p n k ≤ 5 * cE := by
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hb := binomialWeight_uniform_bound B p (2 / 5) (by norm_num) hp.1
    (manuscript_initial_parameter_bounds p hp).2.1 n k hn hk
  have hh := mul_le_mul_of_nonneg_left hb hr.le
  convert hh using 1
  field_simp [hr.ne']
  <;> ring

theorem manuscript_normalization_error_uniform (P Q : CenteredFourthLaw) (p : ℝ)
    (hp : p ∈ manuscriptInitialInterval) (n : ℕ) (hn : 1 ≤ n) :
    (56 * cE + 48 * phi0) / (p * (1 - p)) * Real.sqrt (n : ℝ) * averageNoiseVariance P Q p ≤
      manuscriptNormalizationBudget * accumulatedNoiseVariance P Q p n / Real.sqrt (n : ℝ) := by
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hs0 := averageNoiseVariance_nonneg P Q p ⟨hpdata.1.1.le, hpdata.1.2.le⟩
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hc := div_le_div_of_nonneg_left (by have := cE_pos; have := phi0_pos; positivity : 0 ≤ 56 * cE + 48 * phi0)
    (by norm_num : (0 : ℝ) < (2 / 5) ^ 2) hpdata.2.2
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hr.le) hs0
  apply hh.trans_eq
  unfold manuscriptNormalizationBudget accumulatedNoiseVariance
  field_simp [hr.ne']
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  rfl

theorem manuscript_central_coefficients_uniform (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε c : ℝ) (hp : p ∈ manuscriptInitialInterval)
    (hε : ε ≤ 2 / 5) (hc : 0 ≤ c)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hmass : c ≤ Real.sqrt (n : ℝ) * binomialWeight p n k) :
    (3 / 1600 : ℝ) * c ≤ manuscriptClusterCentralLossCoefficient P Q p n k ∧
    manuscriptClusterCentralErrorCoefficient P Q p (2 / 5) ε n k ≤
      manuscriptNormalizationBudget / Real.sqrt (n : ℝ) +
        manuscriptCentralErrorMajorant * manuscriptNoisePolynomial (accumulatedNoiseVariance P Q p n) ε := by
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hcoeff := manuscript_cluster_uniform_coefficients P Q p ε hp hε hP hQ hs
  have hmassHi := manuscript_scaled_binomial_mass_bound B p hp n k hn hk
  have hA0 := (by norm_num : (0 : ℝ) ≤ 1 / 100).trans hcoeff.2.1
  have hr0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hlam0 := accumulatedNoiseVariance_nonneg P Q p ⟨hpdata.1.1.le, hpdata.1.2.le⟩ n
  constructor
  · have hh := mul_le_mul hcoeff.2.1 hmass hc hA0
    have hhh := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 3 / 16)
    convert hhh using 1 <;> dsimp only [manuscriptClusterCentralLossCoefficient] <;> ring
  · have h1 : (56 * cE + 48 * phi0) / (p * (1 - p) * Real.sqrt (n : ℝ)) ≤
        manuscriptNormalizationBudget / Real.sqrt (n : ℝ) := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (by have := cE_pos; have := phi0_pos; positivity)
          (by norm_num : (0 : ℝ) < (2 / 5) ^ 2) hpdata.2.2) hr0
    have h2 := mul_le_mul hcoeff.2.2.1 hmassHi (hc.trans hmass) (by norm_num : (0 : ℝ) ≤ 32)
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 176000)
    have h4 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoeff.2.2.1 (by have := cE_pos; positivity : 0 ≤ 128 * cE))
      (by norm_num : (0 : ℝ) ≤ 2 / 5)
    have h5 : 176000 * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
        (Real.sqrt (n : ℝ) * binomialWeight p n k) +
        128 * cE * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) / (2 / 5) ≤
        manuscriptCentralErrorMajorant := by
      unfold manuscriptCentralErrorMajorant manuscriptLeakageCoefficient
      nlinarith only [h3, h4]
    have h6 := mul_le_mul_of_nonneg_right h5 (by unfold manuscriptNoisePolynomial; positivity :
      0 ≤ manuscriptNoisePolynomial (accumulatedNoiseVariance P Q p n) ε)
    exact add_le_add h1 h6

theorem manuscript_scaled_leakage_uniform (B : PublishedBernoulliBound)
    (P Q : CenteredFourthLaw) (p ε : ℝ) (hp : p ∈ manuscriptInitialInterval)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 2 / 5)
    (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (hs : averageNoiseVariance P Q p ≤ p * (1 - p) / 16)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) *
      blockLeakageBudget P Q p n k ≤
      manuscriptLeakageCoefficient * accumulatedNoiseVariance P Q p n *
        manuscriptNoisePolynomial (accumulatedNoiseVariance P Q p n) ε := by
  have hpdata := manuscript_initial_parameter_bounds p hp
  have hcoeff := manuscript_cluster_uniform_coefficients P Q p ε hp hε hP hQ hs
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hlam0 := accumulatedNoiseVariance_nonneg P Q p ⟨hpdata.1.1.le, hpdata.1.2.le⟩ n
  have hb := actual_twoCluster_leakage_bound B P Q p (2 / 5) ε (by norm_num) hp.1
    hpdata.2.1 hε0 hP hQ n hn k
  have hfac0 : 0 ≤ Real.sqrt (n : ℝ) * (Real.sqrt (clusterVariance P Q p) ^ 3 / clusterThirdAbsoluteMoment P Q p) := by
    exact mul_nonneg hr.le ((by norm_num : (0 : ℝ) ≤ 1 / 100).trans hcoeff.2.1)
  have h1 := mul_le_mul_of_nonneg_left hb hfac0
  have h2 := mul_le_mul_of_nonneg_right hcoeff.2.2.1 (by
    have := cE_pos
    unfold manuscriptNoisePolynomial
    positivity : 0 ≤ (128 * cE / (2 / 5)) * (accumulatedNoiseVariance P Q p n *
      manuscriptNoisePolynomial (accumulatedNoiseVariance P Q p n) ε))
  apply h1.trans
  convert h2 using 1 <;> dsimp only [manuscriptLeakageCoefficient, manuscriptNoisePolynomial]
  · field_simp [hr.ne']
    <;> ring
  · ring

end BerryEsseen
