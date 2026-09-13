import BerryEsseen.ManuscriptSupportAnchors
import BerryEsseen.ManuscriptConfinementMass
import BerryEsseen.ManuscriptSmoothingInstance
import BerryEsseen.ManuscriptContactFlatness
import BerryEsseen.ManuscriptContactIncrement
import BerryEsseen.EffectiveConfinement

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem manuscript_confinement_separation_budget (n : ℕ) (hn : appendixNConf ≤ n) :
    3 * Real.exp (-5 * appendixA) < (3 / 5 : ℝ) * appendixZeta - 30 / Real.sqrt (n : ℝ) := by
  have hceil := (Nat.le_ceil (Real.exp (1000 * appendixA))).trans
    (show (appendixNConf : ℝ) ≤ n by exact_mod_cast hn)
  have hr : Real.exp (500 * appendixA) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (Real.exp_pos _).le (Nat.cast_nonneg n)).mpr
    rw [← Real.exp_nat_mul]
    convert hceil using 1 <;> ring
  have hi : 1 / Real.sqrt (n : ℝ) ≤ Real.exp (-500 * appendixA) := by
    rw [show -500 * appendixA = -(500 * appendixA) by ring, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) hr
  have h1 := exponential_relative_sixteenth 3 (5 * appendixA) (2 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  have h2 := exponential_relative_sixteenth 30 (500 * appendixA) (2 * appendixA)
    (by norm_num [appendixA]) (by norm_num [appendixA])
  rw [show -(5 * appendixA) = -5 * appendixA by ring, show -(2 * appendixA) = -2 * appendixA by ring] at h1
  rw [show -(500 * appendixA) = -500 * appendixA by ring, show -(2 * appendixA) = -2 * appendixA by ring] at h2
  dsimp [appendixZeta, appendixEtaStar]
  simp only [div_eq_mul_inv] at hi ⊢
  nlinarith only [hi, h1, h2, Real.exp_pos (-2 * appendixA)]

theorem manuscript_effective_confinement_coordinates (H : ClassicalBerryEsseenBounds)
    (S : PublishedSignedSmoothing) (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality) (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (hN : appendixNConf ≤ n + 1) (t : ℝ)
    (hattain : signedRatio P n t = extremalConstant (n + 1))
    (hv : cE < extremalConstant (n + 1))
    (hsupp : P.measure.support ⊆ Icc (-6) 6)
    (hd : scaledDrop extremalConstant (n + 1) ≤ 20 / Real.sqrt (n + 1 : ℝ)) :
    ∀ y ∈ P.measure.support, esseenAffine y ∈
      Icc (-appendixZeta) appendixZeta ∪ Icc (1 - appendixZeta) (1 + appendixZeta) := by
  have hn : 1 ≤ n := by have h := appendixNConf_ge_two.trans hN; omega
  have hhalf : ((n + 1 : ℕ) : ℝ) / 2 ≤ (n : ℝ) := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [h]
  have hnb := appendix_global_sample_bounds (n + 1) n hN hhalf
  have hpos := positive_extremizer_normalized_violation P n t (by rw [hattain]; exact hv)
  obtain ⟨h, hh, hW, hspan, hβ, hκ, hM, hz, hJ⟩ :=
    effective_identification H S E K U P (n + 1) hN hsupp (t / Real.sqrt (n + 1 : ℝ)) hpos
  have hh0 : 0 < h := (div_pos Real.pi_pos (by norm_num)).trans_le hh.1
  have hys (y : ℝ) (hy : y ∈ P.measure.support) : |y| ≤ 6 := abs_le.mpr (hsupp hy)
  have hcoarse (y : ℝ) (hy : y ∈ P.measure.support) :
      esseenAffine y ∈ Icc (-1 / 2) (3 / 2) := by
    have hc := manuscript_extremizer_effective_contact_polynomial H P n hn t hattain hv hd
      (Real.exp (-6 * appendixA)) (Real.exp_pos _).le hβ hM y hy (hys y hy)
    have hb := manuscript_appendix_contact_polynomial_budget (n + 1) hN (t / Real.sqrt (n + 1 : ℝ)) hz
    simp only [Nat.cast_add, Nat.cast_one] at hb
    exact effective_coarse_support_of_contact y (by linarith only [hc, hb])
  obtain ⟨a, ha, b, hb, ha0, hb1⟩ := manuscript_effective_support_anchors K P hW
  have hzsmall : (t / Real.sqrt (n + 1 : ℝ)) ^ 2 ≤ 0.01 := by
    have he : Real.exp (-5 * appendixA) ≤ Real.exp (-appendixA) := Real.exp_le_exp.mpr (by norm_num [appendixA])
    linarith only [hz, he, appendix_noise_and_cutoff_bounds.1]
  have hflat (y : ℝ) (hy : y ∈ P.measure.support) :=
    (manuscript_extremizer_contact_flatness H P n hn hN t hattain hv hz h hh0 hspan hβ hκ
      (hJ n hhalf) y hy (hys y hy)).2.1.trans
      (manuscript_extremizer_contact_flatness H P n hn hN t hattain hv hz h hh0 hspan hβ hκ
        (hJ n hhalf) y hy (hys y hy)).2.2
  have hsep := manuscript_confinement_separation_budget (n + 1) hN
  simp only [Nat.cast_add, Nat.cast_one] at hsep
  have hconf : esseenAffine '' P.measure.support ⊆
      Icc (-appendixZeta) appendixZeta ∪ Icc (1 - appendixZeta) (1 + appendixZeta) := by
    apply two_cluster_confinement_of_no_intermediate_pair (esseenAffine '' P.measure.support)
      appendixZeta (esseenAffine a) (esseenAffine b)
      ⟨appendixZeta_bounds.1, by linarith [appendixZeta_bounds.2]⟩
      (by rintro x ⟨y, hy, rfl⟩; simpa only [neg_div] using hcoarse y hy)
      (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) ha0 hb1
    rintro x ⟨x₀, hx, rfl⟩ y ⟨y₀, hy, rfl⟩ hxy hlow hhigh
    have hxy0 : x₀ < y₀ := by
      change pE + sigmaE * x₀ < pE + sigmaE * y₀ at hxy
      nlinarith only [hxy, sigmaE_pos]
    have hdscale : y₀ - x₀ = (esseenAffine y₀ - esseenAffine x₀) * hE := by
      unfold esseenAffine hE
      field_simp [sigmaE_pos.ne']
      <;> ring
    have hdlow : 9 * appendixZeta / 10 * hE ≤ y₀ - x₀ := by
      rw [hdscale]
      exact mul_le_mul_of_nonneg_right hlow hE_pos.le
    have hdup : y₀ - x₀ ≤ 3 * hE / 5 := by
      rw [hdscale]
      have hm := mul_le_mul_of_nonneg_right hhigh hE_pos.le
      nlinarith only [hm]
    have hdh : y₀ - x₀ < hE := by nlinarith only [hdup, hE_pos]
    have hup := manuscript_effective_increment_upper (iidSumLaw P.measure n)
      (Real.sqrt (n : ℝ)) (t - y₀) (y₀ - x₀) (Real.exp (-5 * appendixA))
      (Real.sqrt_nonneg _) (Real.exp_pos _).le (sub_nonneg.mpr hxy0.le) hdh (hflat y₀ hy)
    have hratio : hE / (hE - (y₀ - x₀)) ≤ 3 :=
      (div_le_iff₀ (sub_pos.mpr hdh)).mpr (by nlinarith only [hdup, hE_pos])
    have hup' := hup.trans (mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le)
    rw [show t - y₀ + (y₀ - x₀) = t - x₀ by ring] at hup'
    have hlow' := manuscript_extremizer_effective_increment_lower H P n hnb.1 t hattain hv hzsmall
      x₀ y₀ hx hy (hys x₀ hx) (hys y₀ hy) hxy0.le
    have hdζ : (3 / 5 : ℝ) * appendixZeta ≤ (y₀ - x₀) / 3 := by
      have hE2 := two_le_hE
      have hm := mul_le_mul_of_nonneg_left hE2 (show 0 ≤ 9 * appendixZeta / 10 by positivity [appendixZeta_bounds.1])
      nlinarith only [hdlow, hm]
    linarith only [hup', hlow', hdζ, hsep]
  intro y hy
  exact hconf (mem_image_of_mem _ hy)


theorem manuscript_effective_confinement (H : ClassicalBerryEsseenBounds)
    (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality) (U : PublishedNonuniformBound) :
    EffectiveConfinementInput := by
  intro P n t hN hatt hv hsupp hd
  have hn1 : 1 ≤ n := by have h := appendixNConf_ge_two.trans hN; omega
  have he : n - 1 + 1 = n := by omega
  have hncast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast he
  have hcoords := manuscript_effective_confinement_coordinates H manuscriptSignedSmoothing E K U
    P (n - 1) (by rwa [he]) t (by rwa [he]) (by rwa [he]) hsupp
    (by simpa only [he, hncast] using hd)
  change ∀ y ∈ P.measure.support, pE + sigmaE * y ∈
    Icc (-(appendixEtaStar / 2)) (appendixEtaStar / 2) ∪
      Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2) at hcoords
  have hpos := positive_extremizer_normalized_violation P (n - 1) t (by rw [hatt]; exact hv)
  have hpos' : cE * thirdMoment P < Real.sqrt (n : ℝ) *
      (normalizedSumCDF P n (t / Real.sqrt (n : ℝ)) - normalCDF (t / Real.sqrt (n : ℝ))) := by
    simpa only [he, hncast] using hpos
  obtain ⟨h, hh, hW, hspan, hβ, hκ, hM, hz, hJ⟩ :=
    effective_identification H manuscriptSignedSmoothing E K U P n hN hsupp (t / Real.sqrt (n : ℝ)) hpos'
  refine ⟨?_, manuscript_confinement_half_eta_mass K P hW hcoords⟩
  have hs := confinement_affine_intervals_support P pE sigmaE (appendixEtaStar / 2) hcoords
  simpa only [neg_div] using hs

theorem manuscript_effective_full_support (H : ClassicalBerryEsseenBounds)
    (E : PublishedEsseenMoment) (K : PublishedWassersteinDuality) (U : PublishedNonuniformBound)
    (P : StandardizedLaw) (n : ℕ) (t : ℝ) (hN : appendixNConf ≤ n)
    (hatt : signedRatio P (n - 1) t = extremalConstant n) (hv : cE < extremalConstant n)
    (hsupp : P.measure.support ⊆ Icc (-6) 6)
    (hd : scaledDrop extremalConstant n ≤ 20 / Real.sqrt (n : ℝ)) :
    let μ := P.measure.map (fun x => pE + sigmaE * x)
    μ.support ⊆ Icc (-appendixEtaStar / 2) (appendixEtaStar / 2) ∪
      Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2) ∧
    |μ.real (Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2)) - pE| < appendixEtaStar := by
  obtain ⟨hb, hp⟩ := manuscript_effective_confinement H E K U P n t hN hatt hv hsupp hd
  refine ⟨hb, ?_⟩
  let μ := P.measure.map (fun x => pE + sigmaE * x)
  have hae : ∀ᵐ x ∂μ, x ∈ Icc (-(appendixEtaStar / 2)) (appendixEtaStar / 2) ∪
      Icc (1 - appendixEtaStar / 2) (1 + appendixEtaStar / 2) := by
    filter_upwards [μ.support_mem_ae] with x hx
    simpa only [neg_div] using hb hx
  rw [← upper_interval_mass_eq μ (appendixEtaStar / 2) (by linarith [appendixEtaStar_bounds.1.2]) hae]
  exact hp

end BerryEsseen
