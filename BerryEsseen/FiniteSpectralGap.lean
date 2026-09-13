import BerryEsseen.PhaseBezout
import BerryEsseen.AtomicSpectralGap
import BerryEsseen.FiniteLatticeLabels
import BerryEsseen.ManuscriptGlobalPhase

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

theorem finite_lattice_nonresonance_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (τ h u : ℝ) (hτ : 0 < τ)
    (hcard : F.card < 2000) (hs : μ.support ⊆ (F : Set ℝ))
    (hb : ∀ x ∈ F, |x| < 13) (hatom : ∀ x ∈ F, τ ≤ μ.real {x})
    (hlo : Real.pi / 500 ≤ h) (hlat : IsLatticeSpan μ h)
    (hmax : ∀ t : ℝ, IsLatticeSpan μ t → t ≤ h)
    (hdist : 1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h))) :
    ‖charFun μ u‖ ≤ 1 - τ / (10 : ℝ) ^ 30 := by
  classical
  have hs' := finite_positive_atoms_support μ F τ hτ hs hatom
  obtain ⟨z, d, hz, hdz, hd⟩ := finite_lattice_natural_labels μ F h hs' hb hlo hlat
  let D := F.image d
  have hDgcd : D.gcd id = 1 := maximal_lattice_label_gcd_one μ F z h d hlat.1 hs
    (fun x hx => (hd x hx).1) hmax
  have hDM : ∀ k ∈ D, k ≤ 5000 := by
    rintro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact (hd x hx).2
  have hDcard : D.card < 2000 := Finset.card_image_le.trans_lt hcard
  have hDnz : D.gcd id ≠ 0 := by rw [hDgcd]; norm_num
  obtain ⟨m, hm, hm0⟩ := Finset.gcd_ne_zero_iff.mp hDnz
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  obtain ⟨b, t, heq, hbb, hsum⟩ := finite_bounded_bezout D 5000 m hDM hm hmpos hDgcd
  norm_num at hsum
  have hL : (∑ k ∈ D, |(b k : ℝ)|) + |(t : ℝ)| ≤ 30000000 := by
    have hc : (D.card : ℤ) ≤ 2000 := by exact_mod_cast hDcard.le
    have hbnd : (∑ k ∈ D, |b k|) + |t| ≤ 30000000 := by nlinarith only [hsum, hc]
    exact_mod_cast hbnd
  let Δ := 1 - ‖charFun μ u‖
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (norm_charFun_le_one u)
  let C := Real.sqrt (8 * Δ / τ)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCeq : C ^ 2 * τ = 8 * Δ := by
    have h := Real.sq_sqrt (show 0 ≤ 8 * Δ / τ by positivity)
    change C ^ 2 = 8 * Δ / τ at h
    exact (eq_div_iff hτ.ne').mp h
  have hchord : ∀ k ∈ D, ‖realPhase ((k : ℝ) * (h * u)) 1 - 1‖ ≤ C := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := Finset.mem_image.mp hk
    have hpair := two_atoms_characteristic_gap μ τ x z u hτ.le (hatom x hx) (hatom z hz)
    have he : ‖realPhase ((k : ℝ) * (h * u)) 1 - 1‖ = ‖realPhase u x - realPhase u z‖ := by
      have hdiff := realPhase_difference_chord u x (u * z)
      have harg : u * x - u * z = (k : ℝ) * (h * u) := by rw [(hd x hx).1, hxk]; ring
      rw [harg] at hdiff
      simpa only [realPhase, one_mul, mul_one] using hdiff
    rw [he]
    have hsq : ‖realPhase u x - realPhase u z‖ ^ 2 ≤ C ^ 2 := by
      apply le_of_mul_le_mul_right (a := τ) _ hτ
      rw [hCeq]
      change τ * ‖realPhase u x - realPhase u z‖ ^ 2 ≤ 8 * Δ at hpair
      nlinarith only [hpair]
    nlinarith only [hsq, hC, norm_nonneg (realPhase u x - realPhase u z)]
  have hphase := finite_bezout_phase_chord D b t m heq (h * u) C 30000000 hC hchord (hchord m hm) hL
  have hdistance : Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) ≤
      (Real.pi / (2 * h)) * ‖realPhase (h * u) 1 - 1‖ := by
    have h := affineLattice_distance_phase_bound h u 0 hlat.1
    simpa only [zero_div, realPhase, one_mul, mul_one, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero] using h
  have hcoef : Real.pi / (2 * h) ≤ 250 := by
    apply (div_le_iff₀ (by linarith [hlat.1] : 0 < 2 * h)).mpr
    linarith only [hlo]
  have hbound := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (realPhase (h * u) 1 - 1))
  have hClo : 1 / (10 : ℝ) ^ 13 ≤ C := by nlinarith only [hdist, hdistance, hbound, hphase]
  have hCsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 13) hClo 2
  have hmul := mul_le_mul_of_nonneg_right hCsq hτ.le
  change ‖charFun μ u‖ ≤ _
  dsimp [Δ] at hCeq
  nlinarith only [hmul, hCeq, hτ]

theorem finite_lattice_appendix_nonresonance_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (h u : ℝ)
    (hcard : F.card < 2000) (hs : μ.support ⊆ (F : Set ℝ))
    (hb : ∀ x ∈ F, |x| < 13) (hatom : ∀ x ∈ F, appendixRetention ≤ μ.real {x})
    (hlo : Real.pi / 500 ≤ h) (hlat : IsLatticeSpan μ h)
    (hmax : ∀ t : ℝ, IsLatticeSpan μ t → t ≤ h)
    (hdist : 1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h))) :
    ‖charFun μ u‖ ≤ 1 - 50 * appendixGlobalGap := by
  have hτ := appendix_retention_bounds.1
  have hg := finite_lattice_nonresonance_gap μ F appendixRetention h u hτ hcard hs hb hatom hlo hlat hmax hdist
  have htiny := mul_le_mul_of_nonneg_right appendix_retention_tiny hτ.le
  unfold appendixGlobalGap
  norm_num
  nlinarith only [hg, htiny, hτ]

/-- Original all-frequency spectral gap, retaining the rounding index range,
the Cayley-path coefficient budget, and both ordered pairs of atoms. -/
theorem manuscript_finite_lattice_spectral_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (a h₀ h τ u : ℝ) (hτ : 0 < τ)
    (hs : μ.support ⊆ (F : Set ℝ)) (hF : F ⊆ latticeRoundingPoints a h₀)
    (hatom : ∀ x ∈ F, τ ≤ μ.real {x}) (hlo : Real.pi / 500 ≤ h₀)
    (hh : h₀ ≤ h) (hlat : IsLatticeSpan μ h)
    (hmax : ∀ t : ℝ, IsLatticeSpan μ t → t ≤ h) :
    (1 / (10 : ℝ) ^ 12) * τ ^ 2 * Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) ^ 2 ≤
      1 - ‖charFun μ u‖ ^ 2 := by
  classical
  have hs' := finite_positive_atoms_support μ F τ hτ hs hatom
  obtain ⟨z, d, hz, hdz, hd⟩ := manuscript_finite_lattice_natural_labels μ F a h₀ h hs' hF hlo hh hlat
  let D := F.image d
  have hgcd : D.gcd id = 1 := maximal_lattice_label_gcd_one μ F z h d hlat.1 hs
    (fun x hx => (hd x hx).1) hmax
  have hDM : ∀ k ∈ D, k ≤ 2000 := by
    rintro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact (hd x hx).2.le
  obtain ⟨c, heq, hL⟩ := manuscript_finite_bezout_four_thousand D hDM hgcd
  let Δ := 1 - ‖charFun μ u‖ ^ 2
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    have hh := pow_le_pow_left₀ (norm_nonneg (charFun μ u)) (norm_charFun_le_one (μ := μ) u) 2
    norm_num only [one_pow] at hh
    linarith
  let C := Real.sqrt (Δ / τ ^ 2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCeq : C ^ 2 * τ ^ 2 = Δ := by
    have he : C ^ 2 = Δ / τ ^ 2 := Real.sq_sqrt (by positivity)
    exact (eq_div_iff (pow_pos hτ 2).ne').mp he
  have hres (k : ℕ) (hk : k ∈ D) :
      |circularResidual ((k : ℝ) * (h * u))| ≤ (Real.pi / 2) * C := by
    obtain ⟨x, hx, hxk⟩ := Finset.mem_image.mp hk
    have hp := manuscript_finite_two_atoms_square_gap μ F τ x z u hτ.le hs hx hz hatom
    have he : ‖realPhase 1 ((k : ℝ) * (h * u)) - 1‖ = ‖realPhase u x - realPhase u z‖ := by
      have hdiff := realPhase_difference_chord u x (u * z)
      have harg : u * x - u * z = (k : ℝ) * (h * u) := by rw [(hd x hx).1, hxk]; ring
      rw [harg] at hdiff
      simpa only [realPhase, one_mul] using hdiff
    have hnorm : ‖realPhase 1 ((k : ℝ) * (h * u)) - 1‖ ≤ C := by
      rw [he]
      have hsq : ‖realPhase u x - realPhase u z‖ ^ 2 ≤ C ^ 2 := by
        apply le_of_mul_le_mul_right (a := τ ^ 2) _ (pow_pos hτ 2)
        dsimp [Δ] at hCeq
        nlinarith only [hp, hCeq]
      nlinarith only [hsq, hC, norm_nonneg (realPhase u x - realPhase u z)]
    exact (circularResidual_chord_bound _).trans
      (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hphase := manuscript_bezout_circular_bound D c heq hL (h * u) ((Real.pi / 2) * C)
    (by positivity) hres
  have hdistance := manuscript_resonance_distance_residual h u hlat.1
  have hdiv := div_le_div_of_nonneg_right hphase hlat.1.le
  have hediv : 4000 * (Real.pi / 2 * C) / h =
      (4000 * (Real.pi / (2 * h))) * C := by field_simp
  rw [hediv] at hdiv
  have hcoef : Real.pi / (2 * h) ≤ 250 := by
    apply (div_le_iff₀ (by linarith [hlat.1] : 0 < 2 * h)).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 4000 * C by positivity)
  have hdistC : Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) ≤ 1000000 * C := by
    nlinarith only [hdistance, hdiv, hmul]
  have hsq := mul_self_le_mul_self Metric.infDist_nonneg hdistC
  have hsq' : Metric.infDist u (affineLattice 0 (2 * Real.pi / h)) ^ 2 ≤
      (10 : ℝ) ^ 12 * C ^ 2 := by nlinarith only [hsq]
  have hfinal := mul_le_mul_of_nonneg_right hsq' (sq_nonneg τ)
  dsimp [Δ] at hCeq
  nlinarith only [hfinal, hCeq]

theorem manuscript_finite_lattice_appendix_nonresonance_gap (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset ℝ) (a h₀ h u : ℝ)
    (hs : μ.support ⊆ (F : Set ℝ)) (hF : F ⊆ latticeRoundingPoints a h₀)
    (hatom : ∀ x ∈ F, appendixRetention ≤ μ.real {x}) (hlo : Real.pi / 500 ≤ h₀)
    (hh : h₀ ≤ h) (hlat : IsLatticeSpan μ h)
    (hmax : ∀ t : ℝ, IsLatticeSpan μ t → t ≤ h)
    (hdist : 1 / 1000 ≤ Metric.infDist u (affineLattice 0 (2 * Real.pi / h))) :
    ‖charFun μ u‖ ≤ 1 - 50 * appendixGlobalGap := by
  have hg := manuscript_finite_lattice_spectral_gap μ F a h₀ h appendixRetention u
    appendix_retention_bounds.1 hs hF hatom hlo hh hlat hmax
  have hd2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 1000) hdist 2
  have hm := mul_le_mul_of_nonneg_left hd2 (show 0 ≤ (1 / (10 : ℝ) ^ 12) * appendixRetention ^ 2 by positivity)
  have hn := norm_charFun_le_one (μ := μ) u
  have hn0 := norm_nonneg (charFun μ u)
  have hsq : 1 - ‖charFun μ u‖ ^ 2 ≤ 2 * (1 - ‖charFun μ u‖) := by nlinarith [sq_nonneg (1 - ‖charFun μ u‖)]
  unfold appendixGlobalGap
  norm_num at hg hm ⊢
  nlinarith only [hg, hm, hsq]

end BerryEsseen
