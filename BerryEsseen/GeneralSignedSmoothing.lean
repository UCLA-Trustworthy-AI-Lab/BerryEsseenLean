import BerryEsseen.PublishedSmoothing
import BerryEsseen.EdgeworthDensityFourier
import BerryEsseen.CharacteristicConditioning
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Full finite signed-measure smoothing from the internal density interface.

The bridge from a Lipschitz primitive to a bounded density is proved here:
interval FTC gives local density measures, increasing intervals give absolute
continuity on the line, and the existing mathlib signed Radon–Nikodym theorem
identifies the global density with the derivative of the primitive. Jordan
parts identify the actual signed Fourier transform. Finite first moments prove
integrability of the cutoff quotient, so no additional analytic premise is
required in the endpoint.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace BerryEsseen

/-- The value of an actual signed measure is the difference of its Jordan parts. -/
theorem signedMeasure_jordan_apply (s : SignedMeasure ℝ) (A : Set ℝ)
    (hA : MeasurableSet A) :
    s A = s.toJordanDecomposition.posPart.real A -
      s.toJordanDecomposition.negPart.real A := by
  conv_lhs => rw [← s.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hA,
    Measure.toSignedMeasure_apply_measurable hA]

/-- Half-line values determine finite signed measures on the real line. -/
theorem signedMeasure_ext_Iic (s t : SignedMeasure ℝ)
    (h : ∀ x, s (Iic x) = t (Iic x)) : s = t := by
  have he : s.toJordanDecomposition.posPart + t.toJordanDecomposition.negPart =
      t.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart := by
    apply Measure.ext_of_Iic
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    change (s.toJordanDecomposition.posPart + t.toJordanDecomposition.negPart).real (Iic x) =
      (t.toJordanDecomposition.posPart + s.toJordanDecomposition.negPart).real (Iic x)
    rw [measureReal_add_apply, measureReal_add_apply]
    have hx := h x
    rw [signedMeasure_jordan_apply _ _ measurableSet_Iic,
      signedMeasure_jordan_apply _ _ measurableSet_Iic] at hx
    linarith
  ext A hA
  have hA' := congrArg (fun μ : Measure ℝ => μ.real A) he
  dsimp only at hA'
  rw [measureReal_add_apply, measureReal_add_apply] at hA'
  rw [signedMeasure_jordan_apply _ _ hA, signedMeasure_jordan_apply _ _ hA]
  linarith

/-- The primitive of a signed measure recovers its bounded-interval values. -/
theorem signedMeasure_Ioc (s : SignedMeasure ℝ) (a b : ℝ) (hab : a ≤ b) :
    s (Ioc a b) = s (Iic b) - s (Iic a) := by
  rw [← Iic_diff_Iic]
  exact VectorMeasure.of_diff measurableSet_Iic measurableSet_Iic
    (Iic_subset_Iic.mpr hab)

/-- A Lipschitz primitive has the expected derivative integral on every interval. -/
theorem signedMeasure_lipschitz_interval_density (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x)))
    (a b : ℝ) (hab : a ≤ b) :
    ∫ x in Ioc a b, deriv (fun y => s (Iic y)) x = s (Ioc a b) := by
  rw [signedMeasure_Ioc s a b hab,
    ← (hM.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)).integral_deriv_eq_sub,
    intervalIntegral.integral_of_le hab]

/-- A Lipschitz signed primitive gives a density on every bounded interval. -/
theorem signedMeasure_lipschitz_restrict_density (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x))) (a b : ℝ) :
    s.restrict (Ioc a b) = (volume.restrict (Ioc a b)).withDensityᵥ
      (deriv (fun y => s (Iic y))) := by
  have hi : IntegrableOn (deriv (fun y => s (Iic y))) (Ioc a b) := by
    rcases le_total a b with hab | hba
    · exact (hM.lipschitzOnWith.absolutelyContinuousOnInterval
        (a := a) (b := b)).intervalIntegrable_deriv.1
    · rw [Ioc_eq_empty (not_lt.mpr hba)]
      exact integrableOn_empty
  apply signedMeasure_ext_Iic
  intro x
  rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic,
    withDensityᵥ_apply hi measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have he : Iic x ∩ Ioc a b = Ioc a (min x b) := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  rw [he]
  rcases le_total a (min x b) with hac | hca
  · exact (signedMeasure_lipschitz_interval_density s M hM a (min x b) hac).symm
  · rw [Ioc_eq_empty (not_lt.mpr hca)]
    simp

/-- The expanding bounded intervals used to recover a measure on the whole line. -/
theorem signedSmoothing_interval_cover :
    (⋃ n : ℕ, Ioc (-(n : ℝ)) (n : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact mem_iUnion.mpr ⟨n, by
    constructor <;> linarith [le_abs_self x, neg_abs_le x]⟩

/-- Absolute continuity of an actual signed measure follows from its Lipschitz primitive. -/
theorem signedMeasure_absolutelyContinuous_of_lipschitz (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x))) :
    s ≪ᵥ volume.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro A hA hz
  have hz' : volume A = 0 := by
    exact (by simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA] using hz)
  have hzero (n : ℕ) : s (A ∩ Ioc (-(n : ℝ)) (n : ℝ)) = 0 := by
    have he := signedMeasure_lipschitz_restrict_density s M hM (-(n : ℝ)) (n : ℝ)
    have hr := (volume.restrict (Ioc (-(n : ℝ)) (n : ℝ))).withDensityᵥ_absolutelyContinuous
      (deriv (fun y => s (Iic y)))
    rw [← he] at hr
    rw [← VectorMeasure.restrict_apply _ measurableSet_Ioc hA]
    apply hr
    rw [Measure.toENNRealVectorMeasure_apply_measurable hA, Measure.restrict_apply hA]
    exact measure_mono_null inter_subset_left hz'
  have hm : Monotone (fun n : ℕ => A ∩ Ioc (-(n : ℝ)) (n : ℝ)) := by
    intro i j hij x hx
    refine ⟨hx.1, ?_, ?_⟩ <;> push_cast at *
    · exact lt_of_le_of_lt (neg_le_neg (Nat.cast_le.mpr hij)) hx.2.1
    · exact hx.2.2.trans (Nat.cast_le.mpr hij)
  have ht := VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat
    (v := s) hm (fun n => hA.inter measurableSet_Ioc)
  have hu : (⋃ n : ℕ, A ∩ Ioc (-(n : ℝ)) (n : ℝ)) = A := by
    rw [← inter_iUnion, signedSmoothing_interval_cover, inter_univ]
  rw [hu] at ht
  have hc : Tendsto (fun n : ℕ => s (A ∩ Ioc (-(n : ℝ)) (n : ℝ))) atTop (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact (tendsto_nhds_unique ht hc)

/-- A locally represented derivative agrees almost everywhere with the global RN density. -/
theorem signedMeasure_rnDeriv_eq_primitive_deriv (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x))) :
    s.rnDeriv volume =ᵐ[volume] deriv (fun x => s (Iic x)) := by
  have hRN := s.withDensityᵥ_rnDeriv_eq volume
    (signedMeasure_absolutelyContinuous_of_lipschitz s M hM)
  have hlocal (n : ℕ) : s.rnDeriv volume =ᵐ[volume.restrict (Ioc (-(n : ℝ)) (n : ℝ))]
      deriv (fun x => s (Iic x)) := by
    have hf := (hM.lipschitzOnWith.absolutelyContinuousOnInterval
      (a := -(n : ℝ)) (b := (n : ℝ))).intervalIntegrable_deriv.1
    apply ((s.integrable_rnDeriv volume).integrableOn).ae_eq_of_withDensityᵥ_eq hf
    rw [← signedMeasure_lipschitz_restrict_density s M hM]
    ext A hA
    rw [withDensityᵥ_apply ((s.integrable_rnDeriv volume).integrableOn) hA,
      VectorMeasure.restrict_apply _ measurableSet_Ioc hA, Measure.restrict_restrict hA]
    have hv := congrArg (fun v : SignedMeasure ℝ => v (A ∩ Ioc (-(n : ℝ)) (n : ℝ))) hRN
    dsimp only at hv
    rw [withDensityᵥ_apply (s.integrable_rnDeriv volume) (hA.inter measurableSet_Ioc)] at hv
    exact hv
  have hc := (ae_eq_restrict_iUnion_iff
    (μ := volume) (fun n : ℕ => Ioc (-(n : ℝ)) (n : ℝ))
    (s.rnDeriv volume) (deriv (fun x => s (Iic x)))).mpr hlocal
  simpa only [signedSmoothing_interval_cover, Measure.restrict_univ] using hc

/-- The ordinary derivative itself is a globally integrable bounded density for the signed measure. -/
theorem signedMeasure_lipschitz_has_bounded_density (s : SignedMeasure ℝ)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x))) :
    ∃ g : ℝ → ℝ, Measurable g ∧ Integrable g ∧ (∀ x, |g x| ≤ M) ∧ volume.withDensityᵥ g = s := by
  let g := deriv (fun x => s (Iic x))
  have hae := signedMeasure_rnDeriv_eq_primitive_deriv s M hM
  have hg : Integrable g := (s.integrable_rnDeriv volume).congr hae
  refine ⟨g, measurable_deriv _, hg, ?_, ?_⟩
  · intro x
    simpa only [g, Real.norm_eq_abs] using (norm_deriv_le_of_lipschitz hM (x₀ := x))
  · rw [← s.withDensityᵥ_rnDeriv_eq volume
      (signedMeasure_absolutelyContinuous_of_lipschitz s M hM)]
    exact WithDensityᵥEq.congr_ae hae.symm

/-- The Fourier transform of a finite signed measure, using its actual Jordan decomposition. -/
def signedFourier (s : SignedMeasure ℝ) (t : ℝ) : ℂ :=
  charFun s.toJordanDecomposition.posPart t - charFun s.toJordanDecomposition.negPart t

/-- The Jordan parts of a density measure are its positive and negative density parts. -/
theorem signedMeasure_density_jordan (s : SignedMeasure ℝ) (g : ℝ → ℝ)
    (hgm : Measurable g) (hg : Integrable g) (he : volume.withDensityᵥ g = s) :
    s.toJordanDecomposition.posPart = volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
    s.toJordanDecomposition.negPart = volume.withDensity (fun x => ENNReal.ofReal (-g x)) := by
  have hj := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity hgm hg
    (VectorMeasure.MutuallySingular.zero_left (w := volume.toENNRealVectorMeasure))
    (show s = 0 + volume.withDensityᵥ g by simpa only [zero_add] using he.symm)
  constructor
  · simpa [SignedMeasure.toJordanDecomposition_zero] using congrArg JordanDecomposition.posPart hj
  · simpa [SignedMeasure.toJordanDecomposition_zero] using congrArg JordanDecomposition.negPart hj

/-- The actual total-variation first moment gives the weighted first moment of
any measurable density representing the signed measure. -/
theorem signedMeasure_density_first_integrable (s : SignedMeasure ℝ) (g : ℝ → ℝ)
    (hgm : Measurable g) (hg : Integrable g) (he : volume.withDensityᵥ g = s)
    (hs1 : Integrable (fun x : ℝ => |x|) s.totalVariation) :
    Integrable (fun x : ℝ => x * g x) := by
  obtain ⟨hp, hn⟩ := signedMeasure_density_jordan s g hgm hg he
  have hsp : Integrable (fun x : ℝ => x) s.toJordanDecomposition.posPart :=
    (integrable_norm_iff (by fun_prop)).mp (by
      simpa only [Real.norm_eq_abs] using hs1.left_of_add_measure)
  have hsn : Integrable (fun x : ℝ => x) s.toJordanDecomposition.negPart :=
    (integrable_norm_iff (by fun_prop)).mp (by
      simpa only [Real.norm_eq_abs] using hs1.right_of_add_measure)
  rw [hp] at hsp
  rw [hn] at hsn
  have hp' := (integrable_withDensity_iff hgm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hsp
  have hn' := (integrable_withDensity_iff hgm.neg.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hsn
  convert hp'.sub hn' using 1
  funext x
  simp only [ENNReal.toReal_ofReal', Pi.sub_apply]
  by_cases hx : 0 ≤ g x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
    ring

/-- Fourier transformation is unchanged when a signed measure is represented by a density. -/
theorem signedFourier_eq_densityFourier (s : SignedMeasure ℝ) (g : ℝ → ℝ)
    (hgm : Measurable g) (hg : Integrable g) (he : volume.withDensityᵥ g = s) (t : ℝ) :
    signedFourier s t = densityFourier g t := by
  obtain ⟨hp, hn⟩ := signedMeasure_density_jordan s g hgm hg he
  unfold signedFourier
  rw [hp, hn, charFun_eq_integral_realPhase, charFun_eq_integral_realPhase,
    integral_withDensity_eq_integral_toReal_smul (hgm.ennreal_ofReal)
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) _,
    integral_withDensity_eq_integral_toReal_smul (hgm.neg.ennreal_ofReal)
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) _]
  simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  have hp' : Integrable (fun x => max (g x) 0) := by
    simpa only [Pi.sup_apply, Pi.zero_apply] using hg.sup (integrable_zero ℝ ℝ volume)
  have hn' : Integrable (fun x => max (-g x) 0) := by
    simpa only [Pi.sup_apply, Pi.zero_apply, Pi.neg_apply] using
      hg.neg.sup (integrable_zero ℝ ℝ volume)
  rw [← integral_sub (densityFourier_integrable _ hp' t)
    (densityFourier_integrable _ hn' t)]
  unfold densityFourier
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simp only [← sub_mul, ← Complex.ofReal_sub]
  congr 2
  by_cases h : 0 ≤ g x
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
    ring

/-- The elementary first-moment Fourier bound for an arbitrary finite positive measure. -/
theorem finiteMeasure_charFun_sub_zero_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => |x|) μ) (t : ℝ) :
    ‖charFun μ t - charFun μ 0‖ ≤ |t| * ∫ x : ℝ, |x| ∂μ := by
  have hp (u : ℝ) : Integrable (realPhase u) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by unfold realPhase; fun_prop)
    exact ae_of_all _ (fun x => (realPhase_norm u x).le)
  rw [charFun_eq_integral_realPhase, charFun_eq_integral_realPhase,
    ← integral_sub (hp t) (hp 0)]
  calc
    _ ≤ ∫ x, ‖realPhase t x - realPhase 0 x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, |t| * |x| ∂μ := integral_mono_ae ((hp t).sub (hp 0)).norm
      (hi.const_mul |t|) (ae_of_all _ (fun x => by
        simpa only [realPhase, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
          sub_zero] using realPhase_spatial_difference t x 0))
    _ = _ := integral_const_mul _ _

/-- A finite signed first moment makes the smoothing Fourier quotient locally integrable. -/
theorem signedSmoothing_fourier_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : SignedMeasure ℝ) (hs : s univ = 1)
    (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hs1 : Integrable (fun x : ℝ => |x|) s.totalVariation) (L : ℝ) :
    IntegrableOn (fun t => ‖charFun μ t - signedFourier s t‖ / |t|) (Icc (-L) L) := by
  have hsp : Integrable (fun x : ℝ => |x|) s.toJordanDecomposition.posPart :=
    hs1.left_of_add_measure
  have hsn : Integrable (fun x : ℝ => |x|) s.toJordanDecomposition.negPart :=
    hs1.right_of_add_measure
  let C := (∫ x : ℝ, |x| ∂μ) + (∫ x : ℝ, |x| ∂s.toJordanDecomposition.posPart) +
    (∫ x : ℝ, |x| ∂s.toJordanDecomposition.negPart)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hzero : charFun μ 0 = charFun s.toJordanDecomposition.posPart 0 -
      charFun s.toJordanDecomposition.negPart 0 := by
    rw [charFun_zero, charFun_zero, charFun_zero, ← Complex.ofReal_sub,
      ← signedMeasure_jordan_apply s univ MeasurableSet.univ, hs]
    simp
  have hb (t : ℝ) : ‖charFun μ t - signedFourier s t‖ ≤ |t| * C := by
    have h1 := finiteMeasure_charFun_sub_zero_bound μ hμ t
    have h2 := finiteMeasure_charFun_sub_zero_bound s.toJordanDecomposition.posPart hsp t
    have h3 := finiteMeasure_charFun_sub_zero_bound s.toJordanDecomposition.negPart hsn t
    have he : charFun μ t - signedFourier s t =
        (charFun μ t - charFun μ 0) -
        (charFun s.toJordanDecomposition.posPart t - charFun s.toJordanDecomposition.posPart 0) +
        (charFun s.toJordanDecomposition.negPart t - charFun s.toJordanDecomposition.negPart 0) := by
      rw [hzero]
      unfold signedFourier
      ring
    rw [he]
    have h4 := norm_add_le
      ((charFun μ t - charFun μ 0) -
        (charFun s.toJordanDecomposition.posPart t - charFun s.toJordanDecomposition.posPart 0))
      (charFun s.toJordanDecomposition.negPart t - charFun s.toJordanDecomposition.negPart 0)
    have h5 := norm_sub_le (charFun μ t - charFun μ 0)
      (charFun s.toJordanDecomposition.posPart t - charFun s.toJordanDecomposition.posPart 0)
    dsimp only [C]
    nlinarith
  apply (integrableOn_const (μ := volume) (s := Icc (-L) L) (C := C) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mono'
    (show AEStronglyMeasurable (fun t => ‖charFun μ t - signedFourier s t‖ / |t|) volume from by
      unfold signedFourier
      exact ((measurable_charFun.sub (measurable_charFun.sub measurable_charFun)).norm.div
        measurable_id.abs).aestronglyMeasurable).restrict
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases ht : t = 0
  · simp [ht, hC]
  · exact (div_le_iff₀ (abs_pos.mpr ht)).mpr (by simpa only [mul_comm] using hb t)

/-- The manuscript smoothing inequality for actual finite signed measures with Lipschitz CDFs.
The density interface is instantiated by the direct manuscript proof. -/
theorem general_signed_smoothing (S : PublishedSignedSmoothing)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ)
    (hs : s univ = 1) (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hs1 : Integrable (fun x : ℝ => |x|) s.totalVariation)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x)))
    (L : ℝ) (hL : 0 < L) (x : ℝ) :
    |(μ (Iic x)).toReal - s (Iic x)| ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t|) +
        (24) * (M : ℝ) / L := by
  obtain ⟨g, hgm, hg, hgb, hge⟩ := signedMeasure_lipschitz_has_bounded_density s M hM
  have hmass : (∫ y : ℝ, g y) = 1 := by
    have he := congrArg (fun v : SignedMeasure ℝ => v univ) hge
    dsimp only at he
    rw [withDensityᵥ_apply hg MeasurableSet.univ, Measure.restrict_univ, hs] at he
    exact he
  have hMp : (0 : ℝ) < M := by
    by_contra! h
    have he : g = fun _ => 0 := by
      funext y
      exact abs_nonpos_iff.mp ((hgb y).trans h)
    simp only [he, integral_zero] at hmass
    norm_num at hmass
  have hFourier : densityFourier g = signedFourier s := by
    funext t
    exact (signedFourier_eq_densityFourier s g hgm hg hge t).symm
  have hint := signedSmoothing_fourier_integrable μ s hs hμ hs1 L
  have hμ' : Integrable (fun x : ℝ => x) μ :=
    (integrable_norm_iff (by fun_prop)).mp (by simpa only [Real.norm_eq_abs] using hμ)
  have hg1 := signedMeasure_density_first_integrable s g hgm hg hge hs1
  have hb := S.bound μ inferInstance hμ' g hg hg1 hmass M L hMp hL hgb (hFourier ▸ hint) x
  rw [hFourier] at hb
  have hcdf : (∫ y in Iic x, g y) = s (Iic x) := by
    rw [← withDensityᵥ_apply hg measurableSet_Iic, hge]
  rwa [hcdf] at hb

/-- Supremum form of the full signed-measure smoothing bound. -/
theorem general_signed_smoothing_sup (S : PublishedSignedSmoothing)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : SignedMeasure ℝ)
    (hs : s univ = 1) (hμ : Integrable (fun x : ℝ => |x|) μ)
    (hs1 : Integrable (fun x : ℝ => |x|) s.totalVariation)
    (M : ℝ≥0) (hM : LipschitzWith M (fun x => s (Iic x)))
    (L : ℝ) (hL : 0 < L) :
    sSup (range (fun x : ℝ => |(μ (Iic x)).toReal - s (Iic x)|)) ≤
      (1 / 4) * (∫ t in Icc (-L) L, ‖charFun μ t - signedFourier s t‖ / |t|) +
        (24) * (M : ℝ) / L := by
  apply csSup_le (range_nonempty _)
  rintro y ⟨x, rfl⟩
  exact general_signed_smoothing S μ s hs hμ hs1 M hM L hL x

end BerryEsseen
