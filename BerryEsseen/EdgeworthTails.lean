import BerryEsseen.CompactRawFourier

/-! Gaussian decay of the signed Edgeworth comparison away from zero. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem edgeworthChar_norm_bound (n : ℕ) (κ t : ℝ) :
    ‖edgeworthChar n κ t‖ ≤ Real.exp (-t ^ 2 / 2) *
      (1 + |κ| * |t| ^ 3 / (6 * Real.sqrt (n : ℝ))) := by
  unfold edgeworthChar
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hn := norm_sub_le (1 : ℂ) ((κ : ℂ) * (t : ℂ) ^ 3 * Complex.I / (6 * Real.sqrt (n : ℝ)))
  simpa only [norm_one, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, Complex.norm_ofNat, abs_of_nonneg (Real.sqrt_nonneg _)] using hn

theorem edgeworthChar_rescaled_norm_bound (n : ℕ) (hn : 1 ≤ n) (κ u : ℝ) :
    ‖edgeworthChar n κ (Real.sqrt (n : ℝ) * u)‖ ≤
      Real.exp (-(n : ℝ) * u ^ 2 / 2) * (1 + |κ| * (n : ℝ) * |u| ^ 3 / 6) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hb := edgeworthChar_norm_bound n κ (Real.sqrt (n : ℝ) * u)
  rw [mul_pow, Real.sq_sqrt hnpos.le, abs_mul, abs_of_pos hs, mul_pow] at hb
  convert hb using 1
  rw [neg_mul]
  congr 2
  field_simp [hs.ne']
  rw [Real.sq_sqrt hnpos.le]
  ring

def rawEdgeworthIntegrand (n : ℕ) (κ u : ℝ) : ℝ :=
  ‖edgeworthChar n κ (Real.sqrt (n : ℝ) * u)‖ / |u|

theorem rawEdgeworthIntegrand_nonneg (n : ℕ) (κ u : ℝ) : 0 ≤ rawEdgeworthIntegrand n κ u := by
  unfold rawEdgeworthIntegrand
  positivity

theorem rawEdgeworthIntegrand_measurable (n : ℕ) (κ : ℝ) : Measurable (rawEdgeworthIntegrand n κ) := by
  unfold rawEdgeworthIntegrand edgeworthChar
  fun_prop

theorem rawEdgeworthIntegrand_compact_bound (n : ℕ) (hn : 1 ≤ n) (κ B a T u : ℝ)
    (hκ : |κ| ≤ B) (ha : 0 < a) (hl : a ≤ |u|) (hu : |u| ≤ T) :
    rawEdgeworthIntegrand n κ u ≤ Real.exp (-(n : ℝ) * a ^ 2 / 2) *
      (1 + B * (n : ℝ) * T ^ 3 / 6) / a := by
  have hB : 0 ≤ B := (abs_nonneg κ).trans hκ
  have hT : 0 ≤ T := (abs_nonneg u).trans hu
  have hu2 : a ^ 2 ≤ u ^ 2 := by nlinarith [sq_abs u]
  have he : Real.exp (-(n : ℝ) * u ^ 2 / 2) ≤ Real.exp (-(n : ℝ) * a ^ 2 / 2) := by
    apply Real.exp_le_exp.2
    nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.2 hu2)]
  have hpoly : 1 + |κ| * (n : ℝ) * |u| ^ 3 / 6 ≤ 1 + B * (n : ℝ) * T ^ 3 / 6 := by
    gcongr
  have hb := (edgeworthChar_rescaled_norm_bound n hn κ u).trans
    (mul_le_mul he hpoly (by positivity) (Real.exp_pos _).le)
  unfold rawEdgeworthIntegrand
  exact (div_le_div_of_nonneg_right hb (abs_nonneg u)).trans
    (div_le_div_of_nonneg_left (by positivity) ha hl)

theorem sqrt_mul_polynomial_exp_decay (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (D δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * Real.exp (-(n j : ℝ) * δ / 2) * (1 + D * (n j : ℝ)))
      atTop (𝓝 0) := by
  have h1 := sqrt_mul_exp_decay n hn δ hδ
  have h3 : Tendsto (fun j => Real.sqrt (n j : ℝ) * (n j : ℝ) *
      Real.exp (-(n j : ℝ) * δ / 2)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 / 2) (δ / 2)
      (div_pos hδ (by norm_num))).comp (tendsto_natCast_atTop_atTop.comp hn)
    convert hh using 1
    funext j
    dsimp only [Function.comp_apply]
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by norm_num) zero_le_one,
      Real.rpow_one, Real.sqrt_eq_rpow]
    congr 2
    ring
  convert h1.add (h3.const_mul D) using 1
  · funext j
    ring
  · ring

theorem rawEdgeworth_integrableOn (n : ℕ) (hn : 1 ≤ n) (κ B a T : ℝ)
    (hκ : |κ| ≤ B) (ha : 0 < a) (K : Set ℝ) (hK : IsCompact K)
    (hl : ∀ u ∈ K, a ≤ |u|) (hu : ∀ u ∈ K, |u| ≤ T) :
    IntegrableOn (rawEdgeworthIntegrand n κ) K := by
  have hi : IntegrableOn (fun _ : ℝ => Real.exp (-(n : ℝ) * a ^ 2 / 2) *
      (1 + B * (n : ℝ) * T ^ 3 / 6) / a) K := integrableOn_const hK.measure_lt_top.ne
  apply hi.mono' (rawEdgeworthIntegrand_measurable n κ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with u humem
  rw [Real.norm_eq_abs, abs_of_nonneg (rawEdgeworthIntegrand_nonneg n κ u)]
  exact rawEdgeworthIntegrand_compact_bound n hn κ B a T u hκ ha (hl u humem) (hu u humem)

theorem compact_rawEdgeworth_integral_tendsto_zero (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (κ : ℕ → ℝ) (B a T : ℝ) (hκ : ∀ j, |κ j| ≤ B) (ha : 0 < a)
    (K : Set ℝ) (hK : IsCompact K) (hl : ∀ u ∈ K, a ≤ |u|) (hu : ∀ u ∈ K, |u| ≤ T) :
    Tendsto (fun j => Real.sqrt (n j : ℝ) * ∫ u in K, rawEdgeworthIntegrand (n j) (κ j) u)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => (volume K).toReal / a *
      (Real.sqrt (n j : ℝ) * Real.exp (-(n j : ℝ) * a ^ 2 / 2) *
        (1 + B * T ^ 3 / 6 * (n j : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (sqrt_mul_polynomial_exp_decay n hn (B * T ^ 3 / 6)
      (a ^ 2) (sq_pos_of_pos ha)).const_mul ((volume K).toReal / a)
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun j => mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg (rawEdgeworthIntegrand_nonneg (n j) (κ j))))
  · filter_upwards [hn.eventually (eventually_ge_atTop 1)] with j hnj
    have hiC : IntegrableOn (fun _ : ℝ => Real.exp (-(n j : ℝ) * a ^ 2 / 2) *
        (1 + B * (n j : ℝ) * T ^ 3 / 6) / a) K := integrableOn_const hK.measure_lt_top.ne
    have hb := integral_mono_ae (rawEdgeworth_integrableOn (n j) hnj (κ j) B a T (hκ j) ha K hK hl hu) hiC
      (show ∀ᵐ u ∂volume.restrict K, rawEdgeworthIntegrand (n j) (κ j) u ≤
          Real.exp (-(n j : ℝ) * a ^ 2 / 2) * (1 + B * (n j : ℝ) * T ^ 3 / 6) / a from by
        filter_upwards [ae_restrict_mem hK.measurableSet] with u humem
        exact rawEdgeworthIntegrand_compact_bound (n j) hnj (κ j) B a T u (hκ j) ha (hl u humem) (hu u humem))
    rw [setIntegral_const] at hb
    have hh := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (n j : ℝ))
    convert hh using 1
    change _ = Real.sqrt (n j : ℝ) * ((volume K).toReal * _)
    ring

end BerryEsseen
