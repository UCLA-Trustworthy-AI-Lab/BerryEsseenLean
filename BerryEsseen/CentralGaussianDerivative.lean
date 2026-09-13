import BerryEsseen.PublishedWassersteinThree
import BerryEsseen.BinomialExpansion

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem standardNormalDensity_lipschitz (x y : ℝ) :
    |standardNormalDensity x - standardNormalDensity y| ≤ 3 * phi0 * |x - y| := by
  have hd (t : ℝ) : ‖-t * standardNormalDensity t‖ ≤ 3 * phi0 := by
    rw [Real.norm_eq_abs, neg_mul, abs_neg]
    exact gaussian_first_monomial_bound t
  simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (standardNormalDensity_hasDerivAt t).hasDerivWithinAt) (fun t _ => hd t) (mem_univ y) (mem_univ x)

def centralDensityFloor (M : ℝ) : ℝ := phi0 * Real.exp (-(M ^ 2) / 2)

theorem centralDensityFloor_pos (M : ℝ) : 0 < centralDensityFloor M := mul_pos phi0_pos (Real.exp_pos _)

theorem standardNormalDensity_central_lower (M x : ℝ) (hM : 0 ≤ M) (hx : |x| ≤ M) :
    centralDensityFloor M ≤ standardNormalDensity x := by
  rw [standardNormalDensity_formula]
  unfold centralDensityFloor
  apply mul_le_mul_of_nonneg_left _ phi0_pos.le
  apply Real.exp_le_exp.2
  have hsq := pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [sq_abs] at hsq
  linarith

theorem positive_ratio_of_tenth_errors (A D C m : ℝ) (hm : 0 < m) (hC : m ≤ C)
    (hA : |A - C| ≤ m / 10) (hD : |D - C| ≤ m / 10) :
    0 < D ∧ 3 / 4 ≤ A / D ∧ A / D ≤ 5 / 4 := by
  have ha := abs_le.1 hA
  have hd := abs_le.1 hD
  have hpos : 0 < D := by linarith
  refine ⟨hpos, (le_div_iff₀ hpos).2 ?_, (div_le_iff₀ hpos).2 ?_⟩ <;> linarith

def clusterGaussianIncrement (p : ℝ) (n k : ℕ) (s u : ℝ) : ℝ :=
  (normalCDF (((k : ℝ) - (n : ℝ) * p + u) / Real.sqrt ((n : ℝ) * (p * (1 - p) + s))) -
    normalCDF (((k : ℝ) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * (p * (1 - p) + s)))) / binomialWeight p n k

theorem gaussian_increment_hasDerivAt (t a b u : ℝ) :
    HasDerivAt (fun w => (normalCDF ((t + w) / a) - normalCDF (t / a)) / b)
      (standardNormalDensity ((t + u) / a) / (a * b)) u := by
  have h := (((normalCDF_hasDerivAt ((t + u) / a)).comp u
    (((hasDerivAt_const u t).add (hasDerivAt_id u)).div_const a)).sub_const (normalCDF (t / a))).div_const b
  convert h using 1
  simp only [zero_add, mul_one]
  ring

theorem clusterGaussianIncrement_deriv (p : ℝ) (n k : ℕ) (s u : ℝ) :
    deriv (clusterGaussianIncrement p n k s) u =
      standardNormalDensity (((k : ℝ) - (n : ℝ) * p + u) / Real.sqrt ((n : ℝ) * (p * (1 - p) + s))) /
        (Real.sqrt ((n : ℝ) * (p * (1 - p) + s)) * binomialWeight p n k) :=
  (gaussian_increment_hasDerivAt _ _ _ _).deriv

theorem scaled_argument_density_bound (r v s z u M U : ℝ) (hr : 0 < r) (hv : 0 < v) (hs : 0 ≤ s)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hz : |z| ≤ M) (hu : |u| ≤ U) :
    |standardNormalDensity ((r * Real.sqrt v * z + u) / (r * Real.sqrt (v + s))) - standardNormalDensity z| ≤
      3 * phi0 * (M * |Real.sqrt v / Real.sqrt (v + s) - 1| + U / (r * Real.sqrt (v + s))) := by
  have hsqrt : 0 < Real.sqrt (v + s) := Real.sqrt_pos.2 (by linarith)
  have he : (r * Real.sqrt v * z + u) / (r * Real.sqrt (v + s)) - z =
      z * (Real.sqrt v / Real.sqrt (v + s) - 1) + u / (r * Real.sqrt (v + s)) := by
    field_simp [hr.ne', hsqrt.ne']
    ring
  have harg : |(r * Real.sqrt v * z + u) / (r * Real.sqrt (v + s)) - z| ≤
      M * |Real.sqrt v / Real.sqrt (v + s) - 1| + U / (r * Real.sqrt (v + s)) := by
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_div, abs_of_pos (mul_pos hr hsqrt)]
    exact add_le_add (mul_le_mul_of_nonneg_right hz (abs_nonneg _)) (div_le_div_of_nonneg_right hu (mul_pos hr hsqrt).le)
  exact (standardNormalDensity_lipschitz _ _).trans (mul_le_mul_of_nonneg_left harg (mul_pos (by norm_num) phi0_pos).le)

theorem scaled_density_denominator_bound (b σ z d : ℝ) (hσ : 0 ≤ σ) (hd : 0 ≤ d)
    (hb : |b - hE * standardNormalDensity z| ≤ d) :
    |σ * b - standardNormalDensity z| ≤ σ * d + |σ * hE - 1| * phi0 := by
  have he : σ * b - standardNormalDensity z = σ * (b - hE * standardNormalDensity z) +
      (σ * hE - 1) * standardNormalDensity z := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul σ _, abs_of_nonneg hσ, abs_mul (σ * hE - 1) _, abs_of_pos (standardNormalDensity_pos z)]
  exact add_le_add (mul_le_mul_of_nonneg_left hb hσ)
    (mul_le_mul_of_nonneg_left (standardNormalDensity_le_phi0 z) (abs_nonneg _))

theorem binomial_central_gaussian_derivative (W : PublishedWassersteinThreeTopology) (S : PublishedSignedSmoothing) (B : PublishedBernoulliBound)
    (p : ℕ → ℝ) (hp : ∀ j, p j ∈ Ioo 0 1) (hcentral : ∀ j, p j ∈ Icc (2 / 5) (3 / 5))
    (hlim : Tendsto p atTop (𝓝 pE)) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (hn2 : ∀ j, 2 ≤ n j)
    (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (hslim : Tendsto s atTop (𝓝 0)) (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ j in atTop, ∀ k : ℕ, k ≤ n j → |binomialZ (p j) (n j) k| ≤ M →
      0 < binomialWeight (p j) (n j) k ∧
      ∀ u : ℝ, |u| ≤ 3 / 5 →
        3 / 4 ≤ deriv (clusterGaussianIncrement (p j) (n j) k (s j)) u ∧
        deriv (clusterGaussianIncrement (p j) (n j) k (s j)) u ≤ 5 / 4 := by
  let v : ℕ → ℝ := fun j => p j * (1 - p j)
  let σ : ℕ → ℝ := fun j => Real.sqrt (v j + s j)
  let r : ℕ → ℝ := fun j => Real.sqrt (n j : ℝ)
  let m := centralDensityFloor M
  have hm : 0 < m := centralDensityFloor_pos M
  have hv : ∀ j, 0 < v j := fun j => mul_pos (hp j).1 (sub_pos.2 (hp j).2)
  have hσ : ∀ j, 0 < σ j := fun j => Real.sqrt_pos.2 (by have := hv j; have := hs j; linarith)
  have hr : ∀ j, 0 < r j := fun j => Real.sqrt_pos.2 (by exact_mod_cast (show 0 < n j by have := hn2 j; omega))
  have hvlim : Tendsto v atTop (𝓝 (pE * (1 - pE))) := hlim.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hlim)
  have hσlim : Tendsto σ atTop (𝓝 sigmaE) := by
    simpa only [add_zero, sigmaE, qE] using (hvlim.add hslim).sqrt
  have hσbase : Tendsto (fun j => Real.sqrt (v j)) atTop (𝓝 sigmaE) := by
    simpa only [sigmaE, qE] using hvlim.sqrt
  have hrlim : Tendsto r atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  have hrat : Tendsto (fun j => Real.sqrt (v j) / σ j - 1) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_self sigmaE_pos.ne', sub_self] using (hσbase.div hσlim sigmaE_pos.ne').sub_const 1
  have htail : Tendsto (fun j => (3 / 5 : ℝ) / (r j * σ j)) atTop (𝓝 (0 : ℝ)) := by
    have h := ((tendsto_const_nhds (x := (3 / 5 : ℝ))).div_atTop hrlim).div hσlim sigmaE_pos.ne'
    change Tendsto (fun j => ((3 / 5 : ℝ) / r j) / σ j) atTop (𝓝 (0 / sigmaE)) at h
    simpa only [div_div, mul_assoc, zero_div] using h
  have hnum : Tendsto (fun j => 3 * phi0 * (M * |Real.sqrt (v j) / σ j - 1| + (3 / 5 : ℝ) / (r j * σ j)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero, mul_zero, zero_add] using ((hrat.abs.const_mul M).add htail).const_mul (3 * phi0)
  have hunit : sigmaE * hE = 1 := by unfold hE; field_simp [sigmaE_pos.ne']
  have hfactor : Tendsto (fun j => |σ j * hE - 1| * phi0) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hunit, sub_self, abs_zero, zero_mul] using (((hσlim.mul_const hE).sub_const 1).abs).mul_const phi0
  let d := m / (20 * (sigmaE + 1))
  have hd : 0 < d := div_pos hm (by have := sigmaE_pos; positivity)
  filter_upwards [binomial_uniform_local_mass_pE W S B p hp hcentral hlim n hn hn2 d hd,
    hnum.eventually (gt_mem_nhds (by positivity : 0 < m / 10)),
    hfactor.eventually (gt_mem_nhds (by positivity : 0 < m / 20)),
    hσlim.eventually (gt_mem_nhds (by linarith : sigmaE < sigmaE + 1))] with j hjmass hjnum hjfactor hjσ
  intro k hk hzk
  let z := binomialZ (p j) (n j) k
  let w := binomialWeight (p j) (n j) k
  have hC : m ≤ standardNormalDensity z := standardNormalDensity_central_lower M z hM hzk
  have hmass : |r j * w - hE * standardNormalDensity z| ≤ d := (hjmass k hk).le
  have hden := scaled_density_denominator_bound (r j * w) (σ j) z d (hσ j).le hd.le hmass
  have hden' : |σ j * (r j * w) - standardNormalDensity z| ≤ m / 10 := by
    apply hden.trans
    have hh := mul_le_mul_of_nonneg_right hjσ.le hd.le
    have he : (sigmaE + 1) * d = m / 20 := by
      have hnz : sigmaE + 1 ≠ 0 := (by have := sigmaE_pos; positivity : 0 < sigmaE + 1).ne'
      dsimp only [d]
      field_simp [hnz] <;> ring
    rw [he] at hh
    linarith
  have hD : 0 < σ j * (r j * w) := by have hh := abs_le.1 hden'; linarith
  have hw : 0 < w := (mul_pos_iff_of_pos_left (hr j)).1 ((mul_pos_iff_of_pos_left (hσ j)).1 hD)
  refine ⟨hw, ?_⟩
  intro u hu
  have hN := scaled_argument_density_bound (r j) (v j) (s j) z u M (3 / 5) (hr j) (hv j) (hs j)
    hM (by norm_num) hzk hu
  have ht : r j * Real.sqrt (v j) * z = (k : ℝ) - n j * p j := by
    calc
      r j * Real.sqrt (v j) * z = Real.sqrt (v j) * (r j * z) := by ring
      _ = _ := by
        rw [binomialZ_scaling (p j) (hp j) (n j) (by have := hn2 j; omega) k]
        change Real.sqrt (v j) * ((k - n j * p j) / Real.sqrt (v j)) = _
        exact mul_div_cancel₀ _ (Real.sqrt_pos.2 (hv j)).ne'
  rw [ht] at hN
  have hroot : Real.sqrt ((n j : ℝ) * (p j * (1 - p j) + s j)) = r j * σ j := Real.sqrt_mul (Nat.cast_nonneg _) _
  have hN' : |standardNormalDensity (((k : ℝ) - n j * p j + u) / (r j * σ j)) - standardNormalDensity z| ≤ m / 10 :=
    hN.trans hjnum.le
  have hratio := positive_ratio_of_tenth_errors
    (standardNormalDensity (((k : ℝ) - n j * p j + u) / (r j * σ j)))
    (σ j * (r j * w)) (standardNormalDensity z) m hm hC hN' hden'
  rw [clusterGaussianIncrement_deriv, hroot]
  have he : (r j * σ j) * binomialWeight (p j) (n j) k = σ j * (r j * w) := by dsimp only [w]; ring
  rw [he]
  exact hratio.2

end BerryEsseen
