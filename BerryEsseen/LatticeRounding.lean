import BerryEsseen.EffectiveLatticeStability
import BerryEsseen.EffectiveNearLattice
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology
namespace BerryEsseen

def latticeRound (a h x : ℝ) : ℝ := a + h * (round ((x - a) / h) : ℝ)
def latticeRoundingIndices (a h : ℝ) : Finset ℤ :=
  Finset.Icc ⌊(-6 - a) / h + 1 / 2⌋ ⌊(6 - a) / h + 1 / 2⌋

theorem latticeRound_measurable (a h : ℝ) : Measurable (latticeRound a h) := by
  have hr : Measurable (fun x : ℝ => round ((x - a) / h)) := by
    simp_rw [round_eq]
    fun_prop
  exact measurable_const.add (measurable_const.mul ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp hr))

theorem latticeRound_mem (a h x : ℝ) : latticeRound a h x ∈ affineLattice a h :=
  ⟨round ((x - a) / h), rfl⟩

theorem lattice_distance_scale (a h x : ℝ) (hh : 0 < h) (k : ℤ) :
    |x - (a + h * (k : ℝ))| = h * |(x - a) / h - (k : ℝ)| := by
  calc
    _ = |h * ((x - a) / h - (k : ℝ))| := by congr 1; field_simp; ring
    _ = _ := by rw [abs_mul, abs_of_pos hh]

theorem latticeRound_error_le_half (a h x : ℝ) (hh : 0 < h) :
    |x - latticeRound a h x| ≤ h / 2 := by
  rw [latticeRound, lattice_distance_scale a h x hh]
  have hb := abs_sub_round ((x - a) / h)
  nlinarith only [mul_le_mul_of_nonneg_left hb hh.le]

theorem latticeRound_nearest (a h x : ℝ) (hh : 0 < h) (k : ℤ) :
    |x - latticeRound a h x| ≤ |x - (a + h * (k : ℝ))| := by
  rw [latticeRound, lattice_distance_scale a h x hh, lattice_distance_scale a h x hh]
  exact mul_le_mul_of_nonneg_left (round_le ((x - a) / h) k) hh.le

theorem latticeRound_infDist (a h x : ℝ) (hh : 0 < h) :
    Metric.infDist x (affineLattice a h) = |x - latticeRound a h x| := by
  apply le_antisymm
  · simpa only [Real.dist_eq] using Metric.infDist_le_dist_of_mem (latticeRound_mem a h x)
  · apply (Metric.le_infDist (show (affineLattice a h).Nonempty from ⟨a, ⟨0, by simp⟩⟩)).mpr
    rintro y ⟨k, rfl⟩
    simpa only [Real.dist_eq] using latticeRound_nearest a h x hh k

theorem latticeRound_bounded (a h x : ℝ) (hh : 0 < h) (hupper : h ≤ 4 * Real.pi)
    (hx : |x| ≤ 6) : |latticeRound a h x| < 13 := by
  have he := latticeRound_error_le_half a h x hh
  have ht := abs_sub_le (latticeRound a h x) x 0
  rw [sub_zero, sub_zero, abs_sub_comm (latticeRound a h x) x] at ht
  nlinarith [Real.pi_lt_d2]

theorem integral_square_ge_square_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℝ) (hi : Integrable f μ) (hi2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let m := ∫ x, f x ∂μ
  have he : (fun x => (f x - m) ^ 2) = fun x => f x ^ 2 - 2 * m * f x + m ^ 2 := by
    funext x
    ring
  have hp : (0 : ℝ) ≤ ∫ x, (f x - m) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg (f x - m))
  have hisub : Integrable (fun x => f x ^ 2 - 2 * m * f x) μ := hi2.sub (hi.const_mul (2 * m))
  rw [he, integral_add hisub (integrable_const (m ^ 2)),
    integral_sub hi2 (hi.const_mul (2 * m)), integral_const_mul] at hp
  simp only [integral_const, probReal_univ, one_smul] at hp
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * m * m + m ^ 2 at hp
  dsimp [m] at hp
  nlinarith only [hp]

theorem latticeRound_error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a h : ℝ) (hh : 0 < h) :
    Integrable (fun x => |x - latticeRound a h x|) μ ∧
      Integrable (fun x => |x - latticeRound a h x| ^ 2) μ := by
  have hm := (measurable_id.sub (latticeRound_measurable a h)).abs
  refine ⟨real_function_integrable_of_abs_le μ _ (h / 2) hm (by
    filter_upwards [] with x
    simpa only [abs_abs] using latticeRound_error_le_half a h x hh), ?_⟩
  apply real_function_integrable_of_abs_le μ _ ((h / 2) ^ 2) (hm.pow_const 2)
  filter_upwards [] with x
  simpa only [abs_pow, abs_abs] using pow_le_pow_left₀ (abs_nonneg (x - latticeRound a h x))
    (latticeRound_error_le_half a h x hh) 2

theorem latticeRound_mean_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a h t : ℝ) (hh : 0 < h) (ht : 0 ≤ t)
    (herror : (∫ x, Metric.infDist x (affineLattice a h) ^ 2 ∂μ) ≤ 2 * Real.pi ^ 2 * t) :
    (∫ x, |x - latticeRound a h x| ∂μ) ≤ 5 * Real.sqrt t := by
  have hi := latticeRound_error_integrable μ a h hh
  have hs := integral_square_ge_square_integral μ _ hi.1 hi.2
  simp_rw [latticeRound_infDist a h _ hh] at herror
  have hp : (0 : ℝ) ≤ ∫ x, |x - latticeRound a h x| ∂μ := integral_nonneg (fun x => abs_nonneg (x - latticeRound a h x))
  have hpi : 2 * Real.pi ^ 2 ≤ 25 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hbound := (mul_le_mul_of_nonneg_right hpi ht)
  nlinarith only [hs, herror, hbound, hp, Real.sqrt_nonneg t, Real.sq_sqrt ht]

theorem latticeRound_index_mem (a h x : ℝ) (hh : 0 < h) (hx : |x| ≤ 6) :
    round ((x - a) / h) ∈ latticeRoundingIndices a h := by
  rw [latticeRoundingIndices, Finset.mem_Icc, round_eq]
  constructor <;> apply Int.floor_mono
  · have hd : (-6 - a) / h ≤ (x - a) / h := div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).1]) hh.le
    linarith
  · have hd : (x - a) / h ≤ (6 - a) / h := div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).2]) hh.le
    linarith

theorem latticeRoundingIndices_card (a h : ℝ) (hlower : Real.pi / 500 ≤ h) :
    (latticeRoundingIndices a h).card < 2000 := by
  have hh : 0 < h := (div_pos Real.pi_pos (by norm_num)).trans_le hlower
  have hlo : ⌊(-6 - a) / h + 1 / 2⌋ ≤ ⌊(6 - a) / h + 1 / 2⌋ := by
    apply Int.floor_mono
    have hd : (-6 - a) / h ≤ (6 - a) / h := div_le_div_of_nonneg_right (by linarith) hh.le
    linarith
  have hc := Int.card_Icc_of_le ⌊(-6 - a) / h + 1 / 2⌋ ⌊(6 - a) / h + 1 / 2⌋ (by omega)
  have hlo' := Int.lt_floor_add_one ((-6 - a) / h + 1 / 2)
  have hhi' := Int.floor_le ((6 - a) / h + 1 / 2)
  have hr : ((latticeRoundingIndices a h).card : ℝ) < 12 / h + 2 := by
    have hcr : ((latticeRoundingIndices a h).card : ℝ) =
        (⌊(6 - a) / h + 1 / 2⌋ : ℝ) + 1 - (⌊(-6 - a) / h + 1 / 2⌋ : ℝ) := by
      unfold latticeRoundingIndices
      exact_mod_cast hc
    rw [hcr]
    have he : (6 - a) / h - (-6 - a) / h = 12 / h := by ring
    linarith
  have hnum : 12 / h + 2 < 2000 := by
    have h : 12 / h < 1998 := (div_lt_iff₀ hh).mpr (by nlinarith [Real.pi_gt_d2])
    linarith
  exact_mod_cast hr.trans hnum

end BerryEsseen
