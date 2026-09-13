import BerryEsseen.PublishedNonIID
import BerryEsseen.CentralGaussianDerivative

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace BerryEsseen

theorem normalCDF_interval_central_lower (M a b : ℝ) (hM : 0 ≤ M) (ha : |a| ≤ M)
    (hb : |b| ≤ M) (hab : a ≤ b) :
    (b - a) * centralDensityFloor M ≤ normalCDF b - normalCDF a := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope normalCDF standardNormalDensity hab
    normalCDF_continuous.continuousOn (fun x _ => normalCDF_hasDerivAt x)
  have hcm : |c| ≤ M := by
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [hc.1, hc.2]
  have h := standardNormalDensity_central_lower M c hM hcm
  rw [he] at h
  have hh := (le_div_iff₀ (sub_pos.2 hab)).1 h
  nlinarith only [hh]

theorem twoNoiseBlock_Ioc_lower (S : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (ht : 0 < (twoNoiseBlock P Q n k).secondMoment)
    (M a b : ℝ) (hM : 0 ≤ M) (hab : a ≤ b)
    (ha : |a / Real.sqrt (twoNoiseBlock P Q n k).secondMoment| ≤ M)
    (hb : |b / Real.sqrt (twoNoiseBlock P Q n k).secondMoment| ≤ M) :
    ((b - a) * centralDensityFloor M - (1.12 : ℝ) * ε) / Real.sqrt (twoNoiseBlock P Q n k).secondMoment ≤
      (twoNoiseBlock P Q n k).measure.real (Ioc a b) := by
  have hs := Real.sqrt_pos.2 ht
  have hnormal := normalCDF_interval_central_lower M _ _ hM ha hb (div_le_div_of_nonneg_right hab hs.le)
  have hleft := abs_le.1 (twoNoiseBlock_normal_bound S P Q ε hε hP hQ n k hn hk ht a)
  have hright := abs_le.1 (twoNoiseBlock_normal_bound S P Q ε hε hP hQ n k hn hk ht b)
  rw [← cdf_interval_mass _ hab]
  have he : ((b - a) * centralDensityFloor M - (1.12 : ℝ) * ε) / Real.sqrt (twoNoiseBlock P Q n k).secondMoment =
      (b / Real.sqrt (twoNoiseBlock P Q n k).secondMoment - a / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) * centralDensityFloor M -
      2 * ((0.56 : ℝ) * ε / Real.sqrt (twoNoiseBlock P Q n k).secondMoment) := by ring
  rw [he]
  linarith

theorem twoNoiseBlock_open_interval_lower (S : PublishedNonIIDBound) (P Q : CenteredFourthLaw)
    (ε : ℝ) (hε : 0 ≤ ε) (hP : ∀ᵐ x ∂P.measure, |x| ≤ ε) (hQ : ∀ᵐ x ∂Q.measure, |x| ≤ ε)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (ht : 0 < (twoNoiseBlock P Q n k).secondMoment)
    (M a b : ℝ) (hM : 0 ≤ M) (hab : a < b)
    (ha : |a / Real.sqrt (twoNoiseBlock P Q n k).secondMoment| ≤ M)
    (hb : |b / Real.sqrt (twoNoiseBlock P Q n k).secondMoment| ≤ M) :
    ((b - a) / 2 * centralDensityFloor M - (1.12 : ℝ) * ε) / Real.sqrt (twoNoiseBlock P Q n k).secondMoment ≤
      (twoNoiseBlock P Q n k).measure.real (Ioo a b) := by
  let a' := (3 * a + b) / 4
  let b' := (a + 3 * b) / 4
  have haa : a < a' := by dsimp [a']; linarith
  have hbb : b' < b := by dsimp [b']; linarith
  have hab' : a' ≤ b' := by dsimp [a', b']; linarith
  have hs := (Real.sqrt_pos.2 ht).le
  have hmid : ∀ z ∈ Icc a b, |z / Real.sqrt (twoNoiseBlock P Q n k).secondMoment| ≤ M := by
    intro z hz
    rw [abs_le] at ha hb ⊢
    constructor
    · exact ha.1.trans (div_le_div_of_nonneg_right hz.1 hs)
    · exact (div_le_div_of_nonneg_right hz.2 hs).trans hb.2
  have h := twoNoiseBlock_Ioc_lower S P Q ε hε hP hQ n k hn hk ht M a' b' hM hab'
    (hmid a' ⟨haa.le, hab'.trans hbb.le⟩) (hmid b' ⟨haa.le.trans hab', hbb.le⟩)
  have he : b' - a' = (b - a) / 2 := by dsimp [a', b']; ring
  rw [he] at h
  apply h.trans (measureReal_mono ?_)
  intro z hz
  exact ⟨haa.trans hz.1, hz.2.trans_lt hbb⟩

end BerryEsseen
