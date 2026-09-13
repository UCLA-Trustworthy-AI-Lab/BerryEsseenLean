import BerryEsseen

/-! Full statement groups: primary endpoints and the conjuncts reviewed against the manuscript.
These checks expose actual types; they do not automate natural-language equivalence. -/

-- thm:main
#check BerryEsseen.strict_main_theorem
-- 原显式阈值
#check BerryEsseen.strict_explicit_theorem
-- 紧随主定理的最优性论证
#check BerryEsseen.strict_sharpness

-- lem:signed-smoothing
#check BerryEsseen.manuscript_signed_smoothing_sup

-- lem:jitter
#check BerryEsseen.maximal_span_wassersteinThree_jitter_expansion

-- rem:jitter-width
#check BerryEsseen.raw_wassersteinThree_variable_jitter_expansion_at_raw

-- cor:jitter-envelopes
#check BerryEsseen.wassersteinThree_jitter_envelopes
-- 原limsup结论
#check BerryEsseen.wassersteinThree_jitter_limsup

-- lem:binomial-estimates
#check BerryEsseen.manuscript_binomial_estimates

-- prop:clusters
#check BerryEsseen.manuscript_two_interval_cluster_stability

-- lem:one-sided-loss
#check BerryEsseen.manuscript_one_sided_loss

-- lem:small-cluster-variance
#check BerryEsseen.manuscript_small_cluster_variance_original_parameters

-- lem:two-cluster-local-mass
#check BerryEsseen.compact_centered_measure_local_mass

-- lem:accumulated-cluster-variance
#check BerryEsseen.general_cluster_macroscopic_gap
-- 原Consequently结论
#check BerryEsseen.accumulated_cluster_variance_tendsto_zero

-- lem:attainment
#check BerryEsseen.manuscript_extremal_attainment_full

-- lem:selection
#check BerryEsseen.manuscript_harmonic_selection

-- lem:influence
#check BerryEsseen.contamination_influence
-- 全域非正
#check BerryEsseen.influence_nonpos_at_extremizer
-- 支撑上的零接触
#check BerryEsseen.influence_contact_at_extremizer
-- 原接触等式
#check BerryEsseen.influence_contact_equation

-- lem:gaussian-expansion
#check BerryEsseen.gaussianHn_uniform_remainder
-- 全域三次项加线性余项界
#check BerryEsseen.gaussianHn_global_bound
-- 紧集一致极限
#check BerryEsseen.gaussianHn_uniform_limit

-- prop:bounded-extremizers
#check BerryEsseen.manuscript_bounded_extremizing_sequence

-- lem:limit-extremizer
#check BerryEsseen.selected_extremizer_wassersteinThree_subsequence

-- lem:support-interval
#check BerryEsseen.extremizer_support_limit_interval_general

-- lem:support-separation
#check BerryEsseen.extremizer_support_limit_separation_general

-- lem:effective-selection
#check BerryEsseen.effective_selection

-- lem:effective-low-frequency
#check BerryEsseen.effectiveLowFrequencyIntegral_bound
-- 原0.61与0.048逐点误差界
#check BerryEsseen.effective_charFun_edgeworth_low_frequency

-- lem:effective-near-lattice
#check BerryEsseen.effective_near_lattice

-- lem:effective-cluster-jitter
#check BerryEsseen.effective_cluster_jitter

-- lem:effective-binomial
#check BerryEsseen.manuscript_effective_binomial_branches
-- 任意整数质量上确界
#check BerryEsseen.manuscript_effective_binomial_mass_sup
-- 任意整数中央支
#check BerryEsseen.manuscript_effective_binomial_integer_central
-- 任意整数宽区间支
#check BerryEsseen.manuscript_effective_binomial_integer_wide
-- 原常数下界
#check BerryEsseen.manuscript_effective_binomial_constant_lower

-- lem:effective-small-variance
#check BerryEsseen.manuscript_effective_small_variance
-- 原明确量化gap
#check BerryEsseen.manuscript_effective_small_variance_positive

-- lem:effective-local-mass
#check BerryEsseen.manuscript_effective_local_mass

-- prop:effective-clusters
#check BerryEsseen.manuscript_effective_cluster_stability
-- 原双区间与两种参数的结论
#check BerryEsseen.manuscript_effective_interval_stability_support

-- lem:effective-lattice-stability
#check BerryEsseen.effective_lattice_stability

-- lem:effective-global-jitter
#check BerryEsseen.effective_global_jitter

-- lem:effective-identification
#check BerryEsseen.effective_identification_with_global_jitter

-- prop:effective-confinement
#check BerryEsseen.manuscript_effective_full_support

