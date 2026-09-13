import BerryEsseen.StrictResults
import Lean

/-!
This is a proof-expression dependency audit, not an import audit. It starts
from the checked kernel declaration of the new manuscript main theorem and
recursively reads the actual values of theorems, definitions, and opaque
declarations. It records witness paths to required and forbidden endpoints.
It is diagnostic metaprogramming and does not contribute a mathematical proof.
-/

namespace StrictProofAudit
open Lean

def valueConstants (c : ConstantInfo) : Array Name :=
  match c with
  | .thmInfo v => v.value.getUsedConstants
  | .defnInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

def isProject (n : Name) : Bool :=
  n.toString.startsWith "BerryEsseen." || n.toString.startsWith "_private.BerryEsseen."

structure Traversal where
  visited : NameSet := {}
  order : Array Name := #[]
  parent : NameMap Name := {}
  missing : Array Name := #[]

def traverse (env : Environment) (root : Name) (includeTypes : Bool) : Traversal := Id.run do
  let mut state : Traversal := { visited := ({} : NameSet).insert root, order := #[root] }
  let mut i := 0
  while i < state.order.size do
    let name := state.order[i]!
    i := i + 1
    match env.checked.get.find? name with
    | none => state := { state with missing := state.missing.push name }
    | some info =>
      let deps := if includeTypes then valueConstants info ++ info.type.getUsedConstants else valueConstants info
      for dep in deps do
        unless state.visited.contains dep do
          state := { state with
            visited := state.visited.insert dep
            order := state.order.push dep
            parent := state.parent.insert dep name }
  return state

def pathTo (root : Name) (t : Traversal) (target : Name) : Array Name := Id.run do
  if !t.visited.contains target then return #[]
  let mut path := #[target]
  let mut curr := target
  let mut remaining := t.order.size
  while curr != root && remaining > 0 do
    remaining := remaining - 1
    match t.parent.find? curr with
    | none => return path.reverse
    | some par =>
      path := path.push par
      curr := par
  return path.reverse

def checkpoint (root : Name) (t : Traversal) (n : Name) : Json := Json.mkObj [
  ("name", toJson n.toString),
  ("present", toJson (t.visited.contains n)),
  ("path", toJson ((pathTo root t n).map Name.toString))]

def required : Array Name := #[
  `BerryEsseen.manuscript_probability_primitive_L1,
  `BerryEsseen.manuscript_cdf_dirac_L1_identity,
  `BerryEsseen.manuscript_signed_primitive_L1_bound,
  `BerryEsseen.manuscript_signed_primitive_norm_le,
  `BerryEsseen.manuscript_signed_primitive_eq,
  `BerryEsseen.manuscriptStepDifference_section_integrable,
  `BerryEsseen.manuscriptStepDifference_integral_norm,
  `BerryEsseen.manuscriptStepDifference_prod_integrable,
  `BerryEsseen.manuscriptStepDifference_norm_integral,
  `BerryEsseen.manuscript_uniform_forward_quarter_gap,
  `BerryEsseen.manuscript_uniform_backward_quarter_gap,
  `BerryEsseen.manuscript_uniform_forward_weighted_identity,
  `BerryEsseen.manuscript_uniform_backward_weighted_identity,
  `BerryEsseen.manuscript_uniform_forward_weight_pointwise,
  `BerryEsseen.manuscript_uniform_backward_weight_pointwise,
  `BerryEsseen.manuscript_unit_uniform_cdf,
  `BerryEsseen.manuscript_bernoulli_sine_identity,
  `BerryEsseen.manuscript_sine_lower,
  `BerryEsseen.manuscript_attainment_moment_equality,
  `BerryEsseen.manuscript_attained_full_ratio,
  `BerryEsseen.manuscript_extremal_attainment_full,
  `BerryEsseen.manuscript_characteristicSquareCurvature_zero,
  `BerryEsseen.manuscript_characteristicSquareSlope_zero,
  `BerryEsseen.manuscript_zero_quadratic_drop,
  `BerryEsseen.quadratic_upper_at_critical_point,
  `BerryEsseen.manuscript_resonance_gap,
  `BerryEsseen.manuscript_resonanceSubgroup_cyclic,
  `BerryEsseen.manuscript_lattice_span_dichotomy,
  `BerryEsseen.manuscript_exists_span_and_resonance_multiplier,
  `BerryEsseen.manuscript_nonresonant_cutoff,
  `BerryEsseen.manuscript_finite_resonances,
  `BerryEsseen.manuscript_resonance_partition_exists,
  `BerryEsseen.ManuscriptResonancePartition.integral_decomposition,
  `BerryEsseen.ManuscriptResonancePartition.cells_disjoint,
  `BerryEsseen.ManuscriptResonancePartition.remainder_compact,
  `BerryEsseen.ManuscriptResonancePartition.remainder_nonresonant,
  `MeasureTheory.integral_biUnion_finset,
  `BerryEsseen.actual_moving_resonance_envelopes_on,
  `BerryEsseen.actual_resonance_integral_tendsto_zero_on,
  `BerryEsseen.compact_characteristic_spectral_gap,
  `BerryEsseen.manuscript_low_resonance_isolation,
  `BerryEsseen.manuscript_raw_low_frequency_shrink,
  `BerryEsseen.manuscript_low_annulus_integral_decomposition,
  `BerryEsseen.manuscript_separated_resonance_partition_exists,
  `BerryEsseen.ManuscriptSeparatedResonancePartition.cells_disjoint_low,
  `BerryEsseen.ManuscriptSeparatedResonancePartition.cells_subset_annulus,
  `BerryEsseen.ManuscriptSeparatedResonancePartition.integral_decomposition,
  `BerryEsseen.manuscript_separated_rawFourier_integral_tendsto_zero,
  `BerryEsseen.manuscript_separated_rawJitterFourierError_away_tendsto_zero,
  `BerryEsseen.manuscript_signed_smoothing_sup,
  `BerryEsseen.manuscript_signed_smoothing_convolution_bound,
  `BerryEsseen.manuscriptCDFConvolution_bound_of_direct_inversion,
  `BerryEsseen.manuscriptCDFConvolution_direct_inversion_of_quotient,
  `BerryEsseen.manuscriptCDFConvolution_fourier_integrable_of_quotient,
  `BerryEsseen.manuscriptCDFConvolution_fourier_support,
  `BerryEsseen.manuscriptCDFConvolution_fourier_product,
  `BerryEsseen.manuscriptCDFConvolution_continuous,
  `BerryEsseen.manuscriptCDFConvolution_integrable,
  `BerryEsseen.manuscript_densityFourier_convolution,
  `BerryEsseen.manuscript_angular_fourier_convolution,
  `BerryEsseen.manuscriptScaledSmoothingKernel_fourier,
  `BerryEsseen.manuscript_densityFourier_inversion,
  `BerryEsseen.manuscriptAngularFourier_inversion,
  `BerryEsseen.manuscript_signed_cdf_difference_integrable,
  `BerryEsseen.signedSmoothing_fourier_integrable,
  `BerryEsseen.manuscript_signed_cdf_difference_fourier_from_weak_derivative,
  `BerryEsseen.manuscript_cdf_difference_fourier_from_weak_derivative,
  `BerryEsseen.manuscript_fourier_from_bounded_test_derivative,
  `BerryEsseen.manuscript_cdf_difference_bounded_test_derivative,
  `BerryEsseen.manuscript_primitive_test_derivative,
  `BerryEsseen.manuscript_step_test_derivative,
  `BerryEsseen.realPhase_hasDerivAt,
  `BerryEsseen.manuscript_four_uniform_density_angular,
  `BerryEsseen.manuscript_four_uniforms_density,
  `BerryEsseen.manuscript_four_uniforms_charFun,
  `BerryEsseen.manuscript_two_uniforms_density,
  `BerryEsseen.manuscript_two_triangle_density,
  `BerryEsseen.manuscriptUniformWeight_lconvolution,
  `BerryEsseen.manuscript_uniform_overlap,
  -- Full C_n limit and direct selection of C_n - cE, followed by the
  -- shared extraction steps. The historical extraction wrappers are forbidden.
  `BerryEsseen.manuscript_fixed_esseen_sup_le_extremalConstant,
  `BerryEsseen.manuscript_extremalConstant_tendsto,
  `BerryEsseen.original_manuscript_esseen_constant_tendsto,
  `BerryEsseen.PublishedEsseenFixedLawAsymptotic.limit,
  `BerryEsseen.manuscript_extremal_harmonic_selection,
  `BerryEsseen.manuscript_bounded_extremizing_sequence,
  `BerryEsseen.bounded_extremizing_sequence_of_selection,
  `BerryEsseen.manuscript_bounded_extremizing_sequence_of_not_main,
  `BerryEsseen.identified_extremizing_sequence_of_bounded,
  `BerryEsseen.manuscript_identified_extremizing_sequence_of_not_main,
  `BerryEsseen.exists_selectedExtremizers_of_identified,
  `BerryEsseen.manuscript_exists_selectedExtremizers_of_not_main,
  -- The actual Holder integral and both displayed interpolation steps.
  `BerryEsseen.CenteredFourthLaw.absoluteMoment_lower_exact,
  `BerryEsseen.CenteredFourthLaw.absoluteMoment_interpolation_chain,
  `BerryEsseen.CenteredFourthLaw.absoluteMoment_lower_holder,
  `BerryEsseen.CenteredFourthLaw.fourthMoment_pos_of_secondMoment_pos,
  `BerryEsseen.CenteredFourthLaw.holder_moment_interpolation,
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg,

  `BerryEsseen.manuscript_charFun_power_decay_from_log,
  `BerryEsseen.manuscript_compact_square_from_wassersteinThree,
  `BerryEsseen.manuscript_compact_curvature_from_wassersteinThree,
  `BerryEsseen.manuscript_square_tail_tendsto,
  `BerryEsseen.manuscript_principal_log_remainder,
  `BerryEsseen.manuscript_scaled_log_remainder,
  `BerryEsseen.manuscript_charFun_power_from_principal_log,
  `BerryEsseen.manuscript_cubic_coupling_costs_tendsto,
  `BerryEsseen.manuscript_double_coupling_error_bound,
  `BerryEsseen.manuscript_double_coupling_square_difference_bound,
  `BerryEsseen.manuscript_general_integer_window_geometry,
  `BerryEsseen.manuscript_general_window_endpoint,
  `BerryEsseen.manuscript_general_noise_variance_window,
  `BerryEsseen.manuscript_general_noise_open_interval,
  `BerryEsseen.manuscript_general_noise_open_budget,
  `BerryEsseen.manuscript_general_noise_block_window,
  `BerryEsseen.compact_twoCluster_local_jitter_gaps_from_binomial,
  `BerryEsseen.extremizer_support_subset_ten,
  `BerryEsseen.reflected_esseen_envelope_shape,
  `BerryEsseen.negative_edgeworth_envelope_hasDerivAt,
  `BerryEsseen.negative_edgeworth_envelope_strictAntiOn,
  `BerryEsseen.manuscript_contact_first_order,
  `BerryEsseen.manuscript_normal_first_order,
  `BerryEsseen.manuscript_contact_saturation_error,

  `BerryEsseen.manuscript_signed_smoothing,
  `BerryEsseen.manuscriptSmoothingKernel_integral,
  `BerryEsseen.manuscriptSmoothingKernel_fourier_zero,
  `BerryEsseen.manuscript_harmonic_selection,
  `BerryEsseen.manuscript_one_sided_loss,
  `BerryEsseen.manuscript_small_cluster_variance_original_parameters,
  `BerryEsseen.manuscript_original_parameters_uniform_gap,
  `BerryEsseen.manuscript_twoCluster_outside_uniform_error,
  `BerryEsseen.manuscript_two_interval_cluster_stability]

def forbidden : Array Name := #[
  `BerryEsseen.resonance_gap,
  `BerryEsseen.resonanceSubgroup_cyclic,
  `BerryEsseen.resonanceSubgroup_nonnegative_generator,
  `BerryEsseen.lattice_span_dichotomy,
  `BerryEsseen.exists_span_and_resonance_multiplier,
  `BerryEsseen.standardized_support_nontrivial,
  `BerryEsseen.actual_moving_resonance_envelopes,
  `BerryEsseen.actual_resonance_integral_tendsto_zero,
  `BerryEsseen.manuscript_signed_convolution_bound_of_kernel_inversion,
  `BerryEsseen.manuscript_convolution_fourier_of_kernel_inversion,
  `BerryEsseen.manuscript_scaled_kernel_inversion,
  `BerryEsseen.manuscriptSmoothingKernel_inversion,
  `BerryEsseen.manuscript_signed_cdf_difference_fourier,
  `BerryEsseen.manuscript_cdf_difference_fourier,
  `BerryEsseen.manuscript_primitive_difference_fourier,
  `BerryEsseen.manuscriptStepDifference_fourier,
  `BerryEsseen.manuscriptTriangle_fourier,
  `BerryEsseen.extremal_harmonic_selection,
  `BerryEsseen.extremal_harmonic_selection_of_not_main,
  `BerryEsseen.positive_excess_drop,
  `BerryEsseen.bounded_extremizing_sequence,
  `BerryEsseen.bounded_extremizing_sequence_of_not_main,
  `BerryEsseen.identified_extremizing_sequence_of_not_main,
  `BerryEsseen.exists_selectedExtremizers_of_not_main,
  -- This declaration was deleted. Construct its hierarchical name without
  -- requiring it to resolve in the current environment.
  Name.str (Name.str Name.anonymous "BerryEsseen") "scalar_moment_interpolation",

  `BerryEsseen.charFun_general_low_frequency_decay,
  `BerryEsseen.charFun_general_cubic_exponential_bound,
  `BerryEsseen.weak_characteristicSquareCurvature_tendsto,
  `BerryEsseen.noise_block_window_mass_lower,
  `BerryEsseen.noise_variance_central_half_double,
  `BerryEsseen.central_integer_window_geometry,
  `BerryEsseen.contactCorrection_tendsto,

  `BerryEsseen.manuscript_small_variance_bad_sequence_impossible,
  `BerryEsseen.manuscript_small_variance_uniform_gap,
  `BerryEsseen.manuscript_small_cluster_variance,
  `BerryEsseen.main_theorem,
  `BerryEsseen.represented_selected_extremizers_impossible,
  `BerryEsseen.standardized_two_cluster_stability,
  `BerryEsseen.harmonic_selection,
  `BerryEsseen.exists_small_scaledDrop,
  `BerryEsseen.finite_selection,
  `BerryEsseen.one_sided_loss,
  `BerryEsseen.one_sided_loss_upper_of_value,
  `BerryEsseen.small_variance_central_sequence,
  `BerryEsseen.small_cluster_variance,
  `BerryEsseen.effective_small_variance,
  `BerryEsseen.effective_small_variance_positive,
  `BerryEsseen.effective_small_variance_raw,
  `BerryEsseen.effective_cluster_stability,
  `BerryEsseen.effective_interval_stability,
  `BerryEsseen.effective_interval_stability_support,
  `BerryEsseen.two_interval_cluster_stability]

def report (root : Name) (t : Traversal) (mode : String) : Json := Json.mkObj [
  ("mode", toJson mode),
  ("target", toJson root.toString),
  ("visited_count", toJson t.order.size),
  ("missing_kernel_declarations", toJson (t.missing.map Name.toString)),
  ("required", toJson (required.map (checkpoint root t))),
  ("forbidden_found", toJson ((forbidden.filter t.visited.contains).map (checkpoint root t))),
  ("project_dependencies", toJson (((t.order.filter isProject).qsort Name.lt).map Name.toString)),
  ("project_paths", Json.mkObj (((t.order.filter isProject).qsort Name.lt).toList.map
    (fun n => (n.toString, toJson ((pathTo root t n).map Name.toString))))) ]

end StrictProofAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := ``BerryEsseen.strict_main_theorem
  unless (env.checked.get.find? target).isSome do
    throwError "The manuscript main theorem is absent from the checked kernel environment."
  let proof := StrictProofAudit.traverse env target false
  let full := StrictProofAudit.traverse env target true
  let payload := Json.mkObj [
    ("proof_values", StrictProofAudit.report target proof "transitive theorem/definition values"),
    ("values_and_types", StrictProofAudit.report target full "transitive values plus declaration types")]
  logInfo m!"STRICT_PROOF_AUDIT_JSON: {payload.compress}"

#check (BerryEsseen.strict_main_theorem : BerryEsseen.ClassicalBerryEsseenBounds →
  BerryEsseen.PublishedEsseenFixedLawAsymptotic →
  BerryEsseen.PublishedEsseenMoment →
  BerryEsseen.PublishedBernoulliBound → BerryEsseen.PublishedNonIIDBound →
  BerryEsseen.PublishedWassersteinThreeTopology → BerryEsseen.MainClaim)
#print axioms BerryEsseen.strict_main_theorem
