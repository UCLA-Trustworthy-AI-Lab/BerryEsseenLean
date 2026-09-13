import BerryEsseen.ManuscriptExplicitTheorem
import Lean

/-!
This is a proof-expression dependency audit, not an import audit. It starts
from the checked kernel declaration of the new manuscript explicit theorem and
recursively reads the actual values of theorems, definitions, and opaque
declarations. It records witness paths to required and forbidden endpoints.
It is diagnostic metaprogramming and does not contribute a mathematical proof.
-/

namespace StrictExplicitProofAudit
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
  `BerryEsseen.effective_cluster_frequency_partition,
  `BerryEsseen.effective_cluster_frequency_partition_aeDisjoint,
  `BerryEsseen.effective_cluster_frequency_integral_partition,
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
  -- The actual Holder integral and both displayed interpolation steps.
  `BerryEsseen.CenteredFourthLaw.absoluteMoment_lower_exact,
  `BerryEsseen.CenteredFourthLaw.absoluteMoment_interpolation_chain,
  `BerryEsseen.CenteredFourthLaw.absoluteMoment_lower_holder,
  `BerryEsseen.CenteredFourthLaw.fourthMoment_pos_of_secondMoment_pos,
  `BerryEsseen.CenteredFourthLaw.holder_moment_interpolation,
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg,

  `BerryEsseen.effective_identification_with_global_jitter,
  `BerryEsseen.effective_lattice_identification_transfer,
  `BerryEsseen.manuscript_cayley_connected,
  `BerryEsseen.manuscript_finite_bezout_four_thousand,
  `BerryEsseen.manuscript_lattice_rounding_index_span,
  `BerryEsseen.manuscript_finite_lattice_natural_labels,
  `BerryEsseen.manuscript_finite_cosine_square_identity,
  `BerryEsseen.manuscript_finite_two_atoms_square_gap,
  `BerryEsseen.manuscript_circular_residual_integer_sum,
  `BerryEsseen.manuscript_finite_lattice_spectral_gap,
  `BerryEsseen.manuscript_rounding_error_at_threshold,
  `BerryEsseen.manuscript_global_rounding_frequency_exact,
  `BerryEsseen.manuscript_global_rounding_frequency_strict,
  `BerryEsseen.manuscript_global_original_sample_gap,
  `BerryEsseen.manuscript_global_original_exponential_absorption,
  `BerryEsseen.manuscriptConditionalReplacement_law,
  `BerryEsseen.manuscript_wasserstein_common_source,
  `BerryEsseen.manuscript_difference_coupling_marginals,
  `BerryEsseen.manuscript_difference_coupling_cost,
  `BerryEsseen.manuscript_difference_wasserstein_le_two,
  `BerryEsseen.manuscript_difference_slope_lipschitz,
  `BerryEsseen.manuscript_difference_curvature_lipschitz,
  `BerryEsseen.manuscript_bounded_difference_derivative_transport,
  `BerryEsseen.manuscript_measure_squareThird_bound,
  `BerryEsseen.manuscript_measure_squareThird_sixty,
  `BerryEsseen.manuscript_global_cell_curvature,
  `BerryEsseen.manuscript_characteristic_peak_of_cell_curvature,

  `BerryEsseen.manuscript_centered_coupling_marginals,
  `BerryEsseen.manuscript_centered_coupling_cost,
  `BerryEsseen.manuscript_centering_wasserstein_actual,
  `BerryEsseen.manuscript_centered_transport_two_w,

  `BerryEsseen.manuscriptSizeBiasedProduct_first_identity,
  `BerryEsseen.manuscriptSizeBiasedProduct_second_identity,
  `BerryEsseen.manuscriptSizeBiasedProduct_signed_identity,
  `BerryEsseen.manuscript_lattice_deficit_decomposition,
  `BerryEsseen.manuscript_lattice_large_pairs_deficit,
  `BerryEsseen.manuscript_effective_lattice_translate_avoids_zero,
  `BerryEsseen.manuscript_outside_pair_comparison,
  `BerryEsseen.manuscript_lattice_outside_second_bound,
  `BerryEsseen.manuscript_lattice_bracket_atoms_positive,
  `BerryEsseen.manuscript_bracket_atoms_force_maximal_span,
  `BerryEsseen.manuscript_cube_centering_mvt,
  `BerryEsseen.bounded_cubic_centering_errors,
  `BerryEsseen.manuscript_lattice_centering_quadratic_budget,
  `BerryEsseen.bounded_lattice_centered_deficit,
  `BerryEsseen.manuscript_lattice_parameter_error_exact,
  `BerryEsseen.manuscript_bernoulli_span_hasDerivAt,
  `BerryEsseen.manuscript_bernoulli_span_derivative_bound,
  `BerryEsseen.manuscript_lattice_span_error_budget,
  `BerryEsseen.manuscript_wasserstein_conditioning_actual,
  `BerryEsseen.manuscript_wasserstein_affine_standardized_actual,
  `BerryEsseen.manuscript_lattice_affine_transport_budget,
  `BerryEsseen.manuscript_standardizedBernoulli_wasserstein_actual,
  `BerryEsseen.manuscriptUnitUniform_disagreement,
  `BerryEsseen.manuscript_bernoulli_atoms_derivative,
  `BerryEsseen.manuscript_bernoulli_atoms_MVT,
  `BerryEsseen.manuscript_bernoulli_cross_atom_bound,
  `BerryEsseen.manuscript_effective_lattice_wasserstein_budget,
  `BerryEsseen.manuscript_wasserstein_reflected_actual,

  `BerryEsseen.manuscriptDifferenceLaw_fourth,
  `BerryEsseen.manuscriptDifferenceLaw_cos,
  `BerryEsseen.manuscript_effective_difference_fourth,
  `BerryEsseen.manuscript_effective_charFun_square_bound,
  `BerryEsseen.manuscript_cluster_cos_taylor,
  `BerryEsseen.manuscript_cluster_sinWeight_taylor,
  `BerryEsseen.manuscript_cluster_cosSquareWeight_taylor,
  `BerryEsseen.manuscript_cluster_conditional_taylor,
  `BerryEsseen.manuscript_effective_standardized_cluster_moment,
  `BerryEsseen.manuscript_central_gaussian_argument,
  `BerryEsseen.manuscript_central_density_log_bound,
  `BerryEsseen.manuscript_small_variance_scale_ratio,
  `BerryEsseen.manuscript_effective_violation_threshold_four,
  `BerryEsseen.manuscript_gaussian_gap_on_four,
  `BerryEsseen.manuscript_positive_esseen_envelope_quadratic_gap,
  `BerryEsseen.manuscript_esseen_negative_gap_numeric,
  `BerryEsseen.manuscript_esseen_coarse_parameters,
  `BerryEsseen.manuscript_esseen_contact_roots,

  `BerryEsseen.manuscript_signed_smoothing,
  `BerryEsseen.manuscriptSmoothingKernel_integral,
  `BerryEsseen.manuscriptSmoothingKernel_fourier_zero,
  `BerryEsseen.manuscript_gaussianHn_effective_local_remainder,
  `BerryEsseen.manuscript_extremizer_effective_contact_polynomial,
  `BerryEsseen.manuscript_effective_local_mass_pointwise_of_wide,
  `BerryEsseen.manuscript_binomial_jitter_twelve,
  `BerryEsseen.manuscript_binomial_jitter_exp,
  `BerryEsseen.manuscript_binomial_central_of_jitter,
  `BerryEsseen.manuscript_binomial_wide_of_jitter,
  `BerryEsseen.manuscript_effective_small_variance,
  `BerryEsseen.manuscript_effective_small_variance_central_remainder,
  `BerryEsseen.manuscript_effective_perturbed_binomial_branch_bound,
  `BerryEsseen.manuscript_effective_prefactor_error,
  `BerryEsseen.manuscript_effective_cluster_prefactor_bounds,
  `BerryEsseen.manuscript_effective_gaussian_variance_bound,
  `BerryEsseen.manuscript_one_sided_loss,
  `BerryEsseen.manuscriptClip_budgets,
  `BerryEsseen.manuscript_effective_noise_fourth,
  `BerryEsseen.manuscript_effective_noise_absolute_central,
  `BerryEsseen.manuscript_jitter_gap_edgeworth_bound,
  `BerryEsseen.manuscript_effective_cluster_error_budget,
  `BerryEsseen.manuscript_effective_cluster_shift_moment_budget,
  `BerryEsseen.manuscript_cluster_normalized_cubic_errors,
  `BerryEsseen.manuscript_cluster_envelope_comparison,
  `BerryEsseen.manuscript_effective_cluster_envelope_moment,
  `BerryEsseen.manuscript_uniform_block_leakage_bound,
  `BerryEsseen.manuscript_reciprocal_fourth_nat_filter_sum_bound,
  `BerryEsseen.manuscript_affine_wasserstein_eq,
  `BerryEsseen.manuscript_two_interval_mass_via_transport,
  `BerryEsseen.manuscript_confinement_half_eta_mass,
  `BerryEsseen.manuscript_effective_support_anchors,
  `BerryEsseen.manuscript_effective_confinement,
  `BerryEsseen.manuscript_effective_intervals_of_clusters]

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
  -- The old polynomial declaration is absent from the revised project.
  Name.str (Name.str Name.anonymous "BerryEsseen") "scalar_moment_interpolation",

  `BerryEsseen.wassersteinOne_affine_standardized,
  `BerryEsseen.standardizedBernoulli_wasserstein,
  `BerryEsseen.finite_bounded_bezout,
  `BerryEsseen.finite_lattice_nonresonance_gap,
  `BerryEsseen.finite_lattice_appendix_nonresonance_gap,
  `BerryEsseen.finite_lattice_natural_labels,
  `BerryEsseen.two_atoms_characteristic_gap,
  `BerryEsseen.exponential_gap_sample_absorption,
  `BerryEsseen.bounded_characteristic_square_derivative_transport,
  `BerryEsseen.appendix_derivative_transport_budget,
  `BerryEsseen.appendix_rounding_error_decay,
  `BerryEsseen.wassersteinOne_conditioning,

  `BerryEsseen.twoCluster_square_slope_difference,
  `BerryEsseen.twoCluster_square_curvature_difference,
  `BerryEsseen.quantitative_characteristic_peak,
  `BerryEsseen.lattice_deficit_pointwise,

  `BerryEsseen.explicit_theorem,
  `BerryEsseen.explicit_claim_of_effective_confinement,
  `BerryEsseen.effective_confinement,
  `BerryEsseen.effective_confinement_coordinates,
  `BerryEsseen.effective_full_support,
  `BerryEsseen.gaussianHn_effective_local_remainder,
  `BerryEsseen.extremizer_effective_contact_polynomial,
  `BerryEsseen.appendix_contact_polynomial_budget,
  `BerryEsseen.extremizer_effective_contact_flatness,
  `BerryEsseen.extremizer_effective_increment_lower,
  `BerryEsseen.effective_local_mass,
  `BerryEsseen.effective_local_mass_pointwise,
  `BerryEsseen.effective_noise_block_window_mass,
  `BerryEsseen.effective_support_anchors,
  `BerryEsseen.wasserstein_esseen_support_near_atom,
  `BerryEsseen.effective_small_variance,
  `BerryEsseen.effective_small_variance_positive,
  `BerryEsseen.effective_small_variance_positive_pointwise,
  `BerryEsseen.effective_small_variance_central,
  `BerryEsseen.effective_small_variance_absorption,
  `BerryEsseen.effective_central_coefficient_bounds,
  `BerryEsseen.effective_cluster_prefactor_bounds,
  `BerryEsseen.twoCluster_central_normalized_comparison,
  `BerryEsseen.twoCluster_gaussian_central_comparison,
  `BerryEsseen.one_sided_loss,
  `BerryEsseen.one_sided_loss_upper_of_value,
  `BerryEsseen.effective_cluster_stability,
  `BerryEsseen.effective_cluster_large_variance,
  `BerryEsseen.effective_cluster_central_large_variance,
  `BerryEsseen.effective_cluster_local_jitter_gaps,
  `BerryEsseen.effective_cluster_envelope_moment,
  `BerryEsseen.effective_cluster_final_budget,
  `BerryEsseen.effective_interval_standardization,
  `BerryEsseen.effective_interval_stability,
  `BerryEsseen.effective_interval_stability_support,
  `BerryEsseen.two_interval_cluster_stability,
  `BerryEsseen.effective_binomial_endpoint_expansion,
  `BerryEsseen.effective_binomial_endpoint_error,
  `BerryEsseen.effective_binomial_local_error,
  `BerryEsseen.effective_binomial_central,
  `BerryEsseen.effective_binomial_wide,
  `BerryEsseen.effective_binomial_integer_central,
  `BerryEsseen.effective_binomial_integer_wide,
  `BerryEsseen.effective_binomial_branches,
  `BerryEsseen.effective_binomial_constant_lower]

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

def expectedExternalNames : Array Name := #[
  `BerryEsseen.ClassicalBerryEsseenBounds,
  `BerryEsseen.PublishedEsseenMoment,
  `BerryEsseen.PublishedBernoulliBound,
  `BerryEsseen.PublishedNonIIDBound,
  `BerryEsseen.PublishedNonuniformBound,
  `BerryEsseen.PublishedWassersteinDuality]

/-- Inspect the kernel declaration's type directly, before any application can
infer implicit arguments. Exactly six independent external-premise binders
and the actual ExplicitClaim result are permitted. -/
def checkExactExternalType (ty : Expr) : Except String Unit := do
  let mut curr := ty.consumeMData
  for name in expectedExternalNames do
    let .forallE _ domain body binderInfo := curr |
      throw "The explicit theorem has fewer than the six required premise binders."
    unless binderInfo == .default do
      throw "An unexpected implicit or instance premise binder is present."
    unless domain.consumeMData == mkConst name do
      throw s!"Unexpected external premise type; expected {name}, got {domain}."
    if body.hasLooseBVars then
      throw "Unexpected dependency on an external premise inside the remaining theorem type."
    curr := body.consumeMData
  unless curr == mkConst `BerryEsseen.ExplicitClaim do
    throw "Extra premise binders or a different final proposition occur after the six external premises."

end StrictExplicitProofAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let target := ``BerryEsseen.manuscript_explicit_theorem
  unless (env.checked.get.find? target).isSome do
    throwError "The manuscript explicit theorem is absent from the checked kernel environment."
  let info := (env.checked.get.find? target).get!
  match StrictExplicitProofAudit.checkExactExternalType info.type with
  | .error reason => throwError "Explicit theorem interface check failed: {reason}"
  | .ok _ => pure ()
  let proof := StrictExplicitProofAudit.traverse env target false
  let full := StrictExplicitProofAudit.traverse env target true
  let payload := Json.mkObj [
    ("kernel_type_check", Json.mkObj [
      ("passed", toJson true),
      ("external_premises", toJson (StrictExplicitProofAudit.expectedExternalNames.map Name.toString)),
      ("result", toJson "BerryEsseen.ExplicitClaim")]),
    ("proof_values", StrictExplicitProofAudit.report target proof "transitive theorem/definition values"),
    ("values_and_types", StrictExplicitProofAudit.report target full "transitive values plus declaration types")]
  logInfo m!"STRICT_EXPLICIT_PROOF_AUDIT_JSON: {payload.compress}"

-- This exact type assertion excludes an external smoothing interface and all
-- internal jitter, local-mass, stability, or confinement assumptions.
#check (BerryEsseen.manuscript_explicit_theorem : BerryEsseen.ClassicalBerryEsseenBounds →
  BerryEsseen.PublishedEsseenMoment → BerryEsseen.PublishedBernoulliBound →
  BerryEsseen.PublishedNonIIDBound → BerryEsseen.PublishedNonuniformBound →
  BerryEsseen.PublishedWassersteinDuality → BerryEsseen.ExplicitClaim)
#print axioms BerryEsseen.manuscript_explicit_theorem
