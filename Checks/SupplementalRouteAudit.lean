import BerryEsseen
import Lean

/-! Actual proof-value traversal for original endpoints beyond the three final results.
This machine check supplements the human source-to-manuscript review. -/
namespace SupplementalRouteAudit
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

def cases : Array (String × Name × Array Name × Array Name) := #[
  ("general jitter: original log and independent-difference coupling",
    `BerryEsseen.maximal_span_wassersteinThree_jitter_expansion,
    #[`BerryEsseen.manuscript_characteristicSquareCurvature_zero,
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
      `BerryEsseen.manuscript_principal_log_remainder,
      `BerryEsseen.manuscript_charFun_power_from_principal_log,
      `BerryEsseen.manuscript_charFun_power_decay_from_log,
      `BerryEsseen.manuscript_compact_square_from_wassersteinThree,
      `BerryEsseen.manuscript_compact_curvature_from_wassersteinThree,
      `BerryEsseen.manuscript_cubic_coupling_costs_tendsto,
      `BerryEsseen.manuscript_double_coupling_error_bound,
      `BerryEsseen.manuscript_double_coupling_square_difference_bound],
    #[`BerryEsseen.resonance_gap,
      `BerryEsseen.resonanceSubgroup_cyclic,
      `BerryEsseen.resonanceSubgroup_nonnegative_generator,
      `BerryEsseen.lattice_span_dichotomy,
      `BerryEsseen.exists_span_and_resonance_multiplier,
      `BerryEsseen.standardized_support_nontrivial,
      `BerryEsseen.actual_moving_resonance_envelopes,
      `BerryEsseen.actual_resonance_integral_tendsto_zero,
      `BerryEsseen.compact_rawFourier_integral_tendsto_zero]),
  ("general support wrapper: original body compactness",
    `BerryEsseen.selected_extremizer_compact_tail,
    #[`BerryEsseen.extremizer_support_subset_ten], #[]),
  ("binomial estimates: actual Fourier inversion and all six conjuncts",
    `BerryEsseen.manuscript_binomial_estimates,
    #[`BerryEsseen.manuscript_binomial_inversion,
      `BerryEsseen.manuscript_principal_log_remainder], #[])]
end SupplementalRouteAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (label, target, required, forbidden) in SupplementalRouteAudit.cases do
    unless (env.checked.get.find? target).isSome do
      throwError "Missing checked original endpoint: {target}"
    let proof := SupplementalRouteAudit.traverse env target false
    let req := required.map (SupplementalRouteAudit.checkpoint target proof)
    let bad := forbidden.filter proof.visited.contains
    rows := rows.push (Json.mkObj [
      ("case", toJson label), ("target", toJson target.toString),
      ("required", toJson req), ("forbidden_found", toJson (bad.map Name.toString)),
      ("missing_kernel_declarations", toJson (proof.missing.map Name.toString))])
    unless (required.all proof.visited.contains) && bad.isEmpty && proof.missing.isEmpty do
      logInfo m!"SUPPLEMENTAL_ROUTE_AUDIT_JSON: {(toJson rows).compress}"
      throwError "Original route dependency check failed: {label}"
  logInfo m!"SUPPLEMENTAL_ROUTE_AUDIT_JSON: {(toJson rows).compress}"
