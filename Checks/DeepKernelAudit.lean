import BerryEsseen
import Lean

/-! Read-only exact kernel-interface audit of the three delivered final results.
This file is diagnostic; it contributes no mathematical theorem. -/
namespace DeepKernelAudit
open Lean

def targets : Array (Name × Array Name × Name) := #[
  (`BerryEsseen.strict_main_theorem,
    #[`BerryEsseen.ClassicalBerryEsseenBounds,
      `BerryEsseen.PublishedEsseenFixedLawAsymptotic, `BerryEsseen.PublishedEsseenMoment,
      `BerryEsseen.PublishedBernoulliBound, `BerryEsseen.PublishedNonIIDBound,
      `BerryEsseen.PublishedWassersteinThreeTopology],
    `BerryEsseen.MainClaim),
  (`BerryEsseen.strict_explicit_theorem,
    #[`BerryEsseen.ClassicalBerryEsseenBounds, `BerryEsseen.PublishedEsseenMoment,
      `BerryEsseen.PublishedBernoulliBound, `BerryEsseen.PublishedNonIIDBound,
      `BerryEsseen.PublishedNonuniformBound, `BerryEsseen.PublishedWassersteinDuality],
    `BerryEsseen.ExplicitClaim),
  (`BerryEsseen.strict_sharpness,
    #[`BerryEsseen.PublishedEsseenFixedLawAsymptotic],
    `BerryEsseen.ManuscriptSharpnessClaim)]

def inspect (ty : Expr) (premises : Array Name) (result : Name) : Except String Unit := do
  let mut curr := ty.consumeMData
  for name in premises do
    let .forallE _ domain body binderInfo := curr |
      throw s!"Missing premise: {name}"
    unless binderInfo == .default do
      throw "Unexpected implicit or instance binder"
    unless domain.consumeMData == mkConst name do
      throw s!"Unexpected premise type, expected {name}, got {domain}"
    if body.hasLooseBVars then
      throw "The conclusion unexpectedly depends on the premise proof object"
    curr := body.consumeMData
  unless curr == mkConst result do
    throw s!"Unexpected extra premise or conclusion: {curr}"
end DeepKernelAudit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (target, premises, result) in DeepKernelAudit.targets do
    let some info := env.checked.get.find? target |
      throwError "Missing checked kernel declaration: {target}"
    match DeepKernelAudit.inspect info.type premises result with
    | .error message => throwError "{target}: {message}"
    | .ok _ => pure ()
    rows := rows.push (Json.mkObj [
      ("target", toJson target.toString),
      ("premises", toJson (premises.map Name.toString)),
      ("result", toJson result.toString),
      ("passed", toJson true)])
  logInfo m!"DEEP_KERNEL_TYPES_JSON: {(toJson rows).compress}"

#print BerryEsseen.ClassicalBerryEsseenBounds
#print BerryEsseen.PublishedEsseenMoment
#print BerryEsseen.PublishedBernoulliBound
#print BerryEsseen.PublishedNonIIDBound
#print BerryEsseen.PublishedNonuniformBound
#print BerryEsseen.PublishedWassersteinDuality
#print BerryEsseen.PublishedEsseenFixedLawAsymptotic
#print BerryEsseen.PublishedWassersteinThreeTopology
#print BerryEsseen.MainClaim
#print BerryEsseen.ExplicitClaim
#print BerryEsseen.ManuscriptSharpnessClaim
#print BerryEsseen.BoundAt
#print BerryEsseen.StandardizedLaw
#print BerryEsseen.discrepancy
#print BerryEsseen.cE
#print BerryEsseen.explicitThreshold
-- These applications explicitly discharge the paper's smoothing lemma.
#check (BerryEsseen.general_signed_smoothing_sup BerryEsseen.manuscriptSignedSmoothing)
#check (fun W : BerryEsseen.PublishedWassersteinThreeTopology =>
  BerryEsseen.maximal_span_wassersteinThree_jitter_expansion W BerryEsseen.manuscriptSignedSmoothing)
#check (fun W : BerryEsseen.PublishedWassersteinThreeTopology =>
  BerryEsseen.raw_wassersteinThree_variable_jitter_expansion_at_raw W BerryEsseen.manuscriptSignedSmoothing)
#check (fun W : BerryEsseen.PublishedWassersteinThreeTopology =>
  BerryEsseen.wassersteinThree_jitter_limsup W BerryEsseen.manuscriptSignedSmoothing)
#check (fun W : BerryEsseen.PublishedWassersteinThreeTopology =>
  BerryEsseen.compact_centered_measure_local_mass W BerryEsseen.manuscriptSignedSmoothing)
