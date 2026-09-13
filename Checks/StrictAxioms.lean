import BerryEsseen
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc name info =>
    if name.toString.startsWith "BerryEsseen." ||
        name.toString.startsWith "_private.BerryEsseen." then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => acc.push name
      | _ => acc
    else acc
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Project declaration is absent from the checked kernel: {name}"
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := state.axioms.filter fun name => !allowed.contains name
  let report := Json.mkObj [
    ("project_declarations", toJson names.size),
    ("axioms", toJson ((state.axioms.qsort Name.lt).map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString))]
  logInfo m!"STRICT_ALL_AXIOMS_JSON: {report.compress}"
  unless unexpected.isEmpty do
    throwError "Unexpected project axiom dependencies: {unexpected}"

#check (BerryEsseen.strict_main_theorem : BerryEsseen.ClassicalBerryEsseenBounds →
  BerryEsseen.PublishedEsseenFixedLawAsymptotic →
  BerryEsseen.PublishedEsseenMoment → BerryEsseen.PublishedBernoulliBound →
  BerryEsseen.PublishedNonIIDBound → BerryEsseen.PublishedWassersteinThreeTopology →
  BerryEsseen.MainClaim)
#check (BerryEsseen.strict_explicit_theorem : BerryEsseen.ClassicalBerryEsseenBounds →
  BerryEsseen.PublishedEsseenMoment → BerryEsseen.PublishedBernoulliBound →
  BerryEsseen.PublishedNonIIDBound → BerryEsseen.PublishedNonuniformBound →
  BerryEsseen.PublishedWassersteinDuality → BerryEsseen.ExplicitClaim)
#check (BerryEsseen.strict_sharpness : BerryEsseen.PublishedEsseenFixedLawAsymptotic →
  BerryEsseen.ManuscriptSharpnessClaim)
