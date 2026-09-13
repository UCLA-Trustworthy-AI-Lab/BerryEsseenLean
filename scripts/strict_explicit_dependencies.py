#!/usr/bin/env python3
"""Run the checked-proof dependency audit and map actual dependencies to sources.

This deliberately does not infer proof dependencies from imports. It preserves
the JSON emitted by Checks/StrictExplicitAudit.lean, which traverses actual kernel expressions.
Set BERRY_ESSEEN_LAKE and any platform runtime compatibility variables externally.
This command does not rebuild the project: run lake build beforehand after edits.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from compile_strict import digest, has_sorry_diagnostic, pinned_environment

root = Path(__file__).resolve().parents[1]
lake = os.environ.get("BERRY_ESSEEN_LAKE") or shutil.which("lake")
if not lake:
    raise SystemExit("Set BERRY_ESSEEN_LAKE or put the pinned lake executable on PATH")
out_dir = root / "validation"
out_dir.mkdir(exist_ok=True)
environment = pinned_environment(root, lake)
audit_hash = digest(root / "Checks/StrictExplicitAudit.lean")
initial_hashes = {str(path.relative_to(root)): digest(path)
                  for path in sorted((root / "BerryEsseen").glob("*.lean"))}
result = subprocess.run([lake, "env", "lean", "Checks/StrictExplicitAudit.lean"], cwd=root,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(out_dir / "strict-explicit-dependencies.log").write_text(result.stdout)
if result.returncode or has_sorry_diagnostic(result.stdout):
    print(result.stdout)
    raise SystemExit(result.returncode or 2)
marker = "STRICT_EXPLICIT_PROOF_AUDIT_JSON: "
start = result.stdout.find(marker)
if start < 0:
    raise SystemExit("No proof-audit JSON was emitted")
payload, _ = json.JSONDecoder().raw_decode(result.stdout[start + len(marker):])
axiom_match = re.search(r"'BerryEsseen\.manuscript_explicit_theorem' depends on axioms: \[([^\]]*)\]",
                        result.stdout)
if not axiom_match:
    raise SystemExit("Missing exact explicit-theorem axiom output")
target_axioms = sorted(x.strip() for x in axiom_match.group(1).split(",") if x.strip())
unexpected_axioms = sorted(set(target_axioms) - {"propext", "Classical.choice", "Quot.sound"})
declarations = {}
source_hashes = {}
for path in sorted((root / "BerryEsseen").glob("*.lean")):
    source_hashes[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    for name in re.findall(r"^(?:theorem|lemma|instance|def|structure|class|abbrev)\s+([\w'.]+)",
                           path.read_text(), re.M):
        declarations[f"BerryEsseen.{name}"] = str(path.relative_to(root))
for report in (payload["proof_values"], payload["values_and_types"]):
    report["declaration_sources"] = {
        name: declarations.get(name) for name in report["project_dependencies"]
    }
    report["effective_module_dependencies_for_review"] = [
        {"name": name, "source": declarations[name], "path": report["project_paths"][name]}
        for name in report["project_dependencies"]
        if name in declarations and Path(declarations[name]).name.startswith("Effective")
    ]
    report["required_all_present"] = all(row["present"] for row in report["required"])
    report["forbidden_all_absent"] = not report["forbidden_found"]
payload["source_sha256"] = source_hashes
if source_hashes != initial_hashes or digest(root / "Checks/StrictExplicitAudit.lean") != audit_hash:
    raise SystemExit("Sources changed during the dependency audit")
payload["audit_lean_sha256"] = audit_hash
payload["build_environment"] = environment
payload["audit_python_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
payload["lean_toolchain"] = (root / "lean-toolchain").read_text().strip()
payload["exact_type_check"] = "ClassicalBerryEsseenBounds -> PublishedEsseenMoment -> PublishedBernoulliBound -> PublishedNonIIDBound -> PublishedNonuniformBound -> PublishedWassersteinDuality -> ExplicitClaim"
payload["scope"] = "Current checked proof expressions; existing imports/caches, no clean rebuild by this script"
payload["target_axioms"] = target_axioms
payload["unexpected_axioms"] = unexpected_axioms
json_path = out_dir / "strict-explicit-dependencies.json"
json_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
gate = payload["proof_values"]
groups = {}
for row in gate["effective_module_dependencies_for_review"]:
    groups.setdefault(row["source"], []).append(row["name"])
review_lines = [
    "# Explicit theorem: checked proof dependencies", "",
    "Target: `BerryEsseen.manuscript_explicit_theorem`.", "",
    f"The proof-value traversal visited {gate['visited_count']:,} checked declarations, "
    f"including {len(gate['project_dependencies']):,} project declarations. "
    f"All {len(gate['required'])} required manuscript checkpoints are present: "
    f"{gate['required_all_present']}. No forbidden replaced endpoint is present: "
    f"{gate['forbidden_all_absent']}.", "",
    "The audit inspects the kernel declaration's type directly, before application "
    "elaboration could infer implicit arguments. It contains exactly six independent "
    "explicit premise binders and the result `ExplicitClaim`:", "",
    *[f"- `{name}`" for name in payload["kernel_type_check"]["external_premises"]], "",
    "There is no external smoothing premise or additional jitter, local-mass, "
    "stability, or confinement premise. Internally parameterized lemmas are supplied "
    "with actual proofs in this final theorem.", "",
    "Kernel axioms: " + ", ".join(f"`{name}`" for name in target_axioms) + ". "
    "These kernel axioms are separate from the six explicitly listed mathematical "
    "premises; an axiom printout alone would not audit those premises.", "",
    "## What the required checkpoints establish", "",
    "The actual proof values pass through the proved sinc-fourth-power smoothing "
    "kernel, the actual Holder integral with exponents 3/2 and 3 and both "
    "displayed moment-interpolation inequalities, the manuscript's 100 Gaussian "
    "and 2000 contact remainders, the exact "
    "local-mass route, both original binomial cutoffs, the clipping proof and original "
    "small-variance budgets (50, 100, 176000, and leakage coefficient 40), the original "
    "large-variance envelope budgets, and the affine Wasserstein equality and "
    "two-point collapse used for confinement. Full witness paths are recorded in "
    "`strict-explicit-dependencies.json`.", "",
    "## Retained earlier source modules", "",
    f"{len(gate['effective_module_dependencies_for_review'])} actual dependencies "
    "come from files beginning `Effective`. The filename prefix alone does not "
    "show that a replaced argument is still used. The gate excludes the particular "
    "old endpoints listed in `Checks/StrictExplicitAudit.lean`.", "",
    "Some retained dependencies are elementary definitions, moment identities, "
    "coordinate changes, or scalar estimates. Others implement substantial "
    "previously formalized global Fourier, near-lattice, rounding, identification, "
    "support, and finite-selection arguments. They must not all be described as "
    "mere definitions. This audit verifies the specified replacements and the "
    "exact final premise interface; it does not by itself establish line-by-line "
    "manuscript fidelity for every retained analytical lemma.", "",
    "The retained binomial jitter theorem is used with the new proved smoothing "
    "instance and the original cutoffs supplied by the required manuscript wrappers. "
    "The retained small-variance far-threshold coordinate estimate is the appendix's "
    "geometric conversion needed for its published nonuniform bound; the replaced "
    "old central/absorption/small-variance conclusions are absent.", "",
    "| Retained source | Actual declarations |", "| --- | ---: |",
    *[f"| `{source}` | {len(names)} |" for source, names in sorted(groups.items())], "",
    "## Reproduction scope", "",
    "The Python command invokes Lean on the audit and inspects checked imported "
    "declarations. It does not perform a clean project build. Run the project build "
    "after changes, then rerun `scripts/strict_explicit_dependencies.py`. The report "
    "records current source hashes and audit hashes; the complete Lean output is "
    "in `strict-explicit-dependencies.log`.", "",
]
(out_dir / "strict-explicit-dependency-review.md").write_text("\n".join(review_lines))
for key in ("proof_values", "values_and_types"):
    report = payload[key]
    print(json.dumps({"mode": key, "visited": report["visited_count"],
                      "project_declarations": len(report["project_dependencies"]),
                      "required": [{"name": x["name"], "present": x["present"]} for x in report["required"]],
                      "forbidden_found": report["forbidden_found"],
                      "effective_module_declarations_for_review": len(report["effective_module_dependencies_for_review"])},
                     ensure_ascii=False))
print(f"Saved {json_path.relative_to(root)}")
# An actual forbidden endpoint or missing required proof segment is a failed gate.
gate = payload["proof_values"]
sys.exit(0 if gate["required_all_present"] and gate["forbidden_all_absent"] and
         not gate["missing_kernel_declarations"] and not unexpected_axioms and
         payload["kernel_type_check"]["passed"] else 2)
