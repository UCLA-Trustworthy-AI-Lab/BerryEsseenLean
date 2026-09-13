#!/usr/bin/env python3
"""Run the checked-proof dependency audit and map actual dependencies to sources.

This deliberately does not infer proof dependencies from imports. It preserves
the JSON emitted by Checks/StrictAudit.lean, which traverses actual kernel expressions.
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
audit_hash = digest(root / "Checks/StrictAudit.lean")
initial_hashes = {str(path.relative_to(root)): digest(path)
                  for path in sorted((root / "BerryEsseen").glob("*.lean"))}
result = subprocess.run([lake, "env", "lean", "Checks/StrictAudit.lean"], cwd=root,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
(out_dir / "strict-dependencies.log").write_text(result.stdout)
if result.returncode or has_sorry_diagnostic(result.stdout):
    print(result.stdout)
    raise SystemExit(result.returncode or 2)
marker = "STRICT_PROOF_AUDIT_JSON: "
start = result.stdout.find(marker)
if start < 0:
    raise SystemExit("No proof-audit JSON was emitted")
payload, _ = json.JSONDecoder().raw_decode(result.stdout[start + len(marker):])
axiom_match = re.search(r"'BerryEsseen\.strict_main_theorem' depends on axioms: \[([^\]]*)\]",
                        result.stdout)
if not axiom_match:
    raise SystemExit("Missing exact main-theorem axiom output")
target_axioms = sorted(x.strip() for x in axiom_match.group(1).split(",") if x.strip())
unexpected_axioms = sorted(set(target_axioms) - {"propext", "Classical.choice", "Quot.sound"})
declarations = {}
source_hashes = {}
for path in sorted((root / "BerryEsseen").glob("*.lean")):
    source_hashes[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    for name in re.findall(r"^(?:theorem|lemma|instance|def|structure|class|abbrev)\s+([\w'.]+)",
                           path.read_text(), re.M):
        declarations[f"BerryEsseen.{name}"] = str(path.relative_to(root))
for report in payload.values():
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
if source_hashes != initial_hashes or digest(root / "Checks/StrictAudit.lean") != audit_hash:
    raise SystemExit("Sources changed during the dependency audit")
payload["audit_lean_sha256"] = audit_hash
payload["audit_python_sha256"] = digest(Path(__file__))
payload["build_environment"] = environment
payload["exact_type_check"] = "ClassicalBerryEsseenBounds -> PublishedEsseenFixedLawAsymptotic -> PublishedEsseenMoment -> PublishedBernoulliBound -> PublishedNonIIDBound -> PublishedWassersteinThreeTopology -> MainClaim"
payload["scope"] = "Current checked proof expressions; existing imports/caches, no clean rebuild by this script"
payload["target_axioms"] = target_axioms
payload["unexpected_axioms"] = unexpected_axioms
json_path = out_dir / "strict-dependencies.json"
json_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
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
         not gate["missing_kernel_declarations"] and not unexpected_axioms else 2)
