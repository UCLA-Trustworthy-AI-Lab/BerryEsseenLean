#!/usr/bin/env python3
"""Elaborate project sources against the pinned Lean/mathlib environment.

This is a compilation gate, not a claim that every manuscript argument is
faithfully represented. Checks/StrictAudit.lean separately checks proof dependencies.
Mathlib's own build/cache must already be available. No sources are modified.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def has_sorry_diagnostic(text: str) -> bool:
    return bool(re.search(r"declaration uses [`']sorry[`']|\bsorryAx\b", text))


def pinned_environment(root: Path, lake: str) -> dict:
    """Validate the running compiler and fingerprint the pinned build inputs."""
    toolchain = (root / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.28.0":
        raise SystemExit("This verification package requires leanprover/lean4:v4.28.0")
    result = subprocess.run([lake, "env", "lean", "--version"], cwd=root,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    match = re.search(r"Lean \(version ([^,\s)]+)", result.stdout)
    if result.returncode or not match or match.group(1) != "4.28.0":
        raise SystemExit("Expected Lean 4.28.0; compiler reported: " + result.stdout.strip())
    inputs = {name: digest(root / name) for name in
              ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}
    data = {"lean_toolchain": toolchain, "lean_version": result.stdout.strip(),
            "configuration_sha256": inputs}
    data["fingerprint_sha256"] = hashlib.sha256(
        json.dumps(data, sort_keys=True).encode()).hexdigest()
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--incremental", action="store_true",
                        help="Reuse only sources/dependency closures certified by an earlier run.")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    root = Path(__file__).resolve().parents[1]
    logs = root / "validation" / "strict-build"
    logs.mkdir(parents=True, exist_ok=True)
    report_path = root / "validation" / "strict-build.json"
    previous_report = {}
    if args.incremental and report_path.exists():
        previous_report = json.loads(report_path.read_text())
    report_path.write_text(json.dumps({"all_project_sources_compiled": False,
                                      "modules": {}}, indent=2) + "\n")
    environment = pinned_environment(root, args.lake)
    previous = (previous_report.get("modules", {}) if
                previous_report.get("build_environment") == environment else {})

    sources = {".".join(p.relative_to(root).with_suffix("").parts): p
               for p in sorted((root / "BerryEsseen").glob("*.lean"))}
    imports = re.compile(r"^\s*(?:(?:public|private)\s+)?import\s+([\w.']+)", re.M)
    deps = {name: {d for d in imports.findall(p.read_text()) if d in sources}
            for name, p in sources.items()}
    hashes = {name: digest(p) for name, p in sources.items()}
    closure_hashes = {}

    def closure_hash(name: str, stack: tuple[str, ...] = ()) -> str:
        if name in closure_hashes:
            return closure_hashes[name]
        if name in stack:
            raise ValueError("Import cycle: " + " -> ".join((*stack, name)))
        payload = hashes[name] + "".join(closure_hash(d, (*stack, name)) for d in sorted(deps[name]))
        closure_hashes[name] = hashlib.sha256(payload.encode()).hexdigest()
        return closure_hashes[name]

    for name in sources:
        closure_hash(name)
    pending, done, running, records = set(sources), set(), {}, {}

    def compile_one(name: str) -> dict:
        src = sources[name]
        out = root / ".lake" / "build" / "lib" / "lean" / Path(*name.split(".")).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        prior = previous.get(name, {})
        if (prior.get("status") in ("compiled", "reused") and
                prior.get("closure_sha256") == closure_hashes[name] and out.exists() and
                prior.get("olean_sha256") == digest(out)):
            return {**prior, "status": "reused"}
        start = time.monotonic()
        log = logs / (name + ".log")
        command = [args.lake, "env", "lean", str(src.relative_to(root)), "-o",
                   str(out.relative_to(root))]
        with log.open("w") as handle:
            proc = subprocess.run(command, cwd=root, env=os.environ.copy(), stdout=handle,
                                  stderr=subprocess.STDOUT, check=False)
        text = log.read_text()
        status = "compiled" if proc.returncode == 0 else "failed"
        if has_sorry_diagnostic(text):
            status = "failed_sorry"
        if digest(src) != hashes[name]:
            status = "source_changed_during_build"
        return {"status": status, "exit_code": proc.returncode,
                "source_sha256": hashes[name], "closure_sha256": closure_hashes[name],
                "olean_sha256": digest(out) if status == "compiled" else None,
                "seconds": round(time.monotonic() - start, 3),
                "log": str(log.relative_to(root))}

    failed = False
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            if not failed:
                ready = sorted(n for n in pending if deps[n] <= done)
                for name in ready[:max(0, args.jobs - len(running))]:
                    pending.remove(name)
                    running[pool.submit(compile_one, name)] = name
            if not running:
                break
            completed, _ = concurrent.futures.wait(running,
                return_when=concurrent.futures.FIRST_COMPLETED)
            for future in completed:
                name = running.pop(future)
                result = future.result()
                records[name] = result
                done.add(name)
                print(f"{result['status']} {name}", flush=True)
                if result["status"] not in ("compiled", "reused"):
                    failed = True
                report_path.write_text(json.dumps({
                    "gate": "project_source_elaboration_only",
                    "all_project_sources_compiled": False,
                    "build_environment": environment,
                    "modules": records,
                }, indent=2) + "\n")
    changed_sources = sorted(name for name, path in sources.items()
                             if not path.exists() or digest(path) != hashes[name])
    current_sources = {".".join(p.relative_to(root).with_suffix("").parts)
                       for p in (root / "BerryEsseen").glob("*.lean")}
    added_sources = sorted(current_sources - sources.keys())
    configuration_changed = any(digest(root / name) != value for name, value in
                                environment["configuration_sha256"].items())
    ok = (not failed and not pending and len(records) == len(sources)
          and not changed_sources and not added_sources and not configuration_changed)
    report_path.write_text(json.dumps({
        "gate": "project_source_elaboration_only",
        "all_project_sources_compiled": ok,
        "build_environment": environment,
        "configuration_changed_during_run": configuration_changed,
        "module_count": len(sources), "modules": records,
        "uncompiled_modules": sorted(pending),
        "source_changed_during_run": changed_sources,
        "source_added_during_run": added_sources,
        "manuscript_sha256": digest(root / "reference" / "aop-sample.tex"),
    }, indent=2) + "\n")
    print(f"Compilation gate: {'PASS' if ok else 'INCOMPLETE'}; {len(records)}/{len(sources)} modules")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
