#!/usr/bin/env python3
"""Recompile sources and verify strict manuscript endpoints and proof routes."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from compile_strict import digest, has_sorry_diagnostic, pinned_environment

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--incremental', action='store_true',
                    help='Reuse only unchanged, previously checked source/dependency closures.')
parser.add_argument('--jobs', type=int, default=3,
                    help='Maximum concurrent project compilers (default: 3).')
args = parser.parse_args()
if args.jobs < 1:
    parser.error('--jobs must be at least 1')
lake = os.environ.get('BERRY_ESSEEN_LAKE') or shutil.which('lake')
if not lake:
    raise SystemExit('Set BERRY_ESSEEN_LAKE or put the pinned lake executable on PATH')
env = os.environ.copy()
env['BERRY_ESSEEN_LAKE'] = lake
out = root / 'validation'
out.mkdir(exist_ok=True)
summary_path = out / 'strict-summary.json'
summary = {'all_strict_gates_passed': False, 'gates': {}}
summary_path.write_text(json.dumps(summary, indent=2) + '\n')
environment = pinned_environment(root, lake)
summary['build_environment'] = environment
audit_paths = [root / 'BerryEsseen.lean', *sorted((root / 'Checks').glob('*.lean')),
               *sorted((root / 'scripts').glob('*.py')),
               root / 'notes/manuscript-endpoints.json', root / 'reference/aop-sample.tex']
audit_hashes = {str(path.relative_to(root)): digest(path) for path in audit_paths}

project_modules = {'BerryEsseen.' + path.stem for path in (root / 'BerryEsseen').glob('*.lean')}
root_modules = set(re.findall(r'^import\s+(BerryEsseen\.[\w.]+)',
                             (root / 'BerryEsseen.lean').read_text(), re.M))
if root_modules != project_modules:
    raise SystemExit('Root import coverage differs from project sources: ' +
                     repr(sorted(root_modules ^ project_modules)))

def run_gate(name, command, expected_axiom_target=None):
    with (out / (name + '.log')).open('w') as log:
        result = subprocess.run(command, cwd=root, env=env, stdout=log,
                                stderr=subprocess.STDOUT, check=False)
    log_text = (out / (name + '.log')).read_text()
    failure = 'Lean emitted a sorry diagnostic' if has_sorry_diagnostic(log_text) else None
    axiom_names = None
    if expected_axiom_target is not None:
        match = re.search("'" + re.escape(expected_axiom_target) +
                          r"' depends on axioms: \[([^\]]*)\]", log_text)
        if not match:
            failure = 'Missing exact wrapper axiom report'
        else:
            axiom_names = sorted(x.strip() for x in match.group(1).split(',') if x.strip())
            if set(axiom_names) - {'propext', 'Classical.choice', 'Quot.sound'}:
                failure = 'Unexpected wrapper axiom dependencies'
    summary['gates'][name] = {'exit_code': result.returncode,
                            'passed': result.returncode == 0 and failure is None,
                            'failure': failure,
                            'log': 'validation/' + name + '.log'}
    if axiom_names is not None:
        summary['gates'][name]['target_axioms'] = axiom_names
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    print(name, 'PASS' if summary['gates'][name]['passed'] else 'FAIL', flush=True)
    if not summary['gates'][name]['passed']:
        print(log_text)
        if failure:
            print(failure)
        raise SystemExit(result.returncode or 2)

build = [sys.executable, 'scripts/compile_strict.py', '--lake', lake, '--jobs', str(args.jobs)]
if args.incremental:
    build.append('--incremental')
run_gate('strict-build-driver', build)
run_gate('strict-root', [lake, 'env', 'lean', 'BerryEsseen.lean', '-o',
                         '.lake/build/lib/lean/BerryEsseen.olean'])
run_gate('strict-axioms', [lake, 'env', 'lean', 'Checks/StrictAxioms.lean'])
run_gate('exact-kernel-types', [lake, 'env', 'lean', 'Checks/DeepKernelAudit.lean'])
run_gate('manuscript-statement-coverage', [lake, 'env', 'lean', 'Checks/ManuscriptCoverage.lean'])
run_gate('supplemental-original-routes', [lake, 'env', 'lean', 'Checks/SupplementalRouteAudit.lean'])
run_gate('bounded-full-statement', [lake, 'env', 'lean', 'Checks/BoundedFullStatementAudit.lean'],
         'BerryEsseen.CurrentRecheck.bounded_extremizers_full_manuscript_statement')
run_gate('strict-main-route', [sys.executable, 'scripts/strict_dependencies.py'])
run_gate('strict-explicit-route', [sys.executable, 'scripts/strict_explicit_dependencies.py'])

build_data = json.loads((out / 'strict-build.json').read_text())
main_data = json.loads((out / 'strict-dependencies.json').read_text())
explicit_data = json.loads((out / 'strict-explicit-dependencies.json').read_text())
axioms_log = (out / 'strict-axioms.log').read_text()
marker = 'STRICT_ALL_AXIOMS_JSON: '
start = axioms_log.find(marker)
if start < 0:
    raise SystemExit('Missing dynamic project axiom report')
axioms_data, _ = json.JSONDecoder().raw_decode(axioms_log[start + len(marker):])
if axioms_data['unexpected_axioms']:
    raise SystemExit('Unexpected axioms in the project-wide report')
hashes = {'BerryEsseen/' + path.name: hashlib.sha256(path.read_bytes()).hexdigest()
          for path in (root / 'BerryEsseen').glob('*.lean')}
for name, data in [('main', main_data), ('explicit', explicit_data)]:
    if data['source_sha256'] != hashes:
        raise SystemExit(f'Sources changed since the {name} dependency check')
if build_data['build_environment'] != environment:
    raise SystemExit('Build environment differs from the verification environment')
if not build_data['all_project_sources_compiled']:
    raise SystemExit('Source compilation was incomplete')
for module, record in build_data['modules'].items():
    path = module.replace('.', '/') + '.lean'
    if hashes.get(path) != record['source_sha256']:
        raise SystemExit('Source changed after compilation: ' + path)
    if digest(root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')) != record['olean_sha256']:
        raise SystemExit('Compiled object changed after compilation: ' + path)
for path, value in audit_hashes.items():
    if digest(root / path) != value:
        raise SystemExit('Audit input changed during verification: ' + path)
for path, value in environment['configuration_sha256'].items():
    if digest(root / path) != value:
        raise SystemExit('Build configuration changed during verification: ' + path)
for data, audit_name in [(main_data, 'StrictAudit'), (explicit_data, 'StrictExplicitAudit')]:
    if data['audit_lean_sha256'] != audit_hashes['Checks/' + audit_name + '.lean']:
        raise SystemExit('Dependency audit source snapshot mismatch: ' + audit_name)
summary.update({
    'all_strict_gates_passed': True,
    'project_module_count': build_data['module_count'],
    'named_manuscript_statements': len(json.loads(
        (root / 'notes/manuscript-endpoints.json').read_text())['entries']),
    'manuscript_additional_conjuncts': len(json.loads(
        (root / 'notes/manuscript-endpoints.json').read_text())['additional_conjunct_endpoints']),
    'project_axiom_union': axioms_data,
    'main_required_paths': len(main_data['proof_values']['required']),
    'main_forbidden_found': main_data['proof_values']['forbidden_found'],
    'explicit_required_paths': len(explicit_data['proof_values']['required']),
    'explicit_forbidden_found': explicit_data['proof_values']['forbidden_found'],
    'manuscript_sha256': hashlib.sha256((root / 'reference/aop-sample.tex').read_bytes()).hexdigest(),
    'source_sha256': hashes,
    'audit_source_sha256': audit_hashes,
    'scope': 'Project sources elaborated; pinned external mathlib dependencies reused. '
             'Kernel type/axiom/proof-expression checks do not automate semantic comparison with prose.',
})
summary_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2) + '\n')
print('All strict compilation, type, axiom, and proof-dependency gates passed.', flush=True)
