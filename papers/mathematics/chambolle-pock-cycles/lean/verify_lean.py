#!/usr/bin/env python3
"""Rebuild every release module in a fresh directory and audit theorem axioms.

The mathlib installation must match the pinned revision and contain its compiled
dependencies. No existing local proof object is on the generated LEAN_PATH.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import shutil
import sys
import time

MATHLIB_REV = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
MODULES = ['Proximal', 'ThreeCycleThreshold', 'ThreeCycleFunctions', 'GeneralSteps', 'TriangleCycle', 'ParameterBoundary', 'PhaseDiagram', 'QuadraticStability', 'FiniteCycle', 'SevenCycle', 'AttractingCycle', 'SevenAttracting', 'TrigSupport', 'TrigGrid', 'FourierModes', 'FourierAlgebra', 'FourierCertificates', 'FourierSums', 'FourierRobustness', 'AsymptoticParameters', 'AsymptoticCycle']
THEOREMS = ['CPSharpness.supports_iff_isProx', 'CPSharpness.threeCycle_sos_identity', 'CPSharpness.proximal_three_cycle_polynomial_nonneg', 'CPSharpness.step_product_three_cycle_polynomial_nonneg', 'CPSharpness.zero_saddle', 'CPSharpness.primal_isProx', 'CPSharpness.dual_isProx', 'CPSharpness.sharp_cycle_nonconvergence', 'CPSharpness.polynomial_iff_boundary', 'CPSharpness.boundary_below_quadratic_exact_interval', 'CPSharpness.sharp_three_cycle_iff', 'CPSharpness.sharp_three_cycle_counterexample', 'CPQuadratic.eigenmode_characteristic', 'CPQuadratic.cp_positive_quadratic_eigenmode_stable', 'CPQuadratic.cp_nonnegative_quadratic_eigenmode_stable_or_one', 'FiniteCP.project_isProx', 'FiniteCP.certified_step', 'FiniteCP.certified_nonconvergence', 'FiniteCP.origin_saddle', 'SevenCP.strict_normal_certificate', 'SevenCP.compact_saddle', 'SevenCP.actual_seven_cycle', 'SevenCP.below_three_cycle_and_quadratic', 'FiniteCP.project_locally_constant', 'FiniteCP.cycle_one_step_capture', 'FiniteCP.nearby_iterates_not_convergent', 'SevenCP.seven_cycle_one_step_capture', 'SevenCP.seven_cycle_open_basin', 'SevenCP.rational_example_open_basin', 'TrigSupport.cubicSquare_le_one', 'TrigSupport.cos_cube_add_sin_cube_le_one', 'TrigGrid.fourier_support', 'AsymptoticCP.rawPrimal_periodic', 'AsymptoticCP.dualPoints_norm_sq', 'AsymptoticCP.rawDual_support_identity', 'AsymptoticCP.primalPoints_zero_ne_one', 'AsymptoticCP.dualPoints_support_bound', 'AsymptoticCP.primalPoints_sum_zero', 'AsymptoticCP.dualPoints_sum_zero', 'AsymptoticCP.positive_theta_normal_certificate', 'AsymptoticCP.exists_fourier_period', 'AsymptoticCP.fourier_family_normal_certificate', 'AsymptoticCP.fourier_family_periodic', 'AsymptoticCP.fourier_family_nonconvergence', 'AsymptoticCP.counterexamples_for_every_product_above_two']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', type=Path, default=root/'.lake/packages/mathlib')
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--timeout', type=int, default=1800)
    args = parser.parse_args()
    mathlib = args.mathlib.resolve()
    output = (args.output or root/'verification'/dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')).resolve()
    if output.exists():
        raise SystemExit('The output directory must be new; no prior local proof objects may be reused.')
    output.mkdir(parents=True)
    lean = str(args.lean.resolve()) if args.lean else 'lean'
    receipt = {'status': 'incomplete', 'started_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
               'modules': [], 'theorems': THEOREMS,
               'mathlib_expected_revision': MATHLIB_REV, 'allowed_axioms': sorted(ALLOWED_AXIOMS)}
    receipt['verifier_sha256'] = sha256(Path(__file__).resolve())
    receipt['configuration_sha256'] = {
        name: sha256(root/name) for name in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']
    }

    def record() -> None:
        (output/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')

    def run(command: list[str], logname: str, env: dict[str,str] | None = None) -> str:
        start = time.monotonic()
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=args.timeout)
        (output/logname).write_text(result.stdout)
        receipt['modules'].append({'command': command, 'exit_code': result.returncode,
                                   'seconds': time.monotonic()-start, 'log': logname})
        record()
        if result.returncode:
            raise RuntimeError(f'Command failed ({result.returncode}); see {output/logname}')
        return result.stdout

    try:
        toolchain = (root/'lean-toolchain').read_text().strip()
        if toolchain != 'leanprover/lean4:v4.19.0':
            raise RuntimeError('Unexpected project Lean toolchain.')
        if (mathlib/'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('The installed mathlib toolchain differs from the project pin.')
        version = run([lean, '--version'], 'lean-version.log').strip()
        if 'version 4.19.0' not in version:
            raise RuntimeError('The executable is not Lean 4.19.0.')
        receipt['lean_version'] = version
        resolved_lean = Path(shutil.which(lean) or lean).resolve()
        receipt['lean_executable_sha256'] = sha256(resolved_lean)
        receipt['toolchain'] = toolchain
        receipt['mathlib_path'] = str(mathlib)
        receipt['dependency_metadata_sha256'] = {
            name: sha256(mathlib/name) for name in ['lean-toolchain', 'lake-manifest.json']
        }
        if (mathlib/'.git').exists():
            actual = run(['git','-C',str(mathlib),'rev-parse','HEAD'], 'mathlib-revision.log').strip()
            receipt['mathlib_actual_revision'] = actual
            if actual != MATHLIB_REV:
                raise RuntimeError('The installed mathlib Git revision differs from the exact pin.')
            dirty = run(['git','-C',str(mathlib),'status','--porcelain','--untracked-files=no'],
                        'mathlib-working-tree.log').strip()
            if dirty:
                raise RuntimeError('The pinned mathlib checkout has tracked source modifications.')
        else:
            receipt['dependency_revision_limit'] = (
                'Supplied mathlib is an extracted archive without Git metadata. '
                'Toolchain and dependency manifests are hashed; provenance of the source archive '
                'must be established separately. This runner does not claim a Git revision check.')
        dependency_manifest = json.loads((mathlib/'lake-manifest.json').read_text())
        receipt['dependency_manifest'] = dependency_manifest
        receipt['dependency_revisions'] = {}
        packages = []
        for dep in dependency_manifest['packages']:
            name = dep['name']
            candidates = [mathlib/'.lake/packages'/name, mathlib.parent/name, root/'.lake/packages'/name]
            package = next((p for p in candidates if p.is_dir()), None)
            if package is None:
                raise RuntimeError(f'Missing pinned dependency {name}.')
            packages.append(package)
            if (package/'.git').exists():
                revision = run(['git','-C',str(package),'rev-parse','HEAD'],
                               'dependency-'+name+'-revision.log').strip()
                if revision != dep['rev']:
                    raise RuntimeError(f'Dependency {name} differs from its pinned revision.')
                dirty = run(['git','-C',str(package),'status','--porcelain','--untracked-files=no'],
                            'dependency-'+name+'-working-tree.log').strip()
                if dirty:
                    raise RuntimeError(f'Dependency {name} has tracked source modifications.')
                receipt['dependency_revisions'][name] = revision
            else:
                receipt['dependency_revisions'][name] = 'archive; revision not independently checked'
        sources = {name: root/(name+'.lean') for name in MODULES}
        hashes = {name: sha256(path) for name,path in sources.items()}
        receipt['source_sha256'] = hashes
        prohibited = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide)\b')
        for name,path in sources.items():
            match = prohibited.search(path.read_text())
            if match:
                raise RuntimeError(f'Prohibited proof construct {match.group()} in {path.name}.')
        paths = [output, mathlib/'.lake/build/lib/lean']
        paths += [p/'.lake/build/lib/lean' for p in packages]
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,paths)))
        receipt['lean_path'] = env['LEAN_PATH']
        receipt['trust_level'] = 0
        receipt['warnings_as_errors'] = True
        for name,path in sources.items():
            run([lean,'-j1','--trust=0','-DwarningAsError=true','-o',str(output/(name+'.olean')),str(path)],
                name+'.log',env)
            if not (output/(name+'.olean')).is_file():
                raise RuntimeError(f'Missing fresh object for {name}.')
            print(f'{name}: verified',flush=True)
        audit = output/'AxiomAudit.lean'
        audit.write_text('\n'.join('import '+name for name in MODULES)+'\n\n'+
                         '\n'.join('#print axioms '+name for name in THEOREMS)+'\n\n'+
                         '\n'.join('#check @'+name for name in THEOREMS)+'\n')
        audit_output = run([lean,'-j1','--trust=0','-DwarningAsError=true',str(audit)],'AxiomAudit.log',env)
        reports = {}
        for theorem in THEOREMS:
            match = re.search(r"'"+re.escape(theorem)+r"' depends on axioms: \[([^\]]*)\]", audit_output)
            if not match:
                raise RuntimeError(f'Missing axiom report for {theorem}.')
            axioms = {x.strip() for x in match.group(1).split(',') if x.strip()}
            if not axioms <= ALLOWED_AXIOMS:
                raise RuntimeError(f'Unapproved axioms for {theorem}: {axioms-ALLOWED_AXIOMS}')
            reports[theorem] = sorted(axioms)
        if {name:sha256(path) for name,path in sources.items()} != hashes:
            raise RuntimeError('Sources changed during verification.')
        if sha256(Path(__file__).resolve()) != receipt['verifier_sha256']:
            raise RuntimeError('Verifier changed during verification.')
        if {name:sha256(root/name) for name in receipt['configuration_sha256']} != receipt['configuration_sha256']:
            raise RuntimeError('Pinned build configuration changed during verification.')
        receipt['axiom_reports'] = reports
        receipt['object_sha256'] = {name:sha256(output/(name+'.olean')) for name in MODULES}
        receipt['status'] = 'passed'
        receipt['finished_utc'] = dt.datetime.now(dt.timezone.utc).isoformat()
        record()
        print(f'All modules and axiom audits passed. Receipt: {output/"receipt.json"}')
    except Exception as error:
        receipt['status'] = 'failed'
        receipt['error'] = str(error)
        record()
        raise


if __name__ == '__main__':
    main()
