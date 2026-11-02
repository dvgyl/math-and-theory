#!/usr/bin/env python3
"""Replay the exact finite checks of this package in a temporary copy.

The checkers write their reports next to their inputs, so this program copies
checks/ to a temporary directory, decompresses every *.json.xz file there and
runs each checker with `python3 -I`, adding only the checker's own directory to
the import path. NetworkX 3.7 is needed (requirements.txt). The optional
nauty programs geng and labelg enable two further replays.

    python3 checks/run_checks.py [--independent] [--geng PATH --labelg PATH] [--keep DIR]
"""
import argparse
import lzma
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

RUNNER = ("import runpy,sys,os;s=os.path.abspath(sys.argv[1]);"
          "sys.path.insert(0,os.path.dirname(s));sys.argv=sys.argv[1:];"
          "runpy.run_path(s,run_name='__main__')")

CORE = [
    ('five-point cone arithmetic', 'verification/check_five_point_cones.py', []),
    ('capped local certificate and all coefficient choices', 'structure/verify_capped_local_certificate.py', []),
    ('fifteen residual metrics', 'verification/check_capped_survivors.py',
     ['--source', 'structure/capped_local_proof_certificate.json']),
    ('block palette, orders three to six', 'literature/verify_small_cores_independent.py', []),
    ('227-kernel closure', 'experiments/verify_catalogue.py', []),
    ('sharp order-fourteen kernel', 'check_graph.py', ['data/sharp14.json']),
    ('rooted metric truncation audit', 'extensions/audit_generalize/check_rooted_metric.py', []),
    ('even two-tree automaton', 'extensions/two_tree_equality/verify_path_core_automaton.py', []),
    ('even automaton graph semantics', 'extensions/audit_generalize/audit_automaton_graph_semantics.py', []),
    ('complete equality grammar', 'extensions/audit_generalize/verify_general_equality_grammar.py', []),
    ('grammar graph witnesses', 'extensions/two_tree_equality/grammar_graph_witnesses.py', []),
    ('quartic growth and lower family', 'extensions/two_tree_equality/strip_growth.py', []),
    ('grammar growth audit', 'extensions/audit_generalize/audit_grammar_growth.py', []),
    ('exact odd counting identities', 'extensions/two_tree_equality/exact_odd_count.py', ['--through', '101']),
    ('reflection centres of the odd count', 'extensions/audit_generalize/audit_odd_count_centers.py', []),
    ('bipartite subcubic audit', 'extensions/six_boundary/check_new_results.py', []),
    ('infinite metric obstruction', 'extensions/six_local/check_infinite_obstruction.py', []),
]

INDEPENDENT = [
    ('five boundary, all graphs to order 8', 'independent/check.py',
     ['five', 'experiments/reduced_kernels_boundary5.g6', '8']),
    ('subcubic six boundary, all subcubic graphs to order 11', 'independent/check.py',
     ['six', 'extensions/six_boundary/connected_subcubic_boundary6.g6', '11']),
    ('two-trees to order 13', 'independent/twotree.py', ['13']),
    ('two-connected subcubic census to order 14', 'independent/ears.py', ['14']),
    ('201-kernel closure from the census blocks', 'independent/closure.py',
     ['ears_le6_14.json', 'extensions/six_boundary/connected_subcubic_boundary6.g6', '6', '3']),
    ('227-kernel closure from all blocks of order at most 6', 'independent/closure.py',
     ['all6', 'experiments/reduced_kernels_boundary5.g6', '5', '99']),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--independent', action='store_true',
                        help='also run the independent enumerations (about ten minutes)')
    parser.add_argument('--geng', help='nauty geng: replay the 60,070-graph subcubic core census')
    parser.add_argument('--labelg', help='nauty labelg: replay the 201-kernel closure')
    parser.add_argument('--keep', type=Path, help='keep the working copy and reports here')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    work = Path(tempfile.mkdtemp(prefix='harmonic-boundary-checks-'))
    tree = work / 'checks'
    shutil.copytree(source, tree, ignore=shutil.ignore_patterns('__pycache__', 'run_checks.py'))
    for packed in tree.rglob('*.json.xz'):
        packed.with_suffix('').write_bytes(lzma.decompress(packed.read_bytes()))
        packed.unlink()
    jobs = list(CORE)
    if args.geng:
        jobs.append(('subcubic core census with geng', 'extensions/six_local/verify_subcubic_cores_small.py',
                     ['--geng', args.geng]))
    if args.labelg:
        jobs.append(('201-kernel closure with labelg', 'extensions/audit_generalize/verify_subcubic_kernel_closure.py',
                     ['--labelg', args.labelg]))
    if args.independent:
        jobs += INDEPENDENT
    failed = []
    for name, script, extra in jobs:
        start = time.monotonic()
        run = subprocess.run([sys.executable, '-I', '-c', RUNNER, script, *extra], cwd=tree,
                             capture_output=True, text=True)
        status = 'PASS' if run.returncode == 0 else 'FAIL'
        print(f'{status}  {name}  ({time.monotonic() - start:.1f} s)', flush=True)
        if run.returncode:
            failed.append(name)
            print(run.stdout[-3000:] + run.stderr[-3000:])
    if args.keep:
        shutil.copytree(tree, args.keep, dirs_exist_ok=True)
    shutil.rmtree(work)
    print('all checks passed' if not failed else f'{len(failed)} check(s) failed')
    raise SystemExit(1 if failed else 0)


if __name__ == '__main__':
    main()
