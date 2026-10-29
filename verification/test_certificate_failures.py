#!/usr/bin/env python3
"""Test mathematical failures, incomplete coverage, and checker exit codes."""
from pathlib import Path
import ast
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXTENSIONS = ROOT / 'papers/mathematics/gyires/research-notes/extensions/certificates'
SUPPORT = ROOT / 'papers/mathematics/gyires/research-notes/complete-support/certificates'
ORDER_FIVE = ROOT / 'papers/mathematics/gyires/verification'


class CertificateFailureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.folder = Path(self.temporary.name)
        for source in (EXTENSIONS, SUPPORT):
            for path in source.iterdir():
                if path.suffix in {'.py', '.mjs'}:
                    shutil.copy2(path, self.folder / path.name)

    def run_script(self, name, *args, optimized=False):
        command = ['node'] if name.endswith('.mjs') else [sys.executable]
        if optimized:
            command.append('-O')
        command += [str(self.folder / name), *map(str, args)]
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        return subprocess.run(command, cwd=self.folder, env=env, text=True,
                              capture_output=True, timeout=90)

    def replace(self, name, old, new):
        path = self.folder / name
        source = path.read_text()
        self.assertEqual(source.count(old), 1, 'Fault injection location changed.')
        path.write_text(source.replace(old, new))

    def failed(self, result, message):
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(message, result.stdout + result.stderr)

    def passed(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def read_report(self, name):
        return json.loads((self.folder / name).read_text())

    def primary_rows(self):
        return json.loads((SUPPORT.parent / 'results/deletion_n3_birkhoff.json').read_text())

    def write_primary(self, rows):
        (self.folder / 'deletion_n3_birkhoff.json').write_text(json.dumps(rows))

    def test_optimized_python_cannot_skip_assertions(self):
        checked = 0
        for folder in (EXTENSIONS, SUPPORT, ORDER_FIVE):
            for source in folder.glob('*.py'):
                if not any(isinstance(node, ast.Assert) for node in ast.walk(ast.parse(source.read_text()))):
                    continue
                with self.subTest(script=str(source.relative_to(ROOT))):
                    shutil.copy2(source, self.folder / source.name)
                    self.failed(self.run_script(source.name, optimized=True),
                                'Certificate checks require assertions')
                    checked += 1
        self.assertGreaterEqual(checked, 20)

    def test_axiom_checker_rejects_empty_statement_or_declaration_coverage(self):
        shutil.copy2(ORDER_FIVE / 'check_axioms.py', self.folder / 'check_axioms.py')
        specification = self.folder / 'AxiomAudit.lean'
        log = self.folder / 'axioms.log'
        for statements, count in [('', 1), ('#print axioms Example.result', 0)]:
            with self.subTest(statements=statements, count=count):
                specification.write_text(statements)
                log.write_text("'Example.result' depends on axioms: [propext]\n"
                               f'declaration scan: {count} declarations\n'
                               'declaration scan: declarations with non-standard axioms: 0\n'
                               'declaration scan: axioms used: [propext]\n')
                self.failed(self.run_script('check_axioms.py', log), 'RESULT: FAIL')

    def test_source_checker_rejects_missing_proof_library(self):
        relative = 'papers/mathematics/gyires/verification/scan_sources.py'
        target = self.folder / relative
        target.parent.mkdir(parents=True)
        shutil.copy2(ORDER_FIVE / 'scan_sources.py', target)
        for name, count in [('Challenges/Mathematics/Gyires/CirculantFive.lean', 18),
                            ('Solutions/Mathematics/Gyires/CirculantFive.lean', 0),
                            ('Solutions/Mathematics/Gyires/FourBlock.lean', 0),
                            ('Solutions/Mathematics/Gyires/ExceptionalVector.lean', 0)]:
            path = self.folder / 'lean' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('example : True := by sorry\n' * count)
        self.failed(self.run_script(relative), 'RESULT: FAIL')

    def test_source_checker_requires_both_libraries_and_exact_placeholders(self):
        relative = 'papers/mathematics/gyires/verification/scan_sources.py'
        target = self.folder / relative
        target.parent.mkdir(parents=True)
        shutil.copy2(ORDER_FIVE / 'scan_sources.py', target)
        for name, count in [('Challenges/Mathematics/Gyires/CirculantFive.lean', 18),
                            ('Solutions/Mathematics/Gyires/CirculantFive.lean', 0),
                            ('Solutions/Mathematics/Gyires/FourBlock.lean', 0),
                            ('Solutions/Mathematics/Gyires/ExceptionalVector.lean', 0)]:
            path = self.folder / 'lean' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('example : True := by sorry\n' * count)
        for family in ('Gyires/CirculantFive', 'Gyires'):
            path = self.folder / 'lean/MathAndTheory/Mathematics' / family / 'Proof.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('example : True := by trivial\n')
        self.passed(self.run_script(relative))
        for family in ('Gyires/CirculantFive', 'Gyires'):
            path = self.folder / 'lean/MathAndTheory/Mathematics' / family / 'Proof.lean'
            source = path.read_text()
            path.unlink()
            self.failed(self.run_script(relative), 'RESULT: FAIL')
            path.write_text(source)
        path = self.folder / 'lean/Challenges/Mathematics/Gyires/CirculantFive.lean'
        source = path.read_text()
        for count in (17, 19):
            path.write_text('example : True := by sorry\n' * count)
            self.failed(self.run_script(relative), 'RESULT: FAIL')
        for modifiers in ('', 'public ', 'meta ', 'public meta '):
            for scope in ('', 'all '):
                prefix = f'{modifiers}import {scope}'
                with self.subTest(import_prefix=prefix):
                    path.write_text(prefix + 'Mathlib.Data.Matrix.Basic\n' + source)
                    self.passed(self.run_script(relative))
                    path.write_text(prefix + 'Challenges.Local\n' + source)
                    self.failed(self.run_script(relative), 'local Challenge import')
        for header in ('import Mathlib import Challenges.Local',
                       'import/--/Challenges.Local',
                       'import\nChallenges.Local'):
            with self.subTest(import_header=header):
                path.write_text(header + '\n' + source)
                self.failed(self.run_script(relative), 'local Challenge import')
        path.write_text('-- import Challenges.Local\n/- import Challenges.Local -/\n' + source)
        self.passed(self.run_script(relative))
        path.unlink()
        self.failed(self.run_script(relative), 'RESULT: FAIL')

    def test_circulant_copies_match(self):
        self.assertEqual((EXTENSIONS / 'circ_gap_test.py').read_bytes(),
                         (SUPPORT / 'circ_gap_test.py').read_bytes())

    def test_circulant_rejects_invalid_arguments(self):
        for args in [('2', 'all'), ('3', 'typo')]:
            with self.subTest(args=args):
                self.failed(self.run_script('circ_gap_test.py', *args),
                            'Require order >= 3 and mode all or one')

    def test_circulant_negative_coefficient_fails(self):
        self.replace('circ_gap_test.py', 'g=gap_transform(d,u,base,p)',
                     'g=gap_transform(d,u,base,p);g[next(iter(g))]=-1')
        self.failed(self.run_script('circ_gap_test.py', 3, 'all'),
                    'A negative exact coefficient was found')
        self.assertEqual(self.read_report('circ_gap_n3_all_results.json')['status'], 'failed')

    def test_circulant_missing_chamber_fails(self):
        self.replace('circ_gap_test.py', 'for r,p in enumerate(reps):',
                     'for r,p in enumerate([]):')
        self.failed(self.run_script('circ_gap_test.py', 3, 'all'),
                    'Incomplete chamber results')

    def test_circulant_empty_enumeration_fails(self):
        self.replace('circ_gap_test.py', 'list(affine_reps(n))', '[]')
        self.failed(self.run_script('circ_gap_test.py', 3, 'all'),
                    'Incomplete affine chamber coverage')

    def test_circulant_valid_small_certificate(self):
        self.passed(self.run_script('circ_gap_test.py', 3, 'all'))
        report = self.read_report('circ_gap_n3_all_results.json')
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(len(report['chambers']), 1)
        self.assertTrue(all(row['negative_terms'] == 0 for row in report['chambers']))
        self.passed(self.run_script('circ_gap_test.py', 3, 'one'))
        self.assertEqual(self.read_report('circ_gap_n3_one_results.json')['status'], 'sampled')

    def test_transfer_rejects_empty_range(self):
        self.failed(self.run_script('circ_transfer.py', 4),
                    'Maximum order must be at least five')

    def test_transfer_negative_coefficient_fails(self):
        self.replace('circ_transfer.py', 'gap=gap_transform(defect,u,b,perm)',
                     'gap=gap_transform(defect,u,b,perm);gap[next(iter(gap))]=-1')
        self.failed(self.run_script('circ_transfer.py', 5),
                    'A negative exact coefficient was found')
        self.assertGreater(self.read_report('circ_transfer_negative.json')['negative_count'], 0)

    def test_transfer_missing_chamber_fails(self):
        self.replace('circ_transfer.py', 'for perm in permutations(range(3)):',
                     'for perm in list(permutations(range(3)))[:-1]:')
        self.failed(self.run_script('circ_transfer.py', 5),
                    'Incomplete sorting chamber coverage')

    def test_transfer_valid_small_certificate(self):
        self.passed(self.run_script('circ_transfer.py', 5))
        rows = self.read_report('circ_transfer_results.json')
        self.assertEqual([row['n'] for row in rows], [5])
        self.assertEqual(rows[0]['chambers'], 6)

    def test_deletion_negative_coefficient_fails(self):
        self.replace('deletion_n3_certificate.py',
                     'g=gap_transform(gap,u,base,order);neg=',
                     'g=gap_transform(gap,u,base,order);g[next(k for k in g if k not in {6*x for x in u})]=-1;neg=')
        self.failed(self.run_script('deletion_n3_certificate.py'),
                    'A negative exact coefficient was found')
        self.assertFalse((self.folder / 'deletion_n3_birkhoff.json').exists())

    def test_deletion_incomplete_enumeration_fails(self):
        self.replace('deletion_n3_certificate.py',
                     'for tail in permutations(range(1,6)):\n',
                     'for tail in []:\n')
        self.failed(self.run_script('deletion_n3_certificate.py'),
                    'Incomplete cubic chamber coverage')

    def test_deletion_consumers_reject_missing_duplicate_and_failed_rows(self):
        for script in ('deletion_n3_crosscheck.py', 'deletion_n3_independent_audit.py'):
            for corruption in ('empty', 'missing', 'duplicate', 'negative'):
                with self.subTest(script=script, corruption=corruption):
                    rows = self.primary_rows()
                    if corruption == 'empty':
                        rows = []
                    elif corruption == 'missing':
                        rows.pop()
                    elif corruption == 'duplicate':
                        rows[-1] = rows[0]
                    else:
                        rows[0]['negative'] = 1
                    self.write_primary(rows)
                    self.failed(self.run_script(script), 'Primary certificate')

    def test_rank_two_rejects_empty_ranges(self):
        for script in ('rank2_bernstein.py', 'rank2_bernstein_fraction_check.py'):
            with self.subTest(script=script):
                self.failed(self.run_script(script, '--first', 3, '--last', 2),
                            'Require 2 <= first <= last')

    def test_rank_two_valid_small_certificates(self):
        for script, output in (
                ('rank2_bernstein.py', 'rank2_bernstein_certificate.json'),
                ('rank2_bernstein_fraction_check.py', 'rank2_fraction_comparison.json')):
            with self.subTest(script=script):
                self.passed(self.run_script(script, '--first', 2, '--last', 2))
                report = self.read_report(output)
                self.assertEqual(report['status'], 'passed')
                self.assertEqual(report['requested_last_order'], 2)
                self.assertEqual([row['n'] for row in report['records']], [2])
                self.assertEqual(report['records'][0]['tested'], 2)

    def test_rank_two_samples_are_not_certificates(self):
        self.passed(self.run_script('rank2_bernstein.py', '--last', 2, '--samples', 20))
        report = self.read_report('rank2_bernstein_certificate.json')
        self.assertEqual(report['status'], 'sampled')
        self.assertFalse(report['exhaustive_profile_pairs'])

    def test_rank_two_partial_run_does_not_report_passed(self):
        for script, output in (
                ('rank2_bernstein.py', 'rank2_bernstein_certificate.json'),
                ('rank2_bernstein_fraction_check.py', 'rank2_fraction_comparison.json')):
            with self.subTest(script=script):
                self.replace(script, ' for n in range(args.first,args.last+1):',
                             ' for n in range(args.first,args.last+1):\n  if n==3: raise RuntimeError("interrupted before final order")')
                self.failed(self.run_script(script, '--last', 3), 'interrupted before final order')
                report = self.read_report(output)
                self.assertEqual(report['status'], 'running')
                self.assertEqual(report['last_completed_order'], 2)
                self.assertEqual(report['requested_last_order'], 3)

    def test_rank_two_empty_profile_enumeration_fails(self):
        self.replace('rank2_bernstein.py', 'for a,m,c,l in pairs:', 'for a,m,c,l in []:')
        self.failed(self.run_script('rank2_bernstein.py', '--last', 2),
                    'Incomplete profile interval coverage')
        self.assertEqual(self.read_report('rank2_bernstein_certificate.json')['status'], 'running')

    def test_rank_two_missing_coefficient_fails(self):
        self.replace('rank2_bernstein.py', 'ps=pol(n,a,m,c,l);tested+=1',
                     'ps=pol(n,a,m,c,l);ps=(ps[0][:-1],ps[1]);tested+=1')
        self.failed(self.run_script('rank2_bernstein.py', '--last', 2),
                    'Incomplete coefficient vectors')

    def test_javascript_rejects_invalid_and_empty_ranges(self):
        self.assertIsNotNone(shutil.which('node'), 'Node.js is required for certificate tests.')
        for value in ('invalid', '2', '3.5', 'Infinity', '-1'):
            with self.subTest(value=value):
                self.failed(self.run_script('independent_finite.mjs', value),
                            'Require one integer maximum order of at least three')

    def test_javascript_missing_chamber_fails(self):
        self.replace('independent_finite.mjs', 'for(let chamber=0;chamber<3;chamber++) {\n  let weights',
                     'for(let chamber=0;chamber<2;chamber++) {\n  let weights')
        self.failed(self.run_script('independent_finite.mjs', 3),
                    'Incomplete or duplicate finite certificate coverage')

    def test_javascript_negative_coefficient_fails(self):
        self.replace('independent_finite.mjs',
                     'let z=factor*psq.v[k]-fact*gram.v[k];',
                     'let z=k===0 ? -1n : factor*psq.v[k]-fact*gram.v[k];')
        self.failed(self.run_script('independent_finite.mjs', 3),
                    'negative coefficient')
        self.assertFalse((self.folder / 'independent_finite.json').exists())

    def test_javascript_truncated_vector_fails(self):
        self.replace('independent_finite.mjs',
                     'const positions=(2*n+1)*(2*n+2)/2;',
                     'psq.v.pop();const positions=(2*n+1)*(2*n+2)/2;')
        self.failed(self.run_script('independent_finite.mjs', 3),
                    'Incomplete coefficient vector')

    def test_false_identity_fails(self):
        self.replace('sharp_bound_check.py', 'assert trim(P)==trim(expected)',
                     'assert False, "injected false identity"')
        self.failed(self.run_script('sharp_bound_check.py'), 'injected false identity')
        self.assertFalse((self.folder / 'sharp_bound_check.json').exists())
        self.failed(self.run_script('sharp_bound_check.py', optimized=True),
                    'Certificate checks require assertions')

    def test_sharp_bound_valid_certificate(self):
        self.passed(self.run_script('sharp_bound_check.py'))
        self.assertTrue(self.read_report('sharp_bound_check.json')['all_passed'])

    def test_javascript_valid_small_certificate(self):
        self.passed(self.run_script('independent_finite.mjs', 3))
        report = self.read_report('independent_finite.json')
        self.assertEqual(report['status'], 'passed')
        self.assertEqual({(row['n'], row['chamber']) for row in report['results']},
                         {(3, 0), (3, 1), (3, 2)})
        self.assertTrue(all(row['negative'] == 0 for row in report['results']))


if __name__ == '__main__':
    unittest.main()
