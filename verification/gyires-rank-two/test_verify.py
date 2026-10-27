"""Test verification failures without starting Lean or Lake."""
from contextlib import ExitStack, redirect_stdout
from pathlib import Path
from unittest import TestCase, main, mock
import io
import json
import os
import tempfile

import check_package as package
import verify


class VerificationTests(TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        (self.root / 'src').mkdir()
        self.names = ['First', 'CompleteAudit']
        for name in self.names:
            (self.root / 'src' / (name + '.lean')).write_text('theorem ' + name + ' : True := by trivial\n')
        self.modules = {name: {'path': 'src/' + name + '.lean',
                              'sha256': package.digest(self.root / 'src' / (name + '.lean')),
                              'imports': [] if name == 'First' else ['First']} for name in self.names}
        self.expected = json.loads((package.ROOT / 'expected-axioms.json').read_text())
        self.final_log = '\n'.join("'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                                   for name in self.expected['theorems']) + '\n'
        for name in ['manifest.json', 'verify.py', 'lean']:
            (self.root / name).write_text('fixture\n')
        (self.root / 'sources.json').write_text(json.dumps({'entry_module': 'CompleteAudit'}))
        self.pins = [{'name': 'dep', 'revision': 'a' * 40}]
        self.fingerprint = [{'root': 'package:dep', 'objects': 1, 'bytes': 1, 'sha256': 'a' * 64}]
        self.calls = []

    def fixture_check(self, root):
        for item in self.modules.values():
            package.require(package.digest(root / item['path']) == item['sha256'], 'Fixture source changed.')
        return self.modules, self.expected

    def compile(self, arguments, root, environment, log, timeout):
        self.calls.append(arguments[-1])
        self.assertNotIn('untrusted', environment['LEAN_PATH'])
        output = Path(arguments[arguments.index('-o') + 1])
        output.write_text('checked ' + arguments[-1])
        output.with_suffix('.olean.private').write_text('private object')
        log.write_text(self.final_log if arguments[-1].endswith('CompleteAudit.lean') else '')
        return {'exit_code': 0, 'seconds': 0.0, 'peak_rss_kib': 1}

    def run_fixture(self, resume=False, compiler=None, **overrides):
        patches = {'check': self.fixture_check, 'build_order': lambda _: self.names,
                   'locked_packages': lambda _: [],
                   'discover': lambda *_: (self.root / 'lean', [], self.pins, 'Lean 4.35.0 fixture'),
                   'external_fingerprint': lambda _: self.fingerprint,
                   'check_packages': lambda *_: self.pins,
                   'compile_process': compiler or self.compile}
        patches.update(overrides)
        with ExitStack() as stack:
            for name, function in patches.items():
                stack.enter_context(mock.patch.object(verify, name, function))
            stack.enter_context(redirect_stdout(io.StringIO()))
            return verify.run(self.root, resume=resume)

    def incomplete(self):
        self.assertFalse(json.loads((self.root / '.verification/result.json').read_text())['complete'])

    def test_success_checks_final_log(self):
        result = self.run_fixture()
        self.assertTrue(result['complete'])
        self.assertEqual(result['final_axiom_reports'], 1)
        self.assertEqual(len(self.calls), 2)

    def test_unchanged_resume_reuses_only_checked_prefix(self):
        self.run_fixture()
        self.run_fixture(resume=True)
        self.assertEqual(len(self.calls), 2)

    def test_failure_stops_and_resume_retries(self):
        def fail_second(*args):
            if len(self.calls) == 1:
                raise ValueError('Simulated compiler failure.')
            return self.compile(*args)
        with self.assertRaises(ValueError):
            self.run_fixture(compiler=fail_second)
        self.incomplete()
        self.assertEqual(len(self.calls), 1)
        self.assertFalse((self.root / '.verification/pending').exists())
        self.run_fixture(resume=True)
        self.assertEqual(len(self.calls), 2)

    def test_existing_directory_requires_resume(self):
        self.run_fixture()
        with self.assertRaises(ValueError):
            self.run_fixture()

    def test_resume_requires_existing_directory(self):
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)

    def test_unrecorded_object_is_rejected(self):
        self.run_fixture()
        (self.root / '.verification/build/Other.olean').write_text('stale')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_unrecorded_known_object_is_rejected(self):
        self.run_fixture()
        path = self.root / '.verification/state.json'
        state = json.loads(path.read_text()); state['records'].pop()
        path.write_text(json.dumps(state))
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_object_change_is_rejected(self):
        self.run_fixture()
        (self.root / '.verification/build/First.olean').write_text('changed')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_log_change_is_rejected(self):
        self.run_fixture()
        (self.root / '.verification/logs/First.log').write_text('changed')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_source_change_is_rejected(self):
        self.run_fixture()
        (self.root / 'src/First.lean').write_text('changed')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_compiler_change_is_rejected(self):
        self.run_fixture()
        (self.root / 'lean').write_text('changed')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_dependency_object_change_is_rejected(self):
        self.run_fixture()
        self.fingerprint = []
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_dependency_pin_change_is_rejected(self):
        self.run_fixture()
        self.pins = []
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_verifier_change_is_rejected(self):
        self.run_fixture()
        (self.root / 'verify.py').write_text('changed')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_manifest_change_is_rejected(self):
        self.run_fixture()
        (self.root / 'manifest.json').write_text('changed')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_project_dependency_record_change_is_rejected(self):
        self.run_fixture()
        path = self.root / '.verification/state.json'
        state = json.loads(path.read_text()); state['records'][1]['dependencies'] = {}
        path.write_text(json.dumps(state))
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)
        self.incomplete()

    def test_symlink_is_rejected(self):
        self.run_fixture()
        (self.root / '.verification/extra').symlink_to(self.root / 'lean')
        with self.assertRaises(ValueError):
            self.run_fixture(resume=True)

    def test_default_project_outputs_are_rejected(self):
        path = self.root / '.lake/build/lib/lean'
        path.mkdir(parents=True); (path / 'First.olean').write_text('stale')
        with self.assertRaises(ValueError):
            verify.reject_default_outputs(self.root)

    def test_inherited_paths_and_git_settings_are_removed(self):
        with mock.patch.dict(os.environ, {'LEAN_PATH': 'untrusted', 'LEAN_SRC_PATH': 'bad',
                                          'GIT_DIR': 'bad', 'LAKE_HOME': 'bad', 'DYLD_INSERT_LIBRARIES': 'bad'}):
            environment = verify.clean_environment()
        for name in ['LEAN_PATH', 'LEAN_SRC_PATH', 'GIT_DIR', 'LAKE_HOME', 'DYLD_INSERT_LIBRARIES']:
            self.assertNotIn(name, environment)

    def test_changed_source_during_compile_is_rejected(self):
        def changed(*args):
            result = self.compile(*args)
            (self.root / 'src/First.lean').write_text('changed')
            return result
        with self.assertRaises(ValueError):
            self.run_fixture(compiler=changed)
        self.incomplete()

    def test_unexpected_output_is_rejected(self):
        def changed(*args):
            result = self.compile(*args)
            (self.root / '.verification/pending/extra.olean').write_text('unexpected')
            return result
        with self.assertRaises(ValueError):
            self.run_fixture(compiler=changed)
        self.incomplete()

    def test_missing_object_is_rejected(self):
        def changed(*args):
            result = self.compile(*args)
            (self.root / '.verification/pending/First.olean').unlink()
            return result
        with self.assertRaises(ValueError):
            self.run_fixture(compiler=changed)
        self.incomplete()

    def test_warning_is_rejected(self):
        def changed(*args):
            result = self.compile(*args)
            args[3].write_text('warning: simulated warning')
            return result
        with self.assertRaises(ValueError):
            self.run_fixture(compiler=changed)
        self.incomplete()

    def test_interruption_leaves_incomplete_result(self):
        def interrupted(*_):
            raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt):
            self.run_fixture(compiler=interrupted)
        self.incomplete()

    def test_external_objects_rechecked_after_compile(self):
        counter = iter([self.fingerprint, []])
        with self.assertRaises(ValueError):
            self.run_fixture(external_fingerprint=lambda _: next(counter))
        self.incomplete()

    def test_dependency_revision_rechecked_after_compile(self):
        with self.assertRaises(ValueError):
            self.run_fixture(check_packages=lambda *_: [])
        self.incomplete()

    def test_manifest_changed_during_build_is_rejected(self):
        def changed(*args):
            result = self.compile(*args)
            (self.root / 'manifest.json').write_text('changed')
            return result
        with self.assertRaises(ValueError):
            self.run_fixture(compiler=changed)
        self.incomplete()

    def test_compiler_failure_stops_process_group(self):
        process = mock.Mock()
        process.poll.return_value = 1
        process.returncode = 1
        with mock.patch.object(verify.subprocess, 'Popen', return_value=process), \
                mock.patch.object(verify, 'stop_group') as stop:
            with self.assertRaises(ValueError):
                verify.compile_process(['simulated'], self.root, {}, self.root / 'log', 10)
            stop.assert_called_once_with(process)

    def test_compiler_memory_failure_stops_process_group(self):
        process = mock.Mock()
        process.poll.return_value = None
        process.pid = 123
        with mock.patch.object(verify.subprocess, 'Popen', return_value=process), \
                mock.patch.object(verify.subprocess, 'check_output', return_value='123 2097153'), \
                mock.patch.object(verify, 'stop_group') as stop:
            with self.assertRaises(ValueError):
                verify.compile_process(['simulated'], self.root, {}, self.root / 'log', 10)
            stop.assert_called_once_with(process)

    def test_compiler_timeout_stops_process_group(self):
        process = mock.Mock()
        process.poll.return_value = None
        with mock.patch.object(verify.subprocess, 'Popen', return_value=process), \
                mock.patch.object(verify, 'stop_group') as stop:
            with self.assertRaises(ValueError):
                verify.compile_process(['simulated'], self.root, {}, self.root / 'log', 0)
            stop.assert_called_once_with(process)

    def test_final_reports_fail_closed(self):
        variants = ['', self.final_log + self.final_log, self.final_log.replace('propext', 'newAxiom'),
                    self.final_log + 'unknown output', self.final_log + 'warning: bad',
                    '\n'.join(self.final_log.splitlines()[:-1])]
        for content in variants:
            with self.subTest(content=content[:60]):
                path = self.root / 'axiom.log'; path.write_text(content)
                with self.assertRaises(ValueError):
                    package.check_axioms(path, self.expected)

    def test_final_missing_reports_fail_in_same_command(self):
        self.final_log = ''
        with self.assertRaises(ValueError):
            self.run_fixture()
        self.incomplete()

    def test_path_allowlist_rejects_unknown_empty_and_repeated_paths(self):
        prefix = self.root / 'toolchain'
        (prefix / 'lib/lean').mkdir(parents=True)
        dependency = self.root / '.lake/packages/dep/.lake/build/lib/lean'
        dependency.mkdir(parents=True)
        packages = [{'name': 'dep'}]
        valid = os.pathsep.join([str(prefix / 'lib/lean'), str(dependency)])
        self.assertEqual(len(verify.external_paths(self.root, prefix, packages, valid)), 2)
        for invalid in [valid + os.pathsep, valid + os.pathsep + str(self.root),
                        valid + os.pathsep + str(dependency), str(dependency)]:
            with self.subTest(path=invalid):
                with self.assertRaises(ValueError):
                    verify.external_paths(self.root, prefix, packages, invalid)

    def test_checkout_pin_dirty_and_wrong_root_fail(self):
        directory = self.root / '.lake/packages/dep'; directory.mkdir(parents=True)
        packages = [{'name': 'dep', 'rev': 'a' * 40}]
        for values in [[str(directory), 'b' * 40, ''], [str(directory), 'a' * 40, ' M source.lean'],
                       [str(self.root)]]:
            with mock.patch.object(verify, 'capture', side_effect=values):
                with self.assertRaises(ValueError):
                    verify.check_packages(self.root, packages, {})

    def test_duplicate_or_unfixed_dependency_lock_fails(self):
        valid = {'name': 'dep', 'rev': 'a' * 40, 'type': 'git', 'subDir': None}
        for packages in [[valid, valid], [{**valid, 'rev': 'main'}], [{**valid, 'name': '../dep'}]]:
            (self.root / 'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages', 'packages': packages}))
            with self.assertRaises(ValueError):
                verify.locked_packages(self.root)



class EmptyLibraryTests(TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name).resolve()
        self.prefix = self.root / 'toolchain'
        self.tool = self.prefix / 'lib/lean'
        self.tool.mkdir(parents=True)
        (self.tool / 'Core.olean').write_bytes(b'core')
        self.checkout = self.root / '.lake/packages/dep'
        self.checkout.mkdir(parents=True)
        self.library = self.checkout / '.lake/build/lib/lean'
        self.packages = [{'name': 'dep'}]
        self.search = os.pathsep.join([str(self.tool), str(self.library)])

    def tearDown(self):
        self.temporary.cleanup()

    def paths(self):
        return verify.external_paths(self.root, self.prefix, self.packages, self.search)

    def test_missing_library_is_empty(self):
        record = verify.external_fingerprint(self.paths())[1]
        self.assertEqual(record['objects'], 0)
        self.assertEqual(record['bytes'], 0)
        self.assertFalse(self.library.exists())

    def test_empty_existing_library_is_empty(self):
        self.library.mkdir(parents=True)
        self.assertEqual(verify.external_fingerprint(self.paths())[1]['objects'], 0)

    def test_new_object_changes_fingerprint(self):
        before = verify.external_fingerprint(self.paths())
        self.library.mkdir(parents=True)
        (self.library / 'Added.olean').write_bytes(b'new')
        self.assertNotEqual(before, verify.external_fingerprint(self.paths()))

    def test_linked_parent_is_rejected(self):
        for depth in range(4):
            with self.subTest(depth=depth):
                path = self.checkout.joinpath(*('.lake', 'build', 'lib', 'lean')[:depth + 1])
                path.parent.mkdir(parents=True, exist_ok=True)
                target = self.root / ('target' + str(depth)); target.mkdir()
                path.symlink_to(target, target_is_directory=True)
                with self.assertRaises(ValueError):
                    self.paths()
                path.unlink()

    def test_non_directory_parent_is_rejected(self):
        (self.checkout / '.lake').write_bytes(b'file')
        with self.assertRaises(ValueError):
            self.paths()

    def test_missing_checkout_is_rejected(self):
        self.checkout.rmdir()
        with self.assertRaises(ValueError):
            self.paths()

    def test_missing_toolchain_library_is_rejected(self):
        (self.tool / 'Core.olean').unlink(); self.tool.rmdir()
        with self.assertRaises(ValueError):
            self.paths()

    def test_empty_toolchain_library_is_rejected(self):
        (self.tool / 'Core.olean').unlink()
        with self.assertRaises(ValueError):
            verify.external_fingerprint(self.paths())

    def test_link_after_path_check_is_rejected(self):
        paths = self.paths()
        (self.checkout / '.lake').symlink_to(self.prefix, target_is_directory=True)
        with self.assertRaises(ValueError):
            verify.external_fingerprint(paths)

if __name__ == '__main__':
    main()
