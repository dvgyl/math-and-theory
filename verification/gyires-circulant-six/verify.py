from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import threading
import time


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def imported_modules(path):
    result = []
    for line in path.read_text().splitlines():
        match = re.fullmatch(r'(?:public\s+)?import\s+(.+)', line.strip())
        if match:
            result.extend(match[1].split())
    return result


def check_build_namespace(build, module_names):
    suffixes = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig')
    allowed = {name.replace('.', '/') + suffix for name in module_names for suffix in suffixes}
    if build.is_symlink():
        raise ValueError('The build directory is a symbolic link.')
    for path in build.rglob('*'):
        if path.is_symlink():
            raise ValueError('The build directory contains a symbolic link.')
        if path.is_file() and path.relative_to(build).as_posix() not in allowed:
            raise ValueError('The build directory contains an unlisted object or file.')


def final_axiom_audit(source, log):
    names = {
        'strong_margin', 'sorted_margin', 'sorted_gyires_margin', 'strong_inequality',
        'strong_equality', 'gyires', 'gyires_equality', 'gyires_doubly_stochastic',
        'margin_coefficient_le', 'normalized_margin_coefficient_le',
    }
    expected = {'MathAndTheory.Gyires.CirculantSix.' + name for name in names}
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if len(re.findall(r'^example\b', source.read_text(), re.M)) != 5:
        raise ValueError('The direct statement checks do not have the expected coverage.')
    reports = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, log.read_text(), re.S):
        if match[1] in reports:
            raise ValueError('The final log has a duplicate axiom report.')
        axioms = {value.strip() for value in (match[2] or '').split(',') if value.strip()}
        if not axioms <= allowed:
            raise ValueError('An unexpected axiom occurs in the final theorem.')
        reports[match[1]] = sorted(axioms)
    if reports.keys() != expected:
        raise ValueError('The final axiom reports do not cover the exact theorem set.')
    return {'statement_checks': 5, 'axiom_checks': len(reports), 'axioms': reports}


def main():
    parser = argparse.ArgumentParser(description='Verify every source in the certificate manifest.')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--jobs', type=int, choices=(1, 2), default=1)
    parser.add_argument('--memory-mib', type=int, choices=(2048, 4096), default=4096)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    rss_limit_mib = 2048 if args.memory_mib == 2048 else 5120
    verifier_path = Path(__file__).resolve()
    verifier_sha = digest(verifier_path)
    root = args.root.resolve()
    source = root / 'sources'
    work = root / '.verification'
    build = work / 'build'
    logs = work / 'logs'
    if work.is_symlink() or build.is_symlink() or logs.is_symlink():
        raise ValueError('A verification directory is a symbolic link.')
    if args.resume and work.exists():
        save(work / 'result.json', {'complete': False, 'phase': 'validation_started'})
    manifest_path = root / 'source-manifest.json'
    manifest_sha = (root / 'source-manifest.sha256').read_text().split()[0]
    if digest(manifest_path) != manifest_sha:
        raise ValueError('The source manifest hash does not match.')
    manifest = json.loads(manifest_path.read_text())
    if manifest['root_module'] != 'SixTheoremChecks':
        raise ValueError('The source manifest has an unexpected root module.')
    modules = {entry['module']: entry for entry in manifest['sources']}
    if len(modules) != len(manifest['sources']) or len(modules) != manifest['source_count']:
        raise ValueError('The source manifest has duplicate or missing modules.')
    if manifest['root_module'] not in modules:
        raise ValueError('The root module is missing.')
    paths = set()
    for name, entry in modules.items():
        relative = Path(entry['path'])
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('A source path leaves the source directory.')
        if relative.as_posix() != name.replace('.', '/') + '.lean':
            raise ValueError('A source path does not match its module name.')
        path = source / relative
        if digest(path) != entry['sha256'] or path.stat().st_size != entry['bytes']:
            raise ValueError('A source file does not match its manifest: ' + name)
        if imported_modules(path) != entry['imports']:
            raise ValueError('An import list does not match its source: ' + name)
        paths.add(relative.as_posix())
    actual_paths = {path.relative_to(source).as_posix() for path in source.rglob('*.lean')}
    if paths != actual_paths:
        raise ValueError('The manifest does not cover the exact source file set.')
    if sum(entry['bytes'] for entry in modules.values()) != manifest['source_bytes']:
        raise ValueError('The source byte count does not match.')
    dependencies = {name: set(entry['imports']) & modules.keys() for name, entry in modules.items()}
    reached = set()
    visiting = set()

    def visit(name):
        if name in visiting:
            raise ValueError('The source imports contain a cycle.')
        if name in reached:
            return
        visiting.add(name)
        for dependency in dependencies[name]:
            visit(dependency)
        visiting.remove(name)
        reached.add(name)

    visit(manifest['root_module'])
    if reached != modules.keys():
        raise ValueError('The manifest contains sources outside the root dependency graph.')
    if work.exists() and not args.resume:
        raise ValueError('The verification directory exists. Use --resume to check its records.')
    build.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    save(work / 'result.json', {'complete': False, 'phase': 'verification_started'})
    check_build_namespace(build, modules)

    lake_environment = dict(os.environ)
    lake_environment.pop('LEAN_PATH', None)

    def lake_output(*arguments):
        return subprocess.check_output(['lake', 'env', *arguments], cwd=root,
                                       env=lake_environment, text=True).strip()

    prefix = Path(lake_output('lean', '--print-prefix'))
    lean = prefix / 'bin' / 'lean'
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    version_match = re.match(r'^Lean \(version ([^,]+),', version)
    if version_match is None or version_match[1] != manifest['lean_version']:
        raise ValueError('The Lean version does not match the manifest.')
    compiler_sha = digest(lean)
    package_paths = lake_output('printenv', 'LEAN_PATH').split(os.pathsep)
    environment = dict(lake_environment)
    environment['LEAN_NUM_THREADS'] = '1'
    known_paths = {(prefix / 'lib/lean').resolve(): 'toolchain'}
    package_names = set()
    for package in manifest['packages']:
        name = package['name']
        if name in ('.', '..') or Path(name).name != name or name in package_names:
            raise ValueError('A package name is invalid or repeated.')
        package_names.add(name)
        known_paths[(root / '.lake/packages' / name / '.lake/build/lib/lean').resolve()] = 'package:' + name
    external_paths = []
    external_roots = []
    for item in package_paths:
        if not item:
            raise ValueError('Lake returned an empty library search path.')
        path = (root / item).resolve()
        if path == (root / '.lake/build/lib/lean').resolve():
            continue
        if path not in known_paths:
            raise ValueError('Lake returned a library path outside the pinned packages and toolchain.')
        if str(path) in external_paths:
            continue
        external_paths.append(str(path))
        external_roots.append(known_paths[path])
    if set(external_roots) != set(known_paths.values()):
        raise ValueError('Lake did not return every pinned library search path.')
    environment['LEAN_PATH'] = os.pathsep.join([str(build), *external_paths])

    def check_packages():
        result = []
        for package in manifest['packages']:
            if package['name'] in ('.', '..') or Path(package['name']).name != package['name']:
                raise ValueError('A package name is not a directory name.')
            directory = root / '.lake/packages' / package['name']
            revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
            changes = subprocess.check_output(
                ['git', 'status', '--porcelain', '--untracked-files=no'], cwd=directory, text=True)
            if revision != package['rev'] or changes:
                raise ValueError('A dependency differs from its pinned revision: ' + package['name'])
            result.append({'name': package['name'], 'revision': revision})
        return result

    package_records = check_packages()
    stopped = threading.Event()
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, lambda _sig, _frame: stopped.set())

    def output_paths(name):
        relative = Path(name.replace('.', '/'))
        return (build / relative.with_suffix('.olean'),
                logs / relative.with_suffix('.json'), logs / relative.with_suffix('.log'))

    def module_outputs(name):
        obj, _, _ = output_paths(name)
        return [obj, obj.with_suffix('.olean.private'), obj.with_suffix('.olean.server'),
                obj.with_suffix('.ilean'), obj.with_suffix('.ir'), obj.with_suffix('.ir.sig')]

    def object_bundle(name):
        return {path.relative_to(build).as_posix(): digest(path) for path in module_outputs(name) if path.exists()}

    def dependency_objects(name):
        return {dependency: object_bundle(dependency) for dependency in sorted(dependencies[name])}

    def reusable(name):
        obj, record_path, log = output_paths(name)
        if not all(path.is_file() for path in (obj, record_path, log)):
            return False
        record = json.loads(record_path.read_text())
        return (record.get('exit_code') == 0 and record.get('timeout') is False
                and record.get('memory_limit') is False and record.get('interrupted') is False
                and record.get('source_sha256') == modules[name]['sha256']
                and record.get('source_sha256_after') == modules[name]['sha256']
                and record.get('object_sha256') == digest(obj)
                and record.get('objects') == object_bundle(name)
                and record.get('log_sha256') == digest(log)
                and record.get('compiler_sha256') == compiler_sha
                and record.get('verifier_sha256') == verifier_sha
                and record.get('external_path_policy') == 'pinned-package-paths-v1'
                and record.get('external_search_roots') == external_roots
                and record.get('source_manifest_sha256') == manifest_sha
                and record.get('dependencies') == dependency_objects(name))

    def compile_one(name):
        entry = modules[name]
        path = source / entry['path']
        obj, record_path, log = output_paths(name)
        obj.parent.mkdir(parents=True, exist_ok=True)
        log.parent.mkdir(parents=True, exist_ok=True)
        before = digest(path)
        if before != entry['sha256']:
            raise ValueError('A source changed before compilation: ' + name)
        for previous_output in module_outputs(name):
            previous_output.unlink(missing_ok=True)
        arguments = ['-M' + str(args.memory_mib), '-j1', '-DmaxErrors=1', '--error=warning', '-R', 'sources',
                     '-o', obj.relative_to(root).as_posix(), path.relative_to(root).as_posix()]
        started = time.monotonic()
        max_rss = 0
        timeout = memory_limit = interrupted = False
        with log.open('w') as stream:
            process = subprocess.Popen([str(lean), *arguments], cwd=root, env=environment,
                                       stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                while process.poll() is None:
                    rows = subprocess.check_output(['ps', '-axo', 'pid,pgid,rss'], text=True).splitlines()[1:]
                    rss = sum(int(values[2]) for row in rows if len(values := row.split()) == 3
                              and int(values[1]) == process.pid)
                    max_rss = max(max_rss, rss)
                    timeout = time.monotonic() - started > 600
                    memory_limit = rss > rss_limit_mib * 1024
                    interrupted = stopped.is_set()
                    if timeout or memory_limit or interrupted:
                        break
                    try:
                        process.wait(timeout=1)
                    except subprocess.TimeoutExpired:
                        pass
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
            code = process.wait()
        after = digest(path)
        if after != before:
            code = 97
        record = {'module': name, 'exit_code': code, 'timeout': timeout, 'memory_limit': memory_limit,
                  'interrupted': interrupted, 'source_sha256': before, 'source_sha256_after': after,
                  'object_sha256': digest(obj) if code == 0 and obj.exists() else None,
                  'objects': object_bundle(name) if code == 0 else {}, 'log_sha256': digest(log),
                  'compiler_sha256': compiler_sha, 'source_manifest_sha256': manifest_sha,
                  'verifier_sha256': verifier_sha, 'external_path_policy': 'pinned-package-paths-v1',
                  'external_search_roots': external_roots,
                  'lean_arguments': arguments, 'wall_seconds': time.monotonic() - started,
                  'lean_allocation_mib': args.memory_mib, 'group_rss_limit_mib': rss_limit_mib,
                  'max_group_rss_kib': max_rss, 'dependencies': dependency_objects(name)}
        save(record_path, record)
        print(json.dumps({'module': name, 'exit_code': code, 'wall_seconds': record['wall_seconds']}), flush=True)
        return record

    finished = set()
    remaining = set(modules)
    active = {}
    failure = None
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while remaining or active:
            if stopped.is_set():
                failure = {'error': 'Verification was interrupted.'}
            ready = [name for name in modules if name in remaining and dependencies[name] <= finished]
            for name in ready:
                if failure is not None or len(active) >= args.jobs:
                    break
                remaining.remove(name)
                if args.resume and reusable(name):
                    finished.add(name)
                else:
                    active[pool.submit(compile_one, name)] = name
            if not active:
                if failure is not None:
                    break
                if remaining and not ready:
                    raise ValueError('The source dependency graph cannot advance.')
                continue
            done, _ = wait(active, timeout=1, return_when=FIRST_COMPLETED)
            for future in done:
                name = active.pop(future)
                try:
                    record = future.result()
                except Exception as error:
                    failure = {'module': name, 'error': str(error)}
                    continue
                if record['exit_code'] != 0 or record['timeout'] or record['memory_limit'] or record['interrupted']:
                    failure = {'module': name, 'exit_code': record['exit_code']}
                else:
                    finished.add(name)
            if failure is not None and not active:
                break
    changed = [name for name, entry in modules.items() if digest(source / entry['path']) != entry['sha256']]
    if changed:
        failure = {'changed_sources': changed}
    try:
        check_build_namespace(build, modules)
    except ValueError as error:
        failure = {'error': str(error)}
    changed_objects = [name for name in finished if not reusable(name)]
    if changed_objects:
        failure = {'changed_objects': changed_objects}
    if digest(manifest_path) != manifest_sha or digest(lean) != compiler_sha:
        failure = {'error': 'The manifest or compiler changed during verification.'}
    if digest(verifier_path) != verifier_sha:
        failure = {'error': 'The verifier changed during verification.'}
    if check_packages() != package_records:
        failure = {'error': 'A pinned package changed during verification.'}
    audit = None
    if failure is None and not remaining:
        try:
            audit = final_axiom_audit(source / modules['SixTheoremChecks']['path'],
                                      output_paths('SixTheoremChecks')[2])
        except ValueError as error:
            failure = {'error': str(error)}
    result = {'complete': failure is None and not remaining and len(finished) == len(modules),
              'failure': failure, 'finished': len(finished), 'expected': len(modules),
              'source_manifest_sha256': manifest_sha, 'lean_version': version,
              'compiler_sha256': compiler_sha, 'packages': package_records,
              'verifier_sha256': verifier_sha, 'external_path_policy': 'pinned-package-paths-v1',
              'external_search_roots': external_roots,
              'jobs': args.jobs, 'wall_seconds': time.monotonic() - started, 'audit': audit}
    save(work / 'result.json', result)
    print(json.dumps(result), flush=True)
    return 0 if result['complete'] else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        raise SystemExit(str(error))
