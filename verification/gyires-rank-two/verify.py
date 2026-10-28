"""Build the complete proof and check its final axiom reports."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time

from check_package import ROOT, build_order, check, check_axioms, digest, require

SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig')


def save(path, data):
    temporary = path.with_name(path.name + '.tmp')
    require(not temporary.exists() and not temporary.is_symlink(), 'A temporary record already exists.')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def clean_environment():
    blocked = ('LEAN_', 'LAKE_', 'GIT_', 'LD_', 'DYLD_')
    result = {key: value for key, value in os.environ.items() if not key.startswith(blocked)}
    result['LEAN_NUM_THREADS'] = '1'
    result['GIT_CONFIG_NOSYSTEM'] = '1'
    result['GIT_CONFIG_GLOBAL'] = os.devnull
    return result


def no_symlinks(path, anchor):
    path, anchor = Path(path), Path(anchor)
    require(path.is_relative_to(anchor), 'A path leaves its permitted directory.')
    for item in (anchor, *[anchor / Path(*path.relative_to(anchor).parts[:i])
                            for i in range(1, len(path.relative_to(anchor).parts) + 1)]):
        require(not item.is_symlink(), 'A verification path is a symbolic link.')


def files_below(root):
    require(root.is_dir() and not root.is_symlink(), 'A required directory is missing or linked.')
    result = []
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'A verification directory contains a symbolic link.')
        require(path.is_file() or path.is_dir(), 'A verification directory contains a special file.')
        if path.is_file():
            result.append(path)
    return sorted(result)


def capture(arguments, root, environment):
    return subprocess.check_output(arguments, cwd=root, env=environment, text=True,
                                   stderr=subprocess.PIPE, timeout=60).strip()


def locked_packages(root):
    lock = json.loads((root / 'lake-manifest.json').read_text())
    require(lock['packagesDir'] == '.lake/packages', 'The package directory differs from the lock.')
    result = lock['packages']
    names = [item['name'] for item in result]
    require(len(names) == len(set(names)) and bool(names), 'The dependency list is empty or repeated.')
    for item in result:
        require(re.fullmatch(r'[A-Za-z0-9_-]+', item['name']) is not None,
                'A dependency name is invalid.')
        require(item['type'] == 'git' and item.get('subDir') is None,
                'The dependency checkout type is unsupported.')
        require(re.fullmatch(r'[0-9a-f]{40}', item['rev']) is not None,
                'A dependency revision is not fixed.')
    return result


def check_packages(root, packages, environment):
    result = []
    for item in packages:
        directory = root / '.lake/packages' / item['name']
        no_symlinks(directory, root)
        require(directory.is_dir(), 'A dependency checkout is missing: ' + item['name'])
        top = capture(['git', 'rev-parse', '--show-toplevel'], directory, environment)
        require(Path(top).resolve() == directory.resolve(), 'A dependency is not its own checkout.')
        revision = capture(['git', 'rev-parse', 'HEAD'], directory, environment)
        changes = capture(['git', 'status', '--porcelain', '--untracked-files=all'], directory, environment)
        require(revision == item['rev'] and not changes,
                'A dependency differs from its locked revision: ' + item['name'])
        result.append({'name': item['name'], 'revision': revision})
    return result



def library_directory(label, directory):
    package = label.startswith('package:')
    anchor = directory.parents[3] if package else directory.parents[1]
    no_symlinks(directory, anchor)
    require(anchor.is_dir(), 'A dependency checkout or toolchain is missing.')
    for path in (anchor, *[anchor / Path(*directory.relative_to(anchor).parts[:i])
                          for i in range(1, len(directory.relative_to(anchor).parts) + 1)]):
        require(not path.exists() or path.is_dir(), 'A library path contains a non-directory.')
    require(package or directory.is_dir(), 'The toolchain library directory is missing.')
    return directory.is_dir()


def external_paths(root, prefix, packages, lake_paths):
    known = {'toolchain': prefix / 'lib/lean'}
    known.update({'package:' + item['name']: root / '.lake/packages' / item['name'] /
                  '.lake/build/lib/lean' for item in packages})
    for label, path in known.items():
        no_symlinks(path, prefix if label == 'toolchain' else root)
        library_directory(label, path)
    reverse = {str(path.resolve()): label for label, path in known.items()}
    require(len(reverse) == len(known), 'Two dependency paths resolve to the same directory.')
    result = []
    seen = set()
    for item in lake_paths.split(os.pathsep):
        require(bool(item), 'Lake returned an empty library search path.')
        path = Path(item) if Path(item).is_absolute() else root / item
        # The ordinary project build is excluded from the compiler search path.
        if path.absolute() == root / '.lake/build/lib/lean':
            no_symlinks(path, root)
            continue
        label = reverse.get(str(path.absolute()))
        require(label is not None, 'Lake returned a library path outside the locked dependencies.')
        require(label not in seen, 'Lake returned a repeated dependency path.')
        seen.add(label)
        result.append((label, known[label]))
    require(seen == set(known), 'Lake did not return every locked dependency library.')
    return result


def external_fingerprint(paths):
    result = []
    for label, directory in paths:
        files = files_below(directory) if library_directory(label, directory) else []
        total = hashlib.sha256()
        count = size = 0
        for path in files:
            name = path.relative_to(directory).as_posix()
            if not name.endswith(SUFFIXES):
                continue
            record = [name, path.stat().st_size, digest(path)]
            total.update(json.dumps(record, separators=(',', ':')).encode() + b'\n')
            count += 1
            size += path.stat().st_size
        require(label.startswith('package:') or count > 0, 'The toolchain has no Lean objects.')
        result.append({'root': label, 'objects': count, 'bytes': size, 'sha256': total.hexdigest()})
    return result


def reject_default_outputs(root):
    directory = root / '.lake/build/lib/lean'
    no_symlinks(directory, root)
    if directory.exists():
        require(not files_below(directory), 'The ordinary project build contains stale outputs.')


def bundle(build, name):
    stem = name.replace('.', '/')
    return {stem + suffix: digest(build / (stem + suffix)) for suffix in SUFFIXES
            if (build / (stem + suffix)).is_file()}


def validate_state(work, modules, order, context):
    state = json.loads((work / 'state.json').read_text())
    require(state.get('context') == context, 'The saved verification context is stale.')
    records = state['records']
    names = [entry['module'] for entry in records]
    require(names == order[:len(names)], 'The saved module records are not a complete prefix.')
    allowed = {'state.json', 'result.json', 'attempt.log'}
    prior = {}
    for entry in records:
        name = entry['module']
        objects = bundle(work / 'build', name)
        require(name.replace('.', '/') + '.olean' in objects, 'A checked object is missing.')
        require(entry['source_sha256'] == modules[name]['sha256'] and entry['objects'] == objects,
                'A saved source or object record is stale: ' + name)
        require(entry['exit_code'] == 0, 'A saved compiler command failed.')
        expected_dependencies = {dep: prior[dep] for dep in sorted(modules[name]['imports']) if dep in modules}
        require(entry['dependencies'] == expected_dependencies, 'A project dependency record is stale.')
        log = work / 'logs' / (name.replace('.', '/') + '.log')
        require(log.is_file() and digest(log) == entry['log_sha256'], 'A compiler log is missing or stale.')
        check_log(log)
        allowed.add(log.relative_to(work).as_posix())
        allowed.update('build/' + path for path in objects)
        prior[name] = objects
    actual = {path.relative_to(work).as_posix() for path in files_below(work)}
    require(actual <= allowed and {'state.json', 'result.json'} <= actual,
            'The verification directory contains unrecorded or unexpected files.')
    return state


def check_log(path):
    require(not re.search(r'\b(?:warning|error)\s*:|sorryAx', path.read_text(), re.I),
            'A compiler log contains an error, warning, or proof hole.')


def group_exists(identifier):
    try:
        os.killpg(identifier, 0)
        return True
    except ProcessLookupError:
        return False


def stop_group(process):
    if group_exists(process.pid):
        os.killpg(process.pid, signal.SIGTERM)
        limit = time.monotonic() + 3
        while group_exists(process.pid) and time.monotonic() < limit:
            process.poll()
            time.sleep(0.05)
        if group_exists(process.pid):
            os.killpg(process.pid, signal.SIGKILL)
    process.wait()



def compile_process(arguments, root, environment, log, timeout):
    started = time.monotonic()
    peak = 0
    with log.open('w') as stream:
        process = subprocess.Popen(arguments, cwd=root, env=environment, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                require(time.monotonic() - started < timeout, 'The compiler time limit was exceeded.')
                rows = subprocess.check_output(['ps', '-axo', 'pgid=,rss='], text=True).splitlines()
                rss = sum(int(fields[1]) for row in rows if len(fields := row.split()) == 2
                          and int(fields[0]) == process.pid)
                peak = max(peak, rss)
                require(rss <= 8 * 1024 * 1024, 'The compiler process group exceeded 8 GiB.')
                time.sleep(0.2)
            require(process.returncode == 0, 'A Lean compiler command failed.')
            return {'exit_code': 0, 'seconds': time.monotonic() - started, 'peak_rss_kib': peak}
        finally:
            # Stop any child that remains after the main compiler exits.
            stop_group(process)


def discover(root, packages, environment):
    pins = check_packages(root, packages, environment)
    prefix_text = capture(['lake', 'env', 'lean', '--print-prefix'], root, environment)
    prefix = Path(prefix_text)
    require(prefix.is_absolute() and prefix.resolve() == prefix, 'The toolchain prefix is not a direct absolute path.')
    lean = prefix / 'bin/lean'
    no_symlinks(lean, prefix)
    version = capture([str(lean), '--version'], root, environment)
    match = re.match(r'^Lean \(version ([^,]+),', version)
    require(match is not None and match[1] == '4.35.0', 'The compiler version differs from the package.')
    path_text = capture(['lake', 'env', 'printenv', 'LEAN_PATH'], root, environment)
    paths = external_paths(root, prefix, packages, path_text)
    reject_default_outputs(root)
    return lean, paths, pins, version


def run(root=ROOT, resume=False, max_seconds=None, module_timeout=600):
    root = Path(root).absolute()
    require(root.resolve() == root, 'The package directory contains a symbolic link.')
    work = root / '.verification'
    no_symlinks(work, root)
    if work.exists():
        require(resume, 'The verification directory exists. Use --resume to check its records.')
        files_below(work)
        save(work / 'result.json', {'complete': False, 'phase': 'validation_started'})
    else:
        require(not resume, 'There is no saved verification to resume.')
        work.mkdir()
        save(work / 'result.json', {'complete': False, 'phase': 'validation_started'})
    deadline = None if max_seconds is None else time.monotonic() + max_seconds
    try:
        modules, expected = check(root)
        order = build_order(modules)
        entry = json.loads((root / 'sources.json').read_text())['entry_module']
        packages = locked_packages(root)
        environment = clean_environment()
        lean, paths, pins, version = discover(root, packages, environment)
        external = external_fingerprint(paths)
        context = {'format_version': 1, 'manifest_sha256': digest(root / 'manifest.json'),
                   'source_manifest_sha256': digest(root / 'sources.json'),
                   'verifier_sha256': digest(root / 'verify.py'), 'compiler_sha256': digest(lean),
                   'compiler_version': version, 'dependency_revisions': pins,
                   'dependency_objects': external, 'search_roots': ['project'] + [label for label, _ in paths]}
        build = work / 'build'
        environment['LEAN_PATH'] = os.pathsep.join([str(build), *[str(path) for _, path in paths]])
        if resume:
            state = validate_state(work, modules, order, context)
        else:
            state = {'context': context, 'records': []}
            save(work / 'state.json', state)
        pending = work / 'pending'
        for name in order[len(state['records']):]:
            if deadline is not None:
                require(deadline - time.monotonic() > 5, 'The verification time limit was reached. Resume to continue.')
            timeout = module_timeout if deadline is None else min(module_timeout, deadline - time.monotonic() - 3)
            source = root / modules[name]['path']
            require(digest(source) == modules[name]['sha256'], 'A source changed before compilation.')
            pending.mkdir(exist_ok=True)
            require(not files_below(pending), 'The pending output directory is not empty.')
            stem = name.replace('.', '/')
            output = pending / (stem + '.olean')
            output.parent.mkdir(parents=True, exist_ok=True)
            log = work / 'attempt.log'
            print('Checking ' + name, flush=True)
            try:
                evidence = compile_process([str(lean), '-j1', '-M8192', '-DwarningAsError=true', '-R', 'src',
                                            '-o', str(output), modules[name]['path']], root, environment, log, timeout)
                require(digest(source) == modules[name]['sha256'], 'A source changed during compilation.')
                check_log(log)
                objects = bundle(pending, name)
                require(stem + '.olean' in objects, 'The compiler did not produce its required object.')
                actual = {path.relative_to(pending).as_posix() for path in files_below(pending)}
                require(actual == set(objects), 'The compiler produced an unexpected output.')
                dependencies = {dep: bundle(build, dep) for dep in sorted(modules[name]['imports']) if dep in modules}
                for relative in objects:
                    destination = build / relative
                    require(not destination.exists(), 'A stale project object already exists.')
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    (pending / relative).replace(destination)
                final_log = work / 'logs' / (stem + '.log')
                final_log.parent.mkdir(parents=True, exist_ok=True)
                log.replace(final_log)
                record = {'module': name, 'source_sha256': modules[name]['sha256'], 'objects': objects,
                          'dependencies': dependencies, 'log_sha256': digest(final_log), **evidence}
                state['records'].append(record)
                save(work / 'state.json', state)
            finally:
                shutil.rmtree(pending)
        check(root)
        require(digest(root / 'manifest.json') == context['manifest_sha256']
                and digest(root / 'sources.json') == context['source_manifest_sha256']
                and digest(root / 'verify.py') == context['verifier_sha256'],
                'The package or verifier changed during verification.')
        require(digest(lean) == context['compiler_sha256'], 'The compiler changed during verification.')
        require(check_packages(root, packages, environment) == pins, 'The dependency revisions changed.')
        require(external_fingerprint(paths) == external, 'The dependency objects changed during verification.')
        reject_default_outputs(root)
        validate_state(work, modules, order, context)
        require(len(state['records']) == len(modules), 'The proof module coverage is incomplete.')
        axiom_log = work / 'logs' / (entry.replace('.', '/') + '.log')
        check_axioms(axiom_log, expected)
        result = {'complete': True, 'modules': len(modules), 'final_axiom_reports': len(expected['theorems']),
                  'axiom_log': axiom_log.relative_to(work).as_posix(), 'axiom_log_sha256': digest(axiom_log),
                  'state_sha256': digest(work / 'state.json'), 'context': context}
        save(work / 'result.json', result)
        print('All proof modules and final axiom reports passed.')
        return result
    except BaseException:
        save(work / 'result.json', {'complete': False, 'phase': 'stopped'})
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resume', action='store_true', help='Check saved records and continue the build.')
    parser.add_argument('--max-seconds', type=int, help='Limit this run. Resume the checked prefix later.')
    args = parser.parse_args()
    require(args.max_seconds is None or args.max_seconds >= 10, 'The time limit must be at least ten seconds.')
    signal.signal(signal.SIGTERM, lambda _sig, _frame: (_ for _ in ()).throw(KeyboardInterrupt()))
    run(resume=args.resume, max_seconds=args.max_seconds)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError, KeyboardInterrupt) as error:
        print(str(error) or 'Verification was interrupted.', file=sys.stderr)
        raise SystemExit(1)
