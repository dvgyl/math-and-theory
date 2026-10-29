#!/usr/bin/env python3
"""Rebuild the pinned local proofs from fresh outputs and check their axioms."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
import tempfile

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
TARGETS = [
    "Fidelity.holevo_le_entropy_rootFidelityMatrix",
    "Fidelity.rootFidelityMatrix_posSemidef",
    "Fidelity.rootFidelityMatrix_trace_one",
    "Fidelity.blockCoherence_normCompression3",
    "Fidelity.relativeEntropy_normCompression3_posDef",
    "Fidelity.entropy_entryAbs_three_posDef",
    "Fidelity.relativeEntropy_internalPinch_le",
    "Fidelity.nuclear_eq_traceNorm",
]


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def fingerprint(files):
    return {name: sha(path) for name, path in sorted(files.items())}


def binding(snapshot):
    return hashlib.sha256(json.dumps(snapshot, sort_keys=True).encode()).hexdigest()


def local_sources(output):
    return fingerprint({p.name: p for p in ROOT.iterdir()
                        if p.is_file() and p.resolve() != output.resolve()
                        and p.name != "verification.json"})


def source_code(text):
    result = []
    index = depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
        elif string:
            if text[index] == "\\":
                index += 2
            else:
                if text[index] == '"':
                    string = False
                index += 1
        elif text.startswith("/-", index):
            depth = 1
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif text[index] == '"':
            string = True
            index += 1
        else:
            result.append(text[index])
            index += 1
    if depth or string:
        raise RuntimeError("Unterminated Lean comment or string")
    return "".join(result)


def check_local_sources():
    forbidden = re.compile(r"\b(?:sorry|sorryAx|axiom|native_decide|unsafe)\b|"
                           r"Lean\.ofReduce(?:Bool|Nat)|implemented_by|skipKernel|trustLevel")
    for name in ["QICFoundation.lean", "FullCandidate.lean", "Audit.lean"]:
        if forbidden.search(source_code((ROOT / name).read_text())):
            raise RuntimeError(f"Unaccepted proof construction in {name}")


def dependencies(manifest):
    pins = {}
    for entry in manifest["packages"]:
        package = ROOT / manifest["packagesDir"] / entry["name"]
        head = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"],
                                       text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(package), "status", "--porcelain",
                                        "--untracked-files=all"], text=True)
        if head != entry["rev"] or dirty:
            raise RuntimeError(f"Dependency revision or clean-tree check failed: {entry['name']}")
        pins[entry["name"]] = head
    return pins


def is_object(path):
    name = path.name
    return (name.endswith((".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig",
                           ".so", ".dylib", ".dll")) or ".so." in name)


def external_files(manifest, compiler_prefix):
    files = {}
    for entry in manifest["packages"]:
        name = entry["name"]
        package = ROOT / manifest["packagesDir"] / name
        tracked = subprocess.check_output(["git", "-C", str(package), "ls-files", "-z"],
                                          text=True).split("\0")
        for relative in tracked:
            path = package / relative
            if relative and path.is_file() and (path.suffix == ".lean" or path.name in
                    {"lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"}):
                files[f"source/{name}/{relative}"] = path
        library = package / ".lake/build/lib"
        for path in library.rglob("*"):
            if path.is_file() and is_object(path):
                files[f"object/{name}/{path.relative_to(library)}"] = path
    for path in (compiler_prefix / "lib").rglob("*"):
        if path.is_file() and is_object(path):
            files[f"toolchain/lib/{path.relative_to(compiler_prefix / 'lib')}"] = path
    for path in (compiler_prefix / "src/lean").rglob("*.lean"):
        files[f"toolchain/source/{path.relative_to(compiler_prefix / 'src/lean')}"] = path
    return files


def clear_local_outputs():
    parent = ROOT / ".lake"
    output = parent / "build"
    if parent.is_symlink() or output.is_symlink() or output.resolve() != ROOT / ".lake/build":
        raise RuntimeError("Refusing to clear an output path outside this proof project")
    if 'name = "fidelity_entropy_three"' not in (ROOT / "lakefile.toml").read_text():
        raise RuntimeError("Refusing to clear outputs of a different Lake package")
    if output.exists():
        shutil.rmtree(output)
    if output.exists():
        raise RuntimeError("Local proof outputs are not fresh")


def make_launcher(compiler, prefix, logs, memory_mib, timeout):
    temporary = tempfile.TemporaryDirectory(prefix="fidelity-lean-")
    runtime = Path(temporary.name)
    (runtime / "bin").mkdir()
    for path in prefix.iterdir():
        if path.name != "bin":
            (runtime / path.name).symlink_to(path, target_is_directory=path.is_dir())
    for path in (prefix / "bin").iterdir():
        if path.name != "lean":
            (runtime / "bin" / path.name).symlink_to(path)
    configuration = {"compiler": str(compiler), "memory_mib": memory_mib,
                     "timeout": timeout, "environment": {"LEAN_NUM_THREADS": "1", "LEAN_STACK_SIZE_KB": "65536"}, "metrics": str((logs / "compiler-processes.jsonl").resolve())}
    (runtime / "config.json").write_text(json.dumps(configuration))
    launcher = runtime / "bin/lean"
    launcher.write_text(LAUNCHER)
    launcher.chmod(0o700)
    (logs / "compiler-launcher.py").write_text(LAUNCHER)
    (logs / "compiler-launcher-config.json").write_text(json.dumps(configuration, indent=2) + "\n")
    return temporary, runtime


LAUNCHER = r'''#!/usr/bin/env python3
from pathlib import Path
import fcntl,json,os,resource,subprocess,sys,time
runtime = Path(__file__).resolve().parent.parent
config = json.loads((runtime / "config.json").read_text())
command = [config["compiler"]]
if any(x in sys.argv[1:] for x in ["--version", "--print-prefix", "--githash"]):
    raise SystemExit(subprocess.call(command + sys.argv[1:]))
with (runtime / "compiler.lock").open("a") as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    bound = config["memory_mib"] * 1024 ** 2
    resource.setrlimit(resource.RLIMIT_AS, (bound, bound))
    resource.setrlimit(resource.RLIMIT_CPU, (config["timeout"] + 5, config["timeout"] + 5))
    start = time.monotonic()
    code = subprocess.call(command + ["-j1", "-M8192", "--trust=0"] + sys.argv[1:])
    with open(config["metrics"], "a") as out:
        out.write(json.dumps({"arguments": command + ["-j1", "-M8192", "--trust=0"] + sys.argv[1:],
            "environment": {name: os.environ.get(name) for name in config["environment"]},
            "exit_code": code, "elapsed_seconds": round(time.monotonic() - start, 3),
            "maximum_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}) + "\n")
    raise SystemExit(code)
'''


def protect_output(path):
    if path.is_symlink() or path.suffix != ".json":
        raise RuntimeError("Verification output must be a regular JSON file")
    resolved = path.resolve()
    if resolved == ROOT or ROOT / ".lake" in resolved.parents:
        raise RuntimeError("Verification output cannot replace build inputs or artifacts")
    protected = {p.resolve() for p in ROOT.iterdir() if p.is_file()
                 and p.name != "verification.json"}
    if resolved in protected:
        # A previous receipt can be replaced. Scientific inputs cannot.
        try:
            previous = json.loads(path.read_text())
            is_receipt = isinstance(previous, dict) and previous.get("targets") == TARGETS
        except (OSError, ValueError):
            is_receipt = False
        if not is_receipt:
            raise RuntimeError("Verification output would overwrite a project input")
    critical = {ROOT / n for n in ["lake-manifest.json", "theorem-map.json",
                                  "QICFoundation.sources.json"]}
    if resolved in critical:
        raise RuntimeError("Verification output would overwrite project configuration")


def write_receipt(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=1800,
                        help="Wall-time bound in seconds for each command")
    parser.add_argument("--memory-mib", type=int, default=49152,
                        help="Address-space bound for each compiler process")
    parser.add_argument("--scheduler-memory-mib", type=int, default=65536,
                        help="Separate address-space bound for the Lake scheduler")
    parser.add_argument("--compiler", type=Path,
                        help="Actual compiler binary, for environments with a serial launcher")
    args = parser.parse_args()
    try:
        protect_output(args.output)
    except RuntimeError as error:
        parser.error(str(error))
    result = {"status": "failed", "phase": "preflight", "targets": TARGETS, "commands": []}
    # Invalidate any old success receipt before checking configuration or tools.
    write_receipt(args.output, result)
    if args.timeout < 1 or args.memory_mib < 1024 or args.scheduler_memory_mib < args.memory_mib:
        parser.error("Positive timeout and valid compiler/scheduler memory bounds are required")
    logs = args.log_dir or args.output.with_suffix(".logs")
    try:
        if logs.resolve() == ROOT or logs.resolve() in ROOT.parents or logs.is_symlink():
            raise RuntimeError("Verification logs need a separate directory")
        if ROOT / ".lake" in logs.resolve().parents:
            raise RuntimeError("Verification logs cannot replace build artifacts")
        logs.mkdir(parents=True, exist_ok=True)
    except (RuntimeError, OSError) as error:
        result["error"] = str(error)
        write_receipt(args.output, result)
        return 1
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_STACK_SIZE_KB"] = "65536"
    temporary_launcher = None
    result["phase"] = "verification"

    def run(label, command, reject_warnings=True):
        def limits():
            bound = args.scheduler_memory_mib * 1024 ** 2
            resource.setrlimit(resource.RLIMIT_AS, (bound, bound))
            resource.setrlimit(resource.RLIMIT_CPU, (args.timeout + 5, args.timeout + 5))
        start = time.monotonic()
        child = subprocess.Popen(command, cwd=ROOT, env=env, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 start_new_session=True, preexec_fn=limits)
        timed_out = False
        try:
            text, _ = child.communicate(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                text, _ = child.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                text, _ = child.communicate()
        path = logs / f"{label}.log"
        path.write_text(text)
        with (logs / "actual-commands.jsonl").open("a") as ledger:
            ledger.write(json.dumps({"label": label, "arguments": command,
                                     "exit_code": child.returncode}) + "\n")
        result["commands"].append({"label": label, "arguments": [Path(command[0]).name, *command[1:]],
            "exit_code": child.returncode, "elapsed_seconds": round(time.monotonic() - start, 3),
            "timed_out": timed_out, "wall_time_bound_seconds": args.timeout,
            "scheduler_address_space_bound_mib": args.scheduler_memory_mib,
            "compiler_address_space_bound_mib": args.memory_mib, "log_sha256": sha(path)})
        print(f"{label}: exit {child.returncode}", flush=True)
        if timed_out or child.returncode:
            raise RuntimeError(f"Command failed: {label}; see {path.name}")
        if reject_warnings and re.search(r"(?im)\bwarning(?:\s*:|\s*\[)", text):
            raise RuntimeError(f"Compiler warning: {label}; see {path.name}")
        return text

    try:
        sources_before = local_sources(args.output)
        check_local_sources()
        version = run("compiler-version", ["lake", "env", "lean", "--version"])
        if "4.35.0-rc3" not in version or LEAN_COMMIT not in version:
            raise RuntimeError("Compiler version or commit differs from the published pin")
        prefix_text = run("compiler-prefix", ["lake", "env", "lean", "--print-prefix"])
        compiler = (args.compiler or (Path(prefix_text.strip()) / "bin/lean")).resolve()
        prefix = compiler.parent.parent
        selected_version = run("selected-compiler-version", [str(compiler), "--version"])
        if "4.35.0-rc3" not in selected_version or LEAN_COMMIT not in selected_version:
            raise RuntimeError("Selected compiler binary differs from the published pin")
        compiler_before = sha(compiler)
        temporary_launcher, runtime = make_launcher(compiler, prefix, logs, args.memory_mib, args.timeout)
        env.update(LEAN_SYSROOT=str(runtime), LAKE_OVERRIDE_LEAN="true",
                   PATH=str(runtime / "bin") + os.pathsep + env["PATH"])
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        pins_before = dependencies(manifest)
        # This stage builds dependencies. It is not the fresh local proof replay.
        run("prepare-dependencies", ["lake", "--no-cache", "--fail-fast", "--rehash", "build", "+FullCandidate:deps"])
        dependencies(manifest)
        before = fingerprint(external_files(manifest, prefix))
        (logs / "external-before.json").write_text(json.dumps(before, indent=2) + "\n")
        clear_local_outputs()
        result["local_outputs_absent_before_replay"] = True
        run("fresh-proof", ["lake", "--verbose", "--no-cache", "--fail-fast", "--rehash", "build", "FullCandidate"])
        audit = run("audit", ["lake", "lean", "Audit.lean"])
        found = {}
        for name, text in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
            axioms = {x.strip() for x in text.split(",") if x.strip()}
            if not axioms <= ALLOWED:
                raise RuntimeError(f"Unaccepted logical axiom in {name}: {sorted(axioms - ALLOWED)}")
            found[name] = sorted(axioms)
        if set(TARGETS) - set(found):
            raise RuntimeError(f"Missing axiom audits: {sorted(set(TARGETS) - set(found))}")
        after = fingerprint(external_files(manifest, prefix))
        (logs / "external-after.json").write_text(json.dumps(after, indent=2) + "\n")
        if before != after:
            raise RuntimeError("External source or proof-object closure changed during fresh replay")
        pins_after = dependencies(manifest)
        sources_after = local_sources(args.output)
        if sources_before != sources_after or pins_before != pins_after or compiler_before != sha(compiler):
            raise RuntimeError("Local sources, dependency pins, or compiler changed during verification")
        for module in ["QICFoundation", "FullCandidate"]:
            if not (ROOT / ".lake/build/lib/lean" / f"{module}.olean").is_file():
                raise RuntimeError(f"Missing fresh local proof object: {module}")
        objects = {str(p.relative_to(ROOT / ".lake/build")): p
                   for p in (ROOT / ".lake/build").rglob("*") if p.is_file() and
                   (is_object(p) or p.name.endswith(".setup.json"))}
        sanitized = audit.replace(str(ROOT), ".").replace(str(prefix), "<lean-toolchain>")
        (logs / "audit-public.txt").write_text(sanitized)
        result.update(status="verified", phase="complete", compiler_version=selected_version.strip(),
            compiler_binary_sha256=compiler_before,
            runtime_environment={"LEAN_NUM_THREADS": env["LEAN_NUM_THREADS"],
                                 "LEAN_STACK_SIZE_KB": env["LEAN_STACK_SIZE_KB"]},
            compiler_launcher_sha256=sha(logs / "compiler-launcher.py"),
            compiler_process_metrics_sha256=sha(logs / "compiler-processes.jsonl"),
            package_revisions=pins_after,
            dependency_trees_clean_before_and_after=True,
            external_source_and_object_files=len(before),
            external_before_sha256=binding(before), external_after_sha256=binding(after),
            axiom_audits={name: found[name] for name in TARGETS}, source_sha256=sources_after,
            fresh_local_object_sha256=fingerprint(objects), public_audit_sha256=sha(logs / "audit-public.txt"))
    except (RuntimeError, subprocess.SubprocessError, OSError, ValueError, KeyError, TypeError) as error:
        result["error"] = str(error).replace(str(ROOT), ".")
    finally:
        if temporary_launcher is not None:
            temporary_launcher.cleanup()
    write_receipt(args.output, result)
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    sys.exit(main())
