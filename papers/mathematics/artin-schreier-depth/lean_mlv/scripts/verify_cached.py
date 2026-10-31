#!/usr/bin/env python3
"""Fresh serial verification against a pinned, already built mathlib checkout.

Every root and vendored NYLL production Lean module is compiled into a new isolated directory.
Existing project oleans never appear on LEAN_PATH. The generated central audit
checks every declaration by defining module, including private/generated names,
using Lean.collectAxioms. Dependency oleans are pinned/cached, not rebuilt.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from generate_audit import generate, production_modules

LEAN_VERSION = "4.35.0-rc2"
LEAN_COMMIT = "11acb17ec6b07a8f9e9173e6845197929540936b"
MATHLIB_COMMIT = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments_and_strings(source: str) -> str:
    """Keep token positions while ignoring nested Lean comments and strings."""
    result: list[str] = []
    pos = 0
    depth = 0
    in_string = False
    while pos < len(source):
        here = source[pos:pos + 2]
        char = source[pos]
        if depth:
            if here == "/-":
                depth += 1
                result.extend("  ")
                pos += 2
            elif here == "-/":
                depth -= 1
                result.extend("  ")
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif in_string:
            if char == "\\" and pos + 1 < len(source):
                result.extend("  ")
                pos += 2
            elif char == '"':
                in_string = False
                result.append(" ")
                pos += 1
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif here == "/-":
            depth = 1
            result.extend("  ")
            pos += 2
        elif here == "--":
            end = source.find("\n", pos)
            if end < 0:
                result.extend(" " * (len(source) - pos))
                pos = len(source)
            else:
                result.extend(" " * (end - pos))
                pos = end
        elif char == '"':
            in_string = True
            result.append(" ")
            pos += 1
        else:
            result.append(char)
            pos += 1
    if depth or in_string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(result)


def command(args: list[str], cwd: Path, env: dict[str, str] | None = None,
            timeout: int = 60) -> str:
    proc = subprocess.run(args, cwd=cwd, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=timeout, check=False)
    if proc.returncode:
        raise RuntimeError(f"Command failed ({proc.returncode}): {args!r}\n{proc.stdout}")
    return proc.stdout.strip()


def git_pin(path: Path, expected: str) -> dict[str, str]:
    actual = command(["git", "rev-parse", "HEAD"], path)
    if actual != expected:
        raise RuntimeError(f"Wrong Git pin at {path}: {actual}, expected {expected}")
    dirty = command(["git", "status", "--porcelain", "--untracked-files=no"], path)
    if dirty:
        raise RuntimeError(f"Tracked source changes at {path}:\n{dirty}")
    return {"path": str(path), "revision": actual, "tracked_source_clean": "true"}


def production_sources(project: Path) -> dict[str, Path]:
    names = [*production_modules(project), "AxiomAudit"]
    sources = {name: project / (name.replace(".", "/") + ".lean") for name in names}
    if not all(path.is_file() for path in sources.values()):
        raise RuntimeError("Missing production or generated audit source")
    return sources


def module_order(code: dict[str, str]) -> list[str]:
    imports: dict[str, list[str]] = {}
    for name, source in code.items():
        deps: list[str] = []
        for line in source.splitlines():
            match = re.match(r"\s*(?:public\s+)?import\s+(.+?)\s*$", line)
            if match:
                deps.extend(dependency for dependency in match.group(1).split()
                            if dependency in code)
        imports[name] = deps
    result: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(name: str) -> None:
        if name in active:
            raise RuntimeError(f"Import cycle through {name}")
        if name in done:
            return
        active.add(name)
        for dependency in imports[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)
        result.append(name)

    for name in sorted(code):
        visit(name)
    if result[-1] != "AxiomAudit":
        raise RuntimeError("The generated all-module axiom audit must compile last")
    return result


def strip_attributes(source: str) -> str:
    """Blank attribute syntax while preserving newlines for a supplementary scan."""
    result = list(source)
    pos = 0
    while pos < len(source) - 1:
        if source[pos:pos + 2] != "@[":
            pos += 1
            continue
        depth = 1
        start = pos
        pos += 2
        while pos < len(source) and depth:
            if source[pos] == "[":
                depth += 1
            elif source[pos] == "]":
                depth -= 1
            pos += 1
        if depth:
            raise ValueError("Unterminated Lean attribute")
        for index in range(start, pos):
            if result[index] != "\n":
                result[index] = " "
    return "".join(result)


def named_public_declarations(source: str) -> set[str]:
    """Supplementary explicit-name cross-check, never the audit's selection rule.

    This handles attributed declarations, structures/classes/inductives, named
    instances, nested namespaces and sections. Anonymous instances, private
    helpers and generated declarations are covered by the independent full
    environment traversal, not inferred from this textual scan.
    """
    source = strip_attributes(source)
    scopes: list[tuple[str, str]] = []
    names: set[str] = set()
    start = re.compile(
        r"^\s*((?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*)"
        r"(theorem|lemma|def|abbrev|instance|opaque|structure|class|inductive)\s+"
        r"([\w.']+)")
    for line in source.splitlines():
        namespace = re.match(r"\s*namespace\s+([\w.']+)\s*$", line)
        if namespace:
            scopes.append(("namespace", namespace.group(1)))
            continue
        section = re.match(r"\s*(?:noncomputable\s+)?section(?:\s+([\w.']+))?\s*$", line)
        if section:
            scopes.append(("section", section.group(1) or ""))
            continue
        end = re.match(r"\s*end(?:\s+([\w.']+))?\s*$", line)
        if end:
            if scopes:
                scopes.pop()
            continue
        match = start.match(line)
        if not match or "private" in match.group(1).split():
            continue
        name = match.group(3)
        if name[0].isdigit():
            continue
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            namespace_parts = [part for kind, part in scopes if kind == "namespace"]
            full = ".".join([*namespace_parts, name])
        names.add(full)
    return names


def axiom_reports(output: str) -> tuple[dict[str, dict], dict]:
    """Parse only the central audit's JSON lines, with duplicate/missing checks."""
    records: dict[str, dict] = {}
    summaries: list[dict] = []
    for line in output.splitlines():
        if "NTC_AXIOM_DECL " in line:
            record = json.loads(line.split("NTC_AXIOM_DECL ", 1)[1])
            if set(record) != {"module", "name", "kind", "axioms"}:
                raise RuntimeError(f"Malformed declaration audit record: {record!r}")
            if not all(isinstance(record[key], str) for key in ("module", "name", "kind")):
                raise RuntimeError("Non-string audit declaration metadata")
            axioms = record["axioms"]
            if not isinstance(axioms, list) or not all(isinstance(item, str) for item in axioms):
                raise RuntimeError("Malformed axiom array")
            if len(set(axioms)) != len(axioms):
                raise RuntimeError(f"Duplicate axiom in record {record['name']}")
            name = record["name"]
            if name in records:
                raise RuntimeError(f"Duplicate declaration audit record: {name}")
            records[name] = record
        elif "NTC_AXIOM_SUMMARY " in line:
            summaries.append(json.loads(line.split("NTC_AXIOM_SUMMARY ", 1)[1]))
    if len(summaries) != 1:
        raise RuntimeError(f"Expected one audit summary, found {len(summaries)}")
    if not records:
        raise RuntimeError("No environment declaration audit records were emitted")
    return records, summaries[0]


def validate_axiom_coverage(records: dict[str, dict], summary: dict,
                           modules: list[str], public: dict[str, set[str]]) -> dict:
    if summary.get("schema") != 1 or summary.get("collector") != "Lean.collectAxioms":
        raise RuntimeError("Wrong central axiom-audit schema or collector")
    if summary.get("modules") != modules:
        raise RuntimeError("Audit module inventory disagrees with actual production source files")
    if set(summary.get("allowed_axioms", [])) != ALLOWED_AXIOMS:
        raise RuntimeError("Audit allowlist differs from the verifier allowlist")
    counts = summary.get("counts")
    if not isinstance(counts, dict) or set(counts) != set(modules):
        raise RuntimeError("Audit module-count inventory is incomplete")
    if any(type(count) is not int or count <= 0 for count in counts.values()):
        raise RuntimeError("Production module has an invalid/zero declaration count")
    actual = Counter(record["module"] for record in records.values())
    if dict(actual) != counts:
        raise RuntimeError(f"Audit records do not match all-environment module counts: {actual!r}")
    if summary.get("total") != len(records) or sum(counts.values()) != len(records):
        raise RuntimeError("Audit total does not reconcile with emitted declaration records")
    missing: dict[str, list[str]] = {}
    for module, names in public.items():
        absent = sorted(name for name in names
                        if name not in records or records[name]["module"] != module)
        if absent:
            missing[module] = absent
    if missing:
        raise RuntimeError(f"Source-named public declarations missing from owning module audit: {missing}")
    nonstandard = {name: sorted(set(record["axioms"]) - ALLOWED_AXIOMS)
                   for name, record in records.items()
                   if set(record["axioms"]) - ALLOWED_AXIOMS}
    if nonstandard:
        raise RuntimeError(f"Nonstandard transitive axioms detected: {nonstandard}")
    return {
        "selection": "all environment declarations by defining production module; no blacklist",
        "collector": "Lean.collectAxioms (same collector as #print axioms)",
        "environment_declaration_count": len(records),
        "module_counts": counts,
        "kind_counts": dict(sorted(Counter(record["kind"] for record in records.values()).items())),
        "named_public_source_subset_count": sum(len(names) for names in public.values()),
        "named_public_source_subset": {module: sorted(public[module]) for module in modules},
        "source_scan_role": "supplementary subset cross-check, not the audit selection mechanism",
        "includes_private_generated_and_unnamed": True,
        "summary": summary,
    }


def configure_process_stack(stack_kib: int) -> dict:
    try:
        import resource
    except ImportError:
        return {"supported": False, "lean_thread_stack_kib": stack_kib}
    before = resource.getrlimit(resource.RLIMIT_STACK)
    desired = stack_kib * 1024
    if before[1] != resource.RLIM_INFINITY:
        desired = min(desired, before[1])
    if before[0] != resource.RLIM_INFINITY and before[0] < desired:
        resource.setrlimit(resource.RLIMIT_STACK, (desired, before[1]))
    after = resource.getrlimit(resource.RLIMIT_STACK)
    return {"supported": True, "before_bytes": list(before), "after_bytes": list(after),
            "lean_thread_stack_kib": stack_kib}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-cache", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True,
                        help="Full path to the pinned Lean 4.35.0-rc2 executable")
    parser.add_argument("--packages-root", type=Path,
                        help="Optional directory containing mathlib's pinned transitive packages")
    parser.add_argument("--output", type=Path, help="New directory; must not already exist")
    parser.add_argument("--module-timeout", type=int, default=600)
    parser.add_argument("--lean-stack-kib", type=int, default=65536,
                        help="Lean thread/process stack target; default 64 MiB")
    args = parser.parse_args()
    if args.lean_stack_kib <= 0:
        parser.error("--lean-stack-kib must be positive")
    project = Path(__file__).resolve().parents[1]
    mathlib = args.mathlib_cache.resolve()
    lean = args.lean_bin.resolve()
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=False)
    else:
        builds = project / "verification_runs"
        builds.mkdir(exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix=timestamp + "_", dir=builds))
    report: dict = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "status": "running", "project": str(project), "output": str(output),
        "method": "serialized fresh isolated compilation of every root and vendored Nyll production module",
        "dependency_policy": "pinned cached mathlib/dependency oleans; dependencies not rebuilt",
        "standard_axioms_allowed": sorted(ALLOWED_AXIOMS),
        "production_discovery": "every root *.lean and Nyll/**/*.lean file, plus generated AxiomAudit.lean",
        "modules": [],
    }
    report_file = output / "verification_report.json"

    def save_report() -> None:
        report_file.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    save_report()
    print(f"Verification output: {output}", flush=True)
    try:
        version = command([str(lean), "--version"], project)
        commit = command([str(lean), "--githash"], project)
        if f"version {LEAN_VERSION}," not in version or not commit.startswith(LEAN_COMMIT):
            raise RuntimeError(f"Wrong Lean compiler: {version}; {commit}")
        if (project / "lean-toolchain").read_text().strip() != f"leanprover/lean4:v{LEAN_VERSION}":
            raise RuntimeError("Project lean-toolchain disagrees with the required compiler pin")
        report["lean"] = {"executable": str(lean), "version": version, "commit": commit,
                          "sha256": sha256(lean)}
        report["mathlib"] = git_pin(mathlib, MATHLIB_COMMIT)
        manifest_path = mathlib / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        report["mathlib_manifest_sha256"] = sha256(manifest_path)
        pinned_manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
        expected = {item["name"]: item["rev"] for item in pinned_manifest["packages"]}
        if expected.get("mathlib") != MATHLIB_COMMIT:
            raise RuntimeError("Project manifest has the wrong mathlib pin")
        libraries = [mathlib / ".lake/build/lib/lean"]
        dependencies = []
        for package in manifest["packages"]:
            name, revision = package["name"], package["rev"]
            if expected.get(name) != revision:
                raise RuntimeError(f"Dependency pin disagreement for {name}")
            candidates = ([args.packages_root.resolve() / name] if args.packages_root else []) + [
                mathlib / ".lake/packages" / name, project / ".lake/packages" / name,
                mathlib.parent / name]
            path = next((candidate for candidate in candidates if candidate.is_dir()), None)
            if path is None:
                raise RuntimeError(f"Cannot locate pinned dependency {name}; use --packages-root")
            library = path / ".lake/build/lib/lean"
            if not library.is_dir():
                raise RuntimeError(f"Pinned dependency {name} has no compiled Lean library")
            dependencies.append({"name": name, **git_pin(path, revision),
                                 "compiled_library_present": True})
            libraries.append(library)
        report["dependencies"] = dependencies
        if not libraries[0].is_dir():
            raise RuntimeError("The pinned mathlib checkout has no built Lean library directory")
        core = Path(command([str(lean), "--print-libdir"], project)).resolve()
        if not (core / "Init.olean").is_file():
            raise RuntimeError(f"Missing compiler core library at {core}")
        libraries.append(core)

        modules = generate(project)
        sources = production_sources(project)
        source_hashes = {name: sha256(path) for name, path in sources.items()}
        code = {name: strip_comments_and_strings(path.read_text(encoding="utf-8"))
                for name, path in sources.items()}
        forbidden = []
        for name, text in code.items():
            for match in re.finditer(r"\b(sorry|admit|axiom|unsafe|partial)\b", text):
                line = text.count("\n", 0, match.start()) + 1
                forbidden.append(f"{name}:{line}: {match.group(1)}")
        if forbidden:
            raise RuntimeError("Forbidden proof token(s): " + "; ".join(forbidden))
        public = {module: named_public_declarations(code[module]) for module in modules}
        report["production_modules"] = modules
        report["source_scan"] = {"forbidden_tokens": [], "source_sha256": source_hashes}
        report["expected_public_endpoints"] = sorted(set().union(*public.values()))
        report["audit_generation"] = {
            "generated_before_snapshot": True,
            "generator_sha256": sha256(project / "scripts/generate_audit.py"),
            "verifier_sha256": sha256(Path(__file__).resolve()),
        }
        order = module_order(code)
        report["module_order"] = order
        snapshot, lib, logs = output / "source", output / "lib", output / "logs"
        snapshot.mkdir()
        lib.mkdir()
        logs.mkdir()
        for name, source in sources.items():
            destination = snapshot / source.relative_to(project)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, destination)
        config_names = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
        config_hashes = {name: sha256(project / name) for name in config_names}
        for name in config_names:
            shutil.copy2(project / name, snapshot / name)
        (snapshot / "scripts").mkdir()
        for name in ("verify_cached.py", "generate_audit.py"):
            shutil.copy2(project / "scripts" / name, snapshot / "scripts" / name)
        report["configuration_sha256"] = config_hashes
        env = os.environ.copy()
        env.pop("LEAN_SYSROOT", None)
        env["LEAN_PATH"] = os.pathsep.join(str(path) for path in [lib, *libraries])
        report["lean_path"] = env["LEAN_PATH"]
        flags = ["-j", "1", "-s", str(args.lean_stack_kib)]
        report["lean_flags"] = flags
        report["process_stack"] = configure_process_stack(args.lean_stack_kib)
        report["parallelism"] = "one module subprocess at a time, one Lean worker"
        all_output = []
        audit_output = None
        for module in order:
            source = snapshot / (module.replace(".", "/") + ".lean")
            artifact = lib / (module.replace(".", "/") + ".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            argv = ["flock", "/tmp/ntc_lean_compile.lock", str(lean), *flags,
                    f"--root={snapshot}", "-o", str(artifact), str(source)]
            print(f"Compiling {module}", flush=True)
            timed_out = False
            try:
                proc = subprocess.run(argv, cwd=output, env=env, text=True,
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                      timeout=args.module_timeout, check=False)
                stdout, returncode = proc.stdout, proc.returncode
            except subprocess.TimeoutExpired as error:
                timed_out = True
                stdout = error.stdout or ""
                if isinstance(stdout, bytes):
                    stdout = stdout.decode("utf-8", errors="replace")
                returncode = None
            logfile = logs / (module + ".log")
            logfile.write_text(stdout, encoding="utf-8")
            entry = {"name": module, "command": argv, "exit_code": returncode,
                     "timed_out": timed_out, "log": str(logfile.relative_to(output)),
                     "source_sha256": source_hashes[module]}
            if artifact.is_file():
                entry["olean_sha256"] = sha256(artifact)
            report["modules"].append(entry)
            save_report()
            all_output.append(stdout)
            (output / "complete_build.log").write_text("\n".join(all_output), encoding="utf-8")
            if timed_out or returncode:
                if module == "AxiomAudit":
                    # Preserve a completed collector's counterevidence even if
                    # its strict allowlist intentionally made Lean exit nonzero.
                    try:
                        failed_records, failed_summary = axiom_reports(stdout)
                        report["axiom_summary"] = failed_summary
                        report["axiom_declarations"] = failed_records
                        report["nonstandard_axioms"] = {
                            name: sorted(set(record["axioms"]) - ALLOWED_AXIOMS)
                            for name, record in failed_records.items()
                            if set(record["axioms"]) - ALLOWED_AXIOMS
                        }
                    except Exception as audit_error:
                        report["axiom_parse_error"] = str(audit_error)
                    save_report()
                print(stdout, flush=True)
                raise RuntimeError(f"Compilation {'timed out' if timed_out else 'failed'} for {module}")
            if not artifact.is_file():
                raise RuntimeError(f"Compiler reported success without creating {artifact}")
            if module == "AxiomAudit":
                audit_output = stdout
        if audit_output is None:
            raise RuntimeError("Central audit module did not run")
        records, summary = axiom_reports(audit_output)
        report["axiom_coverage"] = validate_axiom_coverage(records, summary, modules, public)
        report["axiom_declarations"] = {name: records[name] for name in sorted(records)}
        report["axiom_audit"] = {name: records[name]["axioms"] for name in sorted(records)}
        report["audited_endpoints"] = sorted(records)
        current = production_sources(project)
        if set(current) != set(sources):
            raise RuntimeError("Production module inventory changed during verification")
        changed = [name for name, path in current.items() if sha256(path) != source_hashes[name]]
        changed += [name for name in config_names if sha256(project / name) != config_hashes[name]]
        if changed:
            raise RuntimeError(f"Source/configuration changed during verification: {changed}")
        generate(project, check=True)
        report["status"] = "passed"
        print(f"PASS: {len(order)} freshly compiled modules; {len(records)} environment declarations "
              f"audited; {sum(map(len, public.values()))} source-named public declarations cross-checked.",
              flush=True)
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save_report()
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
