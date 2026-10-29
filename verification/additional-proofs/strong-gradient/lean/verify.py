#!/usr/bin/env python3
"""Freshly check the local Lean dependency closure of THGStrong.

Requires Python 3.10+, Lean 4.19.0, and the pinned Mathlib checkout with its
ordinary Mathlib/package .olean caches. Existing project .oleans are never
used: source files are copied into a new source-only snapshot and every local
module is rebuilt into a separate fresh library directory.

Example:
  python3 verify.py --lean /path/to/lean-4.19.0/bin/lean \
    --mathlib /path/to/mathlib4 --output /path/to/fresh-check

No network access or package installation is performed. The output includes
source snapshots, per-module logs and hashes, fresh .oleans, a separate theorem
axiom audit, and verification.json. Only exit status 0 with status "verified"
in verification.json is a successful complete check.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from typing import Any

EXPECTED_LEAN_VERSION = "4.19.0"
EXPECTED_MATHLIB_REVISION = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DEFAULT_THEOREMS = [
    "THGStrong.taylor_hendrickx_glineur_conjecture3",
    "THGStrong.taylor_hendrickx_glineur_conjecture3_with_radius",
    "THGStrong.Sharpness.attain_rate",
]
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def remove_comments_and_strings(text: str) -> str:
    """Mask nested Lean comments and strings, preserving line boundaries."""
    result = list(text)
    index = 0
    depth = 0
    in_string = False
    line_comment = False
    while index < len(text):
        char = text[index]
        pair = text[index:index + 2]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                result[index] = " "
            index += 1
        elif depth:
            if pair == "/-":
                result[index:index + 2] = [" ", " "]
                depth += 1
                index += 2
            elif pair == "-/":
                result[index:index + 2] = [" ", " "]
                depth -= 1
                index += 2
            else:
                if char != "\n":
                    result[index] = " "
                index += 1
        elif in_string:
            if char == "\\" and index + 1 < len(text):
                result[index] = " "
                if text[index + 1] != "\n":
                    result[index + 1] = " "
                index += 2
            else:
                if char != "\n":
                    result[index] = " "
                if char == '"':
                    in_string = False
                index += 1
        elif pair == "--":
            result[index:index + 2] = [" ", " "]
            line_comment = True
            index += 2
        elif pair == "/-":
            result[index:index + 2] = [" ", " "]
            depth = 1
            index += 2
        elif char == '"':
            result[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    if depth or in_string:
        raise ValueError("Unterminated Lean comment or string in source snapshot")
    return "".join(result)


def imports_of(source: str) -> list[str]:
    result: list[str] = []
    code = remove_comments_and_strings(source)
    for line in code.splitlines():
        stripped = line.strip()
        if not stripped or stripped == "prelude":
            continue
        match = re.fullmatch(r"(?:public\s+)?import\s+(.+)", stripped)
        if not match:
            break
        for name in match.group(1).split():
            if not MODULE_RE.fullmatch(name):
                raise ValueError(f"Unsupported import syntax: {name!r}")
            result.append(name)
    return result


def check_no_shortcuts(source: str, module: str) -> None:
    code = remove_comments_and_strings(source)
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b"
                           r"|\bLean\.ofReduce(?:Bool|Nat)\b"
                           r"|\bdebug\.skipKernelTC\b")
    match = forbidden.search(code)
    if match:
        line = code.count("\n", 0, match.start()) + 1
        raise ValueError(f"Forbidden proof shortcut in {module}:{line}: {match.group(0)}")


def local_closure(source_root: Path, entry: str, extras: list[str] | None = None) -> tuple[list[str], dict[str, dict[str, Any]]]:
    order: list[str] = []
    records: dict[str, dict[str, Any]] = {}
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise ValueError(f"Cyclic local imports involving {module}")
        if not MODULE_RE.fullmatch(module):
            raise ValueError(f"Invalid module name: {module}")
        path = source_root.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            raise FileNotFoundError(f"Missing local source module {module}: {path}")
        data = path.read_bytes()
        text = data.decode("utf-8")
        check_no_shortcuts(text, module)
        imports = imports_of(text)
        visiting.add(module)
        local = []
        external = []
        for dependency in imports:
            candidate = source_root.joinpath(*dependency.split(".")).with_suffix(".lean")
            if candidate.is_file():
                local.append(dependency)
                visit(dependency)
            elif dependency.split(".")[0] == entry.split(".")[0]:
                raise FileNotFoundError(f"Local import {dependency} has no source file")
            else:
                external.append(dependency)
        visiting.remove(module)
        visited.add(module)
        records[module] = {
            "module": module,
            "original_source": str(path),
            "source_sha256": sha256_bytes(data),
            "source_bytes": len(data),
            "local_imports": local,
            "external_imports": external,
            "data": data,
        }
        order.append(module)

    visit(entry)
    for additional in extras or []:
        visit(additional)
    return order, records


def command_text(command: list[str], cwd: Path | None = None) -> str:
    completed = subprocess.run(command, cwd=cwd, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, check=True)
    return completed.stdout.strip()


def write_report(path: Path, report: dict[str, Any]) -> None:
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def parse_axioms(log: str, theorems: list[str]) -> dict[str, list[str]]:
    results: dict[str, list[str]] = {}
    for name in theorems:
        pattern = re.escape("'" + name + "'") + r"\s+depends on axioms:\s*\[([^\]]*)\]"
        match = re.search(pattern, log, flags=re.DOTALL)
        if match:
            found = [part.strip() for part in match.group(1).split(",") if part.strip()]
        elif re.search(re.escape("'" + name + "'") + r"\s+does not depend on any axioms", log):
            found = []
        else:
            raise ValueError(f"No explicit axiom report found for {name}")
        unexpected = set(found) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Unapproved axioms for {name}: {sorted(unexpected)}")
        results[name] = found
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean", required=True, type=Path, help="Lean 4.19.0 executable")
    parser.add_argument("--mathlib", required=True, type=Path, help="Pinned Mathlib checkout with built package caches")
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parent,
                        help="Directory containing THGStrong/ (default: this script's directory)")
    parser.add_argument("--entry", default="THGStrong", help="Entry module (default: THGStrong)")
    parser.add_argument("--extra-module", action="append", default=[],
                        help="Also rebuild this module and its local dependencies; may be repeated")
    parser.add_argument("--audit-theorem", action="append", default=[],
                        help="Also audit this fully qualified theorem; may be repeated")
    parser.add_argument("--output", type=Path, help="New or empty output directory; never overwrites an existing run")
    parser.add_argument("--timeout", type=float, default=0, help="Seconds per Lean process; zero means no timeout")
    parser.add_argument("--dry-run", action="store_true", help="Print source dependency plan without building or writing files")
    args = parser.parse_args()
    source_root = args.source.resolve()
    mathlib = args.mathlib.resolve()
    lean = args.lean.resolve()
    if not lean.is_file():
        parser.error(f"Lean executable not found: {lean}")
    if not mathlib.is_dir():
        parser.error(f"Mathlib checkout not found: {mathlib}")
    if args.timeout < 0:
        parser.error("--timeout must be nonnegative")
    for name in [args.entry, *args.extra_module, *args.audit_theorem]:
        if not MODULE_RE.fullmatch(name):
            parser.error(f"Invalid Lean identifier: {name}")
    theorem_names = list(dict.fromkeys([*DEFAULT_THEOREMS, *args.audit_theorem]))
    entry_modules = list(dict.fromkeys([args.entry, *args.extra_module]))
    order, sources = local_closure(source_root, args.entry, args.extra_module)
    mathlib_cache = mathlib / ".lake" / "build" / "lib" / "lean"
    if not mathlib_cache.is_dir():
        parser.error(f"Mathlib build cache not found: {mathlib_cache}")
    package_roots = [mathlib / ".lake" / "packages"]
    # Lake project dependencies share .lake/packages with the mathlib checkout.
    # Only recognize that exact layout; never add the project's own build cache.
    if (mathlib.name == "mathlib" and mathlib.parent.name == "packages"
            and mathlib.parent.parent.name == ".lake"):
        package_roots.append(mathlib.parent)
    package_caches = []
    for package_root in package_roots:
        if not package_root.is_dir():
            continue
        for package in package_root.iterdir():
            cache = (package / ".lake" / "build" / "lib" / "lean").resolve()
            if cache.is_dir() and cache != mathlib_cache.resolve() and cache not in package_caches:
                package_caches.append(cache)
    package_caches.sort()
    if args.dry_run:
        print(json.dumps({"status": "not_run", "entry": args.entry,
                          "additional_modules": args.extra_module, "theorems": theorem_names,
                          "module_order": order,
                          "sources": [{key: value for key, value in sources[module].items() if key != "data"}
                                      for module in order],
                          "mathlib_cache": str(mathlib_cache),
                          "package_caches": [str(path) for path in package_caches]},
                         indent=2, ensure_ascii=False))
        return 0
    default_name = "verification_" + dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    output = (args.output if args.output is not None else source_root / default_name).resolve()
    if output.exists() and not output.is_dir():
        parser.error(f"Output path is not a directory: {output}")
    if output.exists() and any(output.iterdir()):
        parser.error(f"Output directory is not empty; choose a fresh path: {output}")
    if output == source_root:
        parser.error("Output directory must be separate from the project source root")
    output.mkdir(parents=True, exist_ok=True)
    snapshot = output / "source"
    library = output / "lib"
    logs = output / "logs"
    for path in (snapshot, library, logs):
        path.mkdir(parents=True)
    report_path = output / "verification.json"
    report: dict[str, Any] = {
        "status": "running", "started_utc": utc_now(), "entry": args.entry,
        "source_root": str(source_root), "source_snapshot": str(snapshot),
        "output_library": str(library), "lean_executable": str(lean),
        "mathlib_checkout": str(mathlib), "expected_lean_version": EXPECTED_LEAN_VERSION,
        "expected_mathlib_revision": EXPECTED_MATHLIB_REVISION,
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "verifier_sha256": sha256_file(Path(__file__).resolve()),
        "fresh_project_build": True, "source_root_oleans_on_search_path": False,
        "module_order": order, "modules": [], "theorems": theorem_names,
        "additional_modules": args.extra_module,
        "source_inventory": [{key: value for key, value in sources[module].items() if key != "data"}
                             for module in order],
    }
    env = os.environ.copy()
    for variable in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(variable, None)
    search_path = [library, mathlib_cache, *package_caches]
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in search_path)
    report["lean_path"] = [str(path) for path in search_path]

    def run_lean(module: str, source: Path, olean: Path, log: Path) -> dict[str, Any]:
        olean.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), "-j1", "--trust=0", "-DwarningAsError=true", "--root=" + str(snapshot), "-o", str(olean), str(source)]
        start = time.monotonic()
        record: dict[str, Any] = {"module": module, "command": command, "started_utc": utc_now(),
                                  "log": str(log.relative_to(output)),
                                  "snapshot_source": str(source.relative_to(output)),
                                  "snapshot_source_sha256": sha256_file(source)}
        with log.open("w", encoding="utf-8") as handle:
            try:
                completed = subprocess.run(command, cwd=output, env=env, stdout=handle,
                                           stderr=subprocess.STDOUT, check=False,
                                           timeout=args.timeout if args.timeout else None,
                                           preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3)))
                record["exit_code"] = completed.returncode
            except subprocess.TimeoutExpired:
                record["exit_code"] = None
                record["timed_out"] = True
        record["finished_utc"] = utc_now()
        record["wall_seconds"] = round(time.monotonic() - start, 6)
        record["log_sha256"] = sha256_file(log)
        record["olean_exists"] = olean.is_file()
        if olean.is_file():
            record["olean"] = str(olean.relative_to(output))
            record["olean_sha256"] = sha256_file(olean)
        return record

    def dependency_fingerprints() -> list[dict[str, Any]]:
        """Fingerprint every source-resolvable external import and its object."""
        roots = [mathlib, *[cache.parents[3] for cache in package_caches]]
        visited: set[str] = set()
        fingerprints: list[dict[str, Any]] = []
        def visit(name: str) -> None:
            if name in visited or name in sources:
                return
            visited.add(name)
            relative = Path(*name.split("."))
            for root in roots:
                source = (root / relative).with_suffix(".lean")
                if source.is_file():
                    obj = (root / ".lake/build/lib/lean" / relative).with_suffix(".olean")
                    if not obj.is_file():
                        raise FileNotFoundError(f"Missing external object for {name}: {obj}")
                    fingerprints.append({"module": name, "package": root.name,
                        "source_sha256": sha256_file(source), "object_sha256": sha256_file(obj)})
                    for imported in imports_of(source.read_text(encoding="utf-8")):
                        visit(imported)
                    return
            # Init, Lean, and Std are supplied by the checked compiler toolchain.
            if name.split(".")[0] not in {"Init", "Lean", "Std"}:
                raise FileNotFoundError(f"Unresolved external source import: {name}")
        for record in sources.values():
            for imported in record["external_imports"]:
                visit(imported)
        return sorted(fingerprints, key=lambda item: item["module"])

    exit_code = 1
    try:
        version = command_text([str(lean), "--version"])
        report["lean_version"] = version
        if not re.search(r"\bversion\s+" + re.escape(EXPECTED_LEAN_VERSION) + r"(?:\b|,)", version):
            raise ValueError(f"Unexpected Lean version: {version}")
        revision = command_text(["git", "-C", str(mathlib), "rev-parse", "HEAD"])
        report["mathlib_revision"] = revision
        if revision != EXPECTED_MATHLIB_REVISION:
            raise ValueError(f"Unexpected Mathlib revision: {revision}")
        dirty = command_text(["git", "-C", str(mathlib), "status", "--porcelain", "--untracked-files=no"])
        report["mathlib_tracked_changes"] = dirty.splitlines() if dirty else []
        if dirty:
            raise ValueError("Pinned Mathlib checkout has tracked changes")
        manifest = mathlib / "lake-manifest.json"
        if manifest.is_file():
            report["mathlib_manifest_sha256"] = sha256_file(manifest)
        report["lean_executable_sha256"] = sha256_file(lean)
        report["external_dependency_fingerprints"] = dependency_fingerprints()
        report["warning_as_error"] = True
        report["memory_limit_bytes"] = 12 * 1024**3
        report["per_process_timeout_seconds"] = args.timeout
        for module in order:
            record = sources[module]
            destination = snapshot.joinpath(*module.split(".")).with_suffix(".lean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(record["data"])
        if list(snapshot.rglob("*.olean")):
            raise RuntimeError("Source snapshot unexpectedly contains object files")
        write_report(report_path, report)
        for module in order:
            record = sources[module]
            source = snapshot.joinpath(*module.split(".")).with_suffix(".lean")
            olean = library.joinpath(*module.split(".")).with_suffix(".olean")
            log = logs / (module.replace(".", "_") + ".log")
            print(f"Checking {module}", flush=True)
            checked = run_lean(module, source, olean, log)
            checked.update({key: value for key, value in record.items() if key != "data"})
            report["modules"].append(checked)
            write_report(report_path, report)
            if checked["exit_code"] != 0 or not checked["olean_exists"] or "warning:" in log.read_text(encoding="utf-8"):
                raise RuntimeError(f"Lean failed for {module}; see {log}")
        audit_source = snapshot / "VerificationAxioms.lean"
        audit_code = "".join("import " + module + "\n" for module in entry_modules) + "\n"
        audit_code += "set_option pp.fullNames true\nset_option pp.universes true\n\n"
        audit_code += "#print THGStrong.gradientRate\n#print THGStrong.Sharpness.NormalizedAttainment\n\n"
        for theorem in theorem_names:
            audit_code += "#print axioms " + theorem + "\n"
            audit_code += "#check @" + theorem + "\n\n"
        audit_source.write_text(audit_code, encoding="utf-8")
        audit_log = logs / "VerificationAxioms.log"
        audit = run_lean("VerificationAxioms", audit_source, library / "VerificationAxioms.olean", audit_log)
        report["axiom_audit"] = audit
        if audit["exit_code"] != 0 or not audit["olean_exists"]:
            raise RuntimeError(f"Final axiom/type audit failed; see {audit_log}")
        report["theorem_axioms"] = parse_axioms(audit_log.read_text(encoding="utf-8"), theorem_names)
        changed = [module for module in order
                   if sha256_file(Path(sources[module]["original_source"])) != sources[module]["source_sha256"]]
        report["sources_changed_during_check"] = changed
        if dependency_fingerprints() != report["external_dependency_fingerprints"]:
            raise RuntimeError("External dependency fingerprints changed during check")
        if sha256_file(Path(__file__).resolve()) != report["verifier_sha256"]:
            raise RuntimeError("Verifier source changed during check")
        report["external_dependencies_unchanged"] = True
        if changed:
            raise RuntimeError("Original sources changed during fresh check: " + ", ".join(changed))
        report["status"] = "verified"
        exit_code = 0
    except KeyboardInterrupt:
        report["status"] = "interrupted"
        report["error"] = "Interrupted by user"
        exit_code = 130
    except Exception as error:
        report["status"] = "failed"
        report["error"] = f"{type(error).__name__}: {error}"
        print(report["error"], file=sys.stderr, flush=True)
    finally:
        report["finished_utc"] = utc_now()
        write_report(report_path, report)
        print(f"Verification status: {report['status']}; report: {report_path}", flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
