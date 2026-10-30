#!/usr/bin/env python3
"""Rebuild the actual theorems into a fresh object directory and audit axioms.

Requires Python's standard library, Lean 4.19.0, and the pinned mathlib project.
By default the dependency project is ./lean; use `lake update` and
`lake exe cache get` there before running this script. Existing project oleans
are never added to the fresh build's import path.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOTS = ["NearSharpFullRank", "CycleCounterexample"]
CENTRAL = [
    "ADMMNearSharpCertificate.C188.certificate",
    "ADMMNearSharpCertificate.C1886.certificate",
    "ADMMNearSharpAllSteps.initialized_admm_objective_converges",
    "ADMMNearSharpAllSteps.rankDeficient_original_admm_converges",
    "ADMMNearSharpAllSteps.fullRank_original_admm_converges",
    "ADMM128Counterexample.counterexample",
]
EXPECTED_MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dependencies(source: Path, roots: list[str]) -> list[str]:
    order: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError("Cyclic local import: " + module)
        path = source / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            raise FileNotFoundError(path)
        visiting.add(module)
        for match in re.finditer(r"^import\s+([^\n]+)", path.read_text(), re.M):
            for dep in match.group(1).split():
                if (source / (dep.replace(".", "/") + ".lean")).is_file():
                    visit(dep)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for root in roots:
        visit(root)
    return order


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dependency-project", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--resume", action="store_true",
                        help="Resume this script's own previously started clean build; reuse only its unchanged completed prefix.")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--skip-import-recheck", action="store_true",
                        help="Diagnostic only: skip explicit central-body rechecking; the fresh source build still kernel-checks every project proof.")
    parser.add_argument("--roots", nargs="+", default=ROOTS)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    source = base / "lean"
    dependency_project = (args.dependency_project or source).resolve()
    if args.output_dir:
        output = args.output_dir.resolve()
        output.mkdir(parents=True, exist_ok=True)
        if any(output.iterdir()) and not args.resume:
            raise RuntimeError("Choose an empty output directory for a clean build: " + str(output))
    else:
        if args.resume:
            raise RuntimeError("--resume requires the original --output-dir")
        parent = base / "verification"
        parent.mkdir(exist_ok=True)
        output = Path(tempfile.mkdtemp(prefix="clean-", dir=parent))
    objects = output / "objects"
    logs = output / "logs"
    objects.mkdir(exist_ok=args.resume)
    logs.mkdir(exist_ok=args.resume)
    manifest = json.loads((source / "lake-manifest.json").read_text())
    mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != EXPECTED_MATHLIB:
        raise RuntimeError("The mathlib pin does not match the reviewed dependency.")
    if (source / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
        raise RuntimeError("Unexpected Lean toolchain")
    mathlib_checkout = dependency_project if (dependency_project / "Mathlib").is_dir() else dependency_project / ".lake/packages/mathlib"
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib_checkout, text=True).strip()
    if revision != EXPECTED_MATHLIB:
        raise RuntimeError("Actual dependency checkout does not match the mathlib pin: " + revision)
    modified = subprocess.check_output(["git", "diff", "--name-only", "HEAD", "--"], cwd=mathlib_checkout, text=True).strip()
    if modified:
        raise RuntimeError("Tracked mathlib sources have local modifications: " + modified)
    actual_dependencies = {}
    package_root = dependency_project / ".lake/packages"
    for package in manifest["packages"]:
        checkout = mathlib_checkout if package["name"] == "mathlib" else package_root / package["name"]
        actual_rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
        actual_dirty = subprocess.check_output(["git", "diff", "--name-only", "HEAD", "--"], cwd=checkout, text=True).strip()
        if actual_rev != package["rev"] or actual_dirty:
            raise RuntimeError("Dependency does not match the clean pinned checkout: " + package["name"])
        actual_dependencies[package["name"]] = {"revision": actual_rev, "tracked_sources_clean": True}
    prefix = subprocess.check_output([args.lake, "env", "lean", "--print-prefix"],
                                     cwd=dependency_project, text=True).strip()
    lean = Path(prefix) / "bin" / "lean"
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if "version 4.19.0," not in version:
        raise RuntimeError("Unexpected compiler: " + version)
    inherited = subprocess.check_output([args.lake, "env", "printenv", "LEAN_PATH"],
                                        cwd=dependency_project, text=True).strip()
    dependency_paths: list[str] = []
    for entry in inherited.split(os.pathsep):
        if not entry:
            continue
        path = (dependency_project / entry).resolve()
        # Exclude only project artifacts, preserving pinned dependency paths.
        if path == (source / ".lake/build/lib/lean").resolve() or path == source:
            continue
        dependency_paths.append(str(path))
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(objects), *dependency_paths])
    order = dependencies(source, args.roots)
    paths = [source / (module.replace(".", "/") + ".lean") for module in order]
    hashes: dict[str, str] = {}
    forbidden = re.compile(r"\b(sorry|admit|native_decide|ofReduceBool|unsafe|skipKernelTC|addDeclWithoutChecking)\b|^\s*axiom\b|\bimplemented_by\b", re.M)
    for path in paths:
        if forbidden.search(path.read_text()):
            raise RuntimeError("Forbidden proof construct in " + str(path))
    result_path = output / "verification.json"
    previous = json.loads(result_path.read_text()) if args.resume else None
    if previous:
        if previous["compiler"] != version or previous["mathlib_revision"] != EXPECTED_MATHLIB:
            raise RuntimeError("Cannot resume a build with a different compiler or dependency pin")
        hashes.update({k:v for k,v in previous["source_sha256"].items()
                       if k in {str(p.relative_to(base)) for p in paths}})
    result = {
        "compiler": version,
        "mathlib_revision": EXPECTED_MATHLIB,
        "dependency_checkouts": actual_dependencies,
        "build_configuration_sha256": {str(p.relative_to(base)): sha(p) for p in
            [source / "lakefile.lean", source / "lake-manifest.json", source / "lean-toolchain",
             source / "KernelBodyAudit.lean", Path(__file__).resolve()]},
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": hashes,
        "roots": args.roots,
        "lean_path": env["LEAN_PATH"],
        "builds": previous["builds"] if previous else [],
        "status": "running",
        "all_sources_built_from_scratch": True,
        "central_body_recheck_requested": not args.skip_import_recheck,
        "central_body_recheck": False,
        "resumed_clean_build": bool(previous),
    }

    def save() -> None:
        result_path.write_text(json.dumps(result, indent=2) + "\n")

    def run(module: str, path: Path, extra: list[str] = []) -> None:
        before_hash = sha(path)
        if forbidden.search(path.read_text()):
            raise RuntimeError("Forbidden proof construct in " + str(path))
        dest = objects / (module.replace(".", "/") + ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module.replace(".", "_") + ".log")
        attempt = 1
        while log.exists():
            attempt += 1
            log = logs / (module.replace(".", "_") + f".attempt{attempt}.log")
        command = [str(lean), "-j", "1", "-DautoImplicit=false", *extra, "--root=" + str(source),
                   "-o", str(dest), str(path)]
        started = time.monotonic()
        print("BUILD", module, flush=True)
        with log.open("w") as stream:
            proc = subprocess.run(command, cwd=source, env=env,
                                  stdout=stream, stderr=subprocess.STDOUT)
        record = {"module": module, "exit_code": proc.returncode,
                  "seconds": time.monotonic() - started, "log": str(log.relative_to(output)),
                  "command": command}
        result["builds"].append(record)
        save()
        if proc.returncode:
            result["status"] = "failed"
            save()
            print(log.read_text()[-12000:], flush=True)
            raise RuntimeError("Build failed: " + module)
        if before_hash != sha(path):
            raise RuntimeError("Source changed while being compiled: " + str(path))
        record["object_sha256"] = sha(dest)
        hashes[str(path.relative_to(base))] = before_hash
        save()
        for match in re.finditer(r"depends on axioms:\s*\[([^]]*)\]", log.read_text()):
            axioms = {s.strip() for s in match.group(1).split(",") if s.strip()}
            if not axioms <= ALLOWED_AXIOMS:
                raise RuntimeError("Unapproved axioms: " + repr(axioms - ALLOWED_AXIOMS))
        print("PASS", module, f"{record['seconds']:.2f}s", flush=True)

    save()
    reuse_prefix = bool(previous)
    last_records = {row["module"]: row for row in result["builds"]}
    for module, path in zip(order, paths):
        if reuse_prefix:
            record = last_records.get(module)
            obj = objects / (module.replace(".", "/") + ".olean")
            if (record and record["exit_code"] == 0 and obj.is_file() and
                hashes.get(str(path.relative_to(base))) == sha(path) and
                ("object_sha256" not in record or record["object_sha256"] == sha(obj))):
                if "object_sha256" not in record:
                    record["object_sha256"] = sha(obj)
                    record["object_hash_first_recorded_on_resume"] = True
                print("REUSE verified clean-build prefix", module, flush=True)
                continue
            reuse_prefix = False
        run(module, path)
    audit = output / "KernelAudit.lean"
    if args.skip_import_recheck:
        audit_text = ("\n".join("import " + m for m in args.roots) + "\n\n" +
                      "\n".join("#print axioms " + c for c in CENTRAL) + "\n")
    else:
        audit_text = (source / "KernelBodyAudit.lean").read_text()
    if forbidden.search(audit_text):
        raise RuntimeError("Forbidden construct in the central body audit")
    audit.write_text(audit_text + "\n" + "\n".join("#check " + c for c in CENTRAL) + "\n")
    # The root is the audit directory for this one file; module names of all
    # imported project objects are still resolved only from the fresh objects.
    audit_log = logs / "KernelAudit.log"
    command = [str(lean), "-j", "1", "--root=" + str(output)]
    if not args.skip_import_recheck:
        command += ["--trust=0"]
    command += [str(audit)]
    started = time.monotonic()
    print("AUDIT central declaration bodies and theorem axioms", flush=True)
    with audit_log.open("w") as stream:
        proc = subprocess.run(command, cwd=source, env=env, stdout=stream, stderr=subprocess.STDOUT)
    result["audit"] = {"exit_code": proc.returncode, "seconds": time.monotonic()-started,
                       "command": command, "log": str(audit_log.relative_to(output)),
                       "generated_source_sha256": sha(audit)}
    content = audit_log.read_text()
    axiom_sets = re.findall(r"depends on axioms:\s*\[([^]]*)\]", content)
    if proc.returncode or len(axiom_sets) != len(CENTRAL):
        result["status"] = "audit_failed"
        save()
        print(content[-12000:])
        raise RuntimeError("Central theorem audit did not complete")
    for axiom_set in axiom_sets:
        observed = {a.strip() for a in axiom_set.split(",") if a.strip()}
        if not observed <= ALLOWED_AXIOMS:
            raise RuntimeError("Unapproved central theorem axiom: " + axiom_set)
    body_rechecks = re.findall(r"CENTRAL_BODY_RECHECK_PASS\s+([A-Za-z0-9_'.]+)", content)
    if not args.skip_import_recheck and body_rechecks != CENTRAL:
        result["status"] = "audit_failed"
        save()
        raise RuntimeError("The six explicit kernel body rechecks did not all pass: " + repr(body_rechecks))
    result["central_body_recheck"] = not args.skip_import_recheck
    result["central_body_recheck_names"] = body_rechecks
    if hashes != {str(p.relative_to(base)): sha(p) for p in paths}:
        raise RuntimeError("Sources changed during the clean build")
    if any(sha(base / rel) != digest for rel, digest in result["build_configuration_sha256"].items()):
        raise RuntimeError("Build configuration changed during verification")
    final_builds = {row["module"]: row for row in result["builds"]}
    if any(module not in final_builds or final_builds[module]["exit_code"] != 0 for module in order):
        raise RuntimeError("A required module has no successful final build")
    result["status"] = "passed"
    result["axioms"] = {name: values for name, values in zip(CENTRAL, axiom_sets)}
    result["final_module_count"] = len(order)
    result["final_module_exit_codes"] = {module: final_builds[module]["exit_code"] for module in order}
    result["completed_utc"] = datetime.now(timezone.utc).isoformat()
    save()
    print("PASS clean build and central theorem audit:", result_path, flush=True)


if __name__ == "__main__":
    main()
