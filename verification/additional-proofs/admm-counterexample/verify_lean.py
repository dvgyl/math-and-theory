#!/usr/bin/env python3
"""Recompile this certificate into fresh objects and audit its theorem axioms.

Only Python's standard library is required. Existing, trusted mathlib object
files are used for library imports; every local Research module is recompiled.
This script never downloads dependencies or invokes native_decide.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


LEAN_VERSION = "4.19.0"
TOOLCHAIN = "leanprover/lean4:v4.19.0"
MATHLIB_COMMIT = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
PACKAGE_ORDER = (
    "batteries", "Qq", "aesop", "proofwidgets", "LeanSearchClient",
    "importGraph", "plausible", "Cli",
)
REQUIRED_MODULES = (
    "Research.ADMMGeometry", "Research.ADMMData",
    "Research.ADMMCounterexample", "Research",
)
REQUIRED_THEOREMS = (
    "ADMMGeometry.projection_of_vertex_normals",
    "ADMMGeometry.zero_mem_polytope",
    "ADMMData.x_normal", "ADMMData.z_normal",
    "ADMMData.residual_lower_bound",
    "ADMMCounterexample.zero_fixed_trajectory",
    "ADMMCounterexample.counterexample",
)
OPTIONAL_THEOREMS = {
    "Research.ADMMHingeScalar": ("ADMMHinge.psi_support",),
    "Research.ADMMHinge": ("ADMMHinge.finite_cycle", "ADMMHinge.unique_optimizer"),
    "Research.ADMMHingeTrajectory": ("ADMMHingeTrajectory.verified_orbit_and_optimizer",),
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEAN_CHECK_OPTIONS = ("--trust=0", "-j1", "-DwarningAsError=true")
COMMAND_MEMORY_LIMIT_BYTES = 6 * 1024**3
COMMAND_SECONDS_LIMIT = 120
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|sorryAx)\b|Lean\.ofReduceBool")


def child_memory_limit() -> None:
    """Apply an OS address-space bound where the resource module is available."""
    import resource
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    limit = COMMAND_MEMORY_LIMIT_BYTES
    if hard != resource.RLIM_INFINITY:
        limit = min(limit, hard)
    resource.setrlimit(resource.RLIMIT_AS, (limit, hard))


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_code(text: str) -> str:
    """Replace comments and string literals by whitespace, preserving lines."""
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def local_sources(project: Path) -> tuple[dict[str, Path], dict[str, list[str]]]:
    files = sorted((project / "Research").rglob("*.lean"))
    root = project / "Research.lean"
    if root.is_file():
        files.append(root)
    modules: dict[str, Path] = {}
    imports: dict[str, list[str]] = {}
    for path in files:
        module = ".".join(path.relative_to(project).with_suffix("").parts)
        modules[module] = path
        code = lean_code(path.read_text(encoding="utf-8"))
        forbidden = FORBIDDEN.search(code)
        if forbidden:
            raise ValueError(f"Forbidden proof construct {forbidden.group()!r} in {path}")
        dependencies: list[str] = []
        for line in code.splitlines():
            match = re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+?)\s*$", line)
            if match:
                for name in match.group(1).split():
                    if name == "Research" or name.startswith("Research."):
                        dependencies.append(name)
        imports[module] = dependencies
    missing = set(REQUIRED_MODULES) - modules.keys()
    if missing:
        raise ValueError(f"Missing required release source modules: {sorted(missing)}")
    for module, dependencies in imports.items():
        missing = set(dependencies) - modules.keys()
        if missing:
            raise ValueError(f"{module} imports missing local source modules: {sorted(missing)}")
    return modules, imports


def dependency_order(imports: dict[str, list[str]]) -> list[str]:
    order: list[str] = []
    active: set[str] = set()
    done: set[str] = set()

    def visit(module: str) -> None:
        if module in done:
            return
        if module in active:
            raise ValueError(f"Local import cycle at {module}")
        active.add(module)
        for dependency in imports[module]:
            visit(dependency)
        active.remove(module)
        done.add(module)
        order.append(module)

    for module in sorted(imports):
        visit(module)
    return order


def parse_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S):
        result[match.group(1)] = [a.strip() for a in match.group(2).split(",") if a.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        result[match.group(1)] = []
    missing = set(expected) - result.keys()
    if missing:
        raise ValueError(f"Missing #print axioms results: {sorted(missing)}")
    for theorem in expected:
        extra = set(result[theorem]) - ALLOWED_AXIOMS
        if extra:
            raise ValueError(f"Unapproved axioms in {theorem}: {sorted(extra)}")
    return {name: result[name] for name in expected}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--mathlib", type=Path, help="Existing mathlib v4.19.0 checkout with cached objects")
    parser.add_argument("--lean", type=Path, help="Path to the Lean 4.19.0 executable (default: PATH)")
    parser.add_argument("--output", type=Path, help="New verification directory; it must not exist yet")
    parser.add_argument("--theorem", action="append", default=[], help="Additional theorem to audit")
    args = parser.parse_args()

    project = args.project.resolve()
    mathlib = (args.mathlib or project / ".lake/packages/mathlib").resolve()
    lean_arg = str(args.lean) if args.lean else shutil.which("lean")
    if not lean_arg:
        parser.error("Lean not found; provide --lean /path/to/lean")
    lean = str(Path(lean_arg).resolve())
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    run_dir = (args.output or project / "verification" / stamp).resolve()
    run_dir.mkdir(parents=True, exist_ok=False)
    objects = run_dir / "objects"
    objects.mkdir()
    manifest_path = run_dir / "manifest.json"
    manifest: dict = {
        "status": "running", "started_utc": utc_now(),
        "project": str(project), "mathlib": str(mathlib),
        "lean": lean, "required_lean_version": LEAN_VERSION,
        "pinned_mathlib_commit": MATHLIB_COMMIT,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "proof_compiler_options": list(LEAN_CHECK_OPTIONS),
        "per_command_seconds_limit": COMMAND_SECONDS_LIMIT,
        "per_command_address_space_limit_bytes": COMMAND_MEMORY_LIMIT_BYTES if os.name == "posix" else None,
        "commands": [], "sources": {},
        "verifier_sha256": digest(Path(__file__).resolve()),
        "fresh_project_objects": str(objects),
        "configuration_sha256": {
            name: digest(project / name)
            for name in ("lean-toolchain", "lakefile.toml")
            if (project / name).is_file()
        },
    }

    def save() -> None:
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def run(label: str, argv: list[str], env: dict[str, str] | None = None,
            require_success: bool = True) -> tuple[int, str]:
        log_path = run_dir / f"{label}.log"
        record = {
            "label": label, "argv": argv, "cwd": str(project),
            "started_utc": utc_now(), "log": str(log_path.relative_to(run_dir)),
        }
        if env and "LEAN_PATH" in env:
            record["LEAN_PATH"] = env["LEAN_PATH"]
        manifest["commands"].append(record)
        save()
        print(f"[{label}] {' '.join(argv)}", flush=True)
        start = time.monotonic()
        with log_path.open("w", encoding="utf-8") as log:
            log.write("COMMAND " + json.dumps(argv) + "\n")
            log.write("CWD " + str(project) + "\n")
            if env and "LEAN_PATH" in env:
                log.write("LEAN_PATH " + env["LEAN_PATH"] + "\n")
            log.write("STARTED_UTC " + record["started_utc"] + "\n\n")
            log.flush()
            process = subprocess.Popen(argv, cwd=project, env=env, stdout=log,
                                       stderr=subprocess.STDOUT, text=True,
                                       preexec_fn=child_memory_limit if os.name == "posix" else None)
            try:
                while True:
                    try:
                        code = process.wait(timeout=30)
                        break
                    except subprocess.TimeoutExpired:
                        if time.monotonic() - start >= COMMAND_SECONDS_LIMIT:
                            raise TimeoutError(f"{label} exceeded {COMMAND_SECONDS_LIMIT} seconds")
                        print(f"[{label}] still running ({time.monotonic() - start:.0f}s)", flush=True)
            except BaseException:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
                raise
            log.write(f"\nEXIT_CODE {code}\n")
        record.update({"exit_code": code, "finished_utc": utc_now(),
                       "duration_seconds": round(time.monotonic() - start, 3)})
        save()
        output = log_path.read_text(encoding="utf-8")
        if code and require_success:
            raise RuntimeError(f"{label} failed with exit code {code}; see {log_path}")
        if "sorryAx" in output:
            raise RuntimeError(f"sorryAx appeared in {label}; see {log_path}")
        print(f"[{label}] exit {code}", flush=True)
        return code, output

    save()
    try:
        if (project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise ValueError("Release lean-toolchain does not match the required pin")
        if (mathlib / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise ValueError("Mathlib lean-toolchain does not match the required pin")
        _, version_output = run("lean-version", [lean, "--version"])
        if not re.search(r"\bLean \(version 4\.19\.0(?:,|\s|\))", version_output):
            raise ValueError(f"Expected Lean {LEAN_VERSION}, got {version_output!r}")
        manifest["lean_version_output"] = version_output
        manifest["mathlib_metadata_sha256"] = {
            name: digest(mathlib / name)
            for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
            if (mathlib / name).is_file()
        }
        if (mathlib / ".git").exists():
            _, head = run("mathlib-revision", ["git", "-C", str(mathlib), "rev-parse", "HEAD"])
            revision_lines = [line.strip() for line in head.splitlines()
                              if re.fullmatch(r"[0-9a-f]{40}", line.strip())]
            if revision_lines != [MATHLIB_COMMIT]:
                raise ValueError(f"Mathlib is not at the pinned commit: {revision_lines}")
            manifest["mathlib_revision_check"] = "git_head_matches_pin"
        else:
            manifest["mathlib_revision_check"] = "archive_without_git_metadata; dependency_provenance_supplied_by_operator"

        modules, imports = local_sources(project)
        order = dependency_order(imports)
        manifest["module_order"] = order
        for module, path in modules.items():
            manifest["sources"][module] = {
                "path": str(path.relative_to(project)), "sha256": digest(path),
                "bytes": path.stat().st_size, "local_imports": imports[module],
            }

        mathlib_objects = mathlib / ".lake/build/lib/lean"
        if not mathlib_objects.is_dir():
            raise ValueError(f"Missing mathlib object cache: {mathlib_objects}")
        lean_paths = [objects, mathlib_objects]
        manifest["absent_optional_cache_directories"] = []
        for name in PACKAGE_ORDER:
            candidates = [mathlib / ".lake/packages" / name,
                          mathlib.parent / name,
                          project / ".lake/packages" / name]
            package = next((p / ".lake/build/lib/lean" for p in candidates
                            if (p / ".lake/build/lib/lean").is_dir()), None)
            if package is None:
                # Cli is used by Lake tooling, but these proof imports do not
                # require it. Preserve the established search-path entry and
                # let Lean report a missing imported module if one is needed.
                if name != "Cli":
                    raise ValueError(f"Missing cached Lean dependency {name}: run lake exe cache get")
                package = candidates[0] / ".lake/build/lib/lean"
                manifest["absent_optional_cache_directories"].append(str(package))
            lean_paths.append(package.resolve())
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join(map(str, lean_paths))
        manifest["LEAN_PATH"] = env["LEAN_PATH"]
        manifest["mathlib_dependency_manifest"] = json.loads((mathlib / "lake-manifest.json").read_text())
        save()

        built: set[str] = set()
        for module in order:
            for dependency in imports[module]:
                expected_object = objects.joinpath(*dependency.split(".")).with_suffix(".olean")
                if dependency not in built or not expected_object.is_file():
                    raise ValueError(f"Fresh local dependency is unavailable: {dependency}")
            target = objects.joinpath(*module.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            source = modules[module]
            run(module, [lean, *LEAN_CHECK_OPTIONS, "-o", str(target), str(source.relative_to(project))], env)
            if not target.is_file():
                raise ValueError(f"Lean succeeded without writing expected object {target}")
            manifest["sources"][module]["object_sha256"] = digest(target)
            built.add(module)
            save()

        optional_theorems = [theorem for module, names in OPTIONAL_THEOREMS.items()
                             if module in modules for theorem in names]
        theorems = list(dict.fromkeys((*REQUIRED_THEOREMS, *optional_theorems, *args.theorem)))
        for theorem in theorems:
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", theorem):
                raise ValueError(f"Invalid theorem name: {theorem}")
        audit = run_dir / "AxiomAudit.lean"
        audit.write_text("\n".join(f"import {module}" for module in order) + "\n\n" +
                         "\n".join(f"#print axioms {theorem}" for theorem in theorems) +
                         "\n", encoding="utf-8")
        manifest["axiom_audit_source_sha256"] = digest(audit)
        _, output = run("axiom-audit", [lean, *LEAN_CHECK_OPTIONS, str(audit)], env)
        manifest["axioms"] = parse_axioms(output, theorems)
        final_modules, final_imports = local_sources(project)
        if final_modules != modules or final_imports != imports:
            raise ValueError("Local Lean source inventory or imports changed during verification")
        for module, path in modules.items():
            if digest(path) != manifest["sources"][module]["sha256"]:
                raise ValueError(f"Source changed during verification: {path}")
        if digest(Path(__file__).resolve()) != manifest["verifier_sha256"]:
            raise ValueError("Verification script changed during the run")
        for name, expected_hash in manifest["configuration_sha256"].items():
            if digest(project / name) != expected_hash:
                raise ValueError(f"Build configuration changed during verification: {name}")
        manifest.update({"status": "verified", "finished_utc": utc_now()})
        save()
        print(f"VERIFIED: {manifest_path}", flush=True)
        return 0
    except BaseException as error:
        manifest.update({"status": "failed", "finished_utc": utc_now(),
                         "error": f"{type(error).__name__}: {error}"})
        save()
        print(f"FAILED: {error}\nManifest: {manifest_path}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
