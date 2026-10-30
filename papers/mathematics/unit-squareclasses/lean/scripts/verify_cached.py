#!/usr/bin/env python3
"""Fresh verification against a pinned, already built mathlib checkout.

This compiles every production source into an isolated new directory. Existing
project .olean files never appear on LEAN_PATH. The script does not download or
rebuild mathlib; that limitation is explicit in its machine-readable report.
"""

from __future__ import annotations

import argparse
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


LEAN_VERSION = "4.19.0"
LEAN_COMMIT = "6caaee842e94"
MATHLIB_COMMIT = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
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
    sources = {"UnitSquareclass": project / "UnitSquareclass.lean",
               "AxiomAudit": project / "AxiomAudit.lean"}
    for path in sorted((project / "UnitSquareclass").rglob("*.lean")):
        sources[".".join(path.relative_to(project).with_suffix("").parts)] = path
    if not all(path.is_file() for path in sources.values()):
        raise RuntimeError("Missing production root source")
    return sources


def module_order(code: dict[str, str]) -> list[str]:
    imports: dict[str, list[str]] = {}
    for name, source in code.items():
        deps: list[str] = []
        for line in source.splitlines():
            match = re.match(r"\s*import\s+(.+?)\s*$", line)
            if match:
                for dependency in match.group(1).split():
                    if dependency.startswith("UnitSquareclass") or dependency == "AxiomAudit":
                        if dependency not in code:
                            raise RuntimeError(f"Unknown local import {dependency} in {name}")
                        deps.append(dependency)
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
    return result


def axiom_reports(output: str) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S):
        reports[match.group(1)] = [item.strip() for item in match.group(2).split(",") if item.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        reports[match.group(1)] = []
    return reports


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib-cache", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True,
                        help="Full path to the pinned Lean 4.19.0 executable")
    parser.add_argument("--packages-root", type=Path,
                        help="Optional directory containing mathlib's pinned transitive packages")
    parser.add_argument("--output", type=Path,
                        help="New directory; must not already exist")
    parser.add_argument("--module-timeout", type=int, default=600)
    args = parser.parse_args()
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
        "method": "fresh isolated compilation of every production module",
        "dependency_policy": "pinned cached mathlib/dependency oleans; dependencies not rebuilt",
        "standard_axioms_allowed": sorted(ALLOWED_AXIOMS),
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
        report["lean"] = {"executable": str(lean), "version": version, "commit": commit,
                          "sha256": sha256(lean)}
        report["mathlib"] = git_pin(mathlib, MATHLIB_COMMIT)
        manifest_path = mathlib / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        report["mathlib_manifest_sha256"] = sha256(manifest_path)
        pinned_manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
        expected = {item["name"]: item["rev"] for item in pinned_manifest["packages"]}
        libraries = [mathlib / ".lake/build/lib/lean"]
        dependencies = []
        for package in manifest["packages"]:
            name, revision = package["name"], package["rev"]
            if expected.get(name) != revision:
                raise RuntimeError(f"Dependency pin disagreement for {name}")
            candidates = ([args.packages_root.resolve() / name] if args.packages_root else
                          [mathlib / ".lake/packages" / name,
                           project / ".lake/packages" / name, mathlib.parent / name])
            path = next((candidate for candidate in candidates if candidate.is_dir()), None)
            if path is None:
                raise RuntimeError(f"Cannot locate pinned dependency {name}; use --packages-root")
            library = path / ".lake/build/lib/lean"
            dependencies.append({"name": name, **git_pin(path, revision),
                                 "compiled_library_present": library.is_dir()})
            libraries.append(library)
        report["dependencies"] = dependencies
        if not libraries[0].is_dir():
            raise RuntimeError("The pinned mathlib checkout has no built Lean library directory")
        core = Path(command([str(lean), "--print-libdir"], project)).resolve()
        if not (core / "Init.olean").is_file():
            raise RuntimeError(f"Missing compiler core library at {core}")
        libraries.append(core)

        sources = production_sources(project)
        source_hashes = {name: sha256(path) for name, path in sources.items()}
        code = {name: strip_comments_and_strings(path.read_text(encoding="utf-8"))
                for name, path in sources.items()}
        forbidden = []
        for name, text in code.items():
            for match in re.finditer(r"\b(sorry|admit|axiom)\b", text):
                line = text.count("\n", 0, match.start()) + 1
                forbidden.append(f"{name}:{line}: {match.group(1)}")
        if forbidden:
            raise RuntimeError("Forbidden proof token(s): " + "; ".join(forbidden))
        report["source_scan"] = {"forbidden_tokens": [], "source_sha256": source_hashes}
        order = module_order(code)
        report["module_order"] = order
        snapshot, lib, logs = output / "source", output / "lib", output / "logs"
        snapshot.mkdir()
        lib.mkdir()
        logs.mkdir()
        for name, source in sources.items():
            target = snapshot.joinpath(*name.split(".")).with_suffix(".lean")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            shutil.copy2(project / name, snapshot / name)
        env = os.environ.copy()
        env.pop("LEAN_SYSROOT", None)
        env["LEAN_PATH"] = os.pathsep.join(str(path) for path in [lib, *libraries])
        report["lean_path"] = env["LEAN_PATH"]
        all_output = []
        for module in order:
            source = snapshot.joinpath(*module.split(".")).with_suffix(".lean")
            artifact = lib.joinpath(*module.split(".")).with_suffix(".olean")
            artifact.parent.mkdir(parents=True, exist_ok=True)
            argv = [str(lean), f"--root={snapshot}", "-o", str(artifact), str(source)]
            print(f"Compiling {module}", flush=True)
            proc = subprocess.run(argv, cwd=output, env=env, text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  timeout=args.module_timeout, check=False)
            logfile = logs / (module + ".log")
            logfile.write_text(proc.stdout, encoding="utf-8")
            entry = {"name": module, "command": argv, "exit_code": proc.returncode,
                     "log": str(logfile.relative_to(output)),
                     "source_sha256": source_hashes[module]}
            if artifact.is_file():
                entry["olean_sha256"] = sha256(artifact)
            report["modules"].append(entry)
            save_report()
            all_output.append(proc.stdout)
            if proc.returncode:
                print(proc.stdout, flush=True)
                raise RuntimeError(f"Compilation failed for {module}")
        combined = "\n".join(all_output)
        (output / "complete_build.log").write_text(combined, encoding="utf-8")
        audits = axiom_reports(combined)
        requested = set(re.findall(r"#print\s+axioms\s+([\w.]+)", code["AxiomAudit"]))
        missing = requested - audits.keys()
        if missing:
            raise RuntimeError(f"Missing axiom output for {sorted(missing)}")
        nonstandard = {name: sorted(set(axioms) - ALLOWED_AXIOMS)
                       for name, axioms in audits.items() if set(axioms) - ALLOWED_AXIOMS}
        if nonstandard:
            raise RuntimeError(f"Nonstandard axioms detected: {nonstandard}")
        report["axiom_audit"] = {name: audits[name] for name in sorted(audits)}
        report["audited_endpoints"] = sorted(requested)
        changed = [name for name, path in sources.items() if sha256(path) != source_hashes[name]]
        if changed:
            raise RuntimeError(f"Source changed during verification: {changed}")
        report["status"] = "passed"
        print(f"PASS: {len(order)} freshly compiled modules; {len(requested)} audited endpoints.",
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
