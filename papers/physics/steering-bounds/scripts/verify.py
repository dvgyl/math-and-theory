#!/usr/bin/env python3
"""Reproduce the pinned Lake build and audit its theorem dependencies.

Configuration checks and existing-log checks have deliberately separate result
labels. Neither is reported as a successful Lean build.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import shutil
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
TOOLCHAIN = "leanprover/lean4:v4.19.0"
MATHLIB_REV = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = {"sorry", "admit", "axiom", "sorryAx", "native_decide", "ofReduceBool", "implemented_by", "unsafe", "extern"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def names(path: str) -> list[str]:
    return [line.strip() for line in (ROOT / path).read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def mask_comments_and_strings(text: str) -> str:
    """Mask nested Lean comments and ordinary strings, preserving line breaks.

    This is only a source hygiene check. Kernel-reported dependencies below are
    the check for axioms used by the actual declarations.
    """
    out = list(text)
    i = 0
    depth = 0
    string = False
    line_comment = False
    while i < len(text):
        c = text[i]
        if line_comment:
            if c == "\n":
                line_comment = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if text.startswith("/-", i):
                out[i:i + 2] = [" ", " "]
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = [" ", " "]
                depth -= 1
                i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if c != "\n":
                out[i] = " "
            if c == "\\" and i + 1 < len(text):
                if text[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
            else:
                if c == '"':
                    string = False
                i += 1
        elif text.startswith("--", i):
            out[i:i + 2] = [" ", " "]
            line_comment = True
            i += 2
        elif text.startswith("/-", i):
            out[i:i + 2] = [" ", " "]
            depth = 1
            i += 2
        elif c == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    require(depth == 0 and not string, "Unterminated Lean comment or string")
    return "".join(out)


def configuration() -> tuple[list[str], dict[str, str]]:
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Unexpected Lean toolchain pin")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    expected = json.loads((ROOT / "dependency-pins.json").read_text())
    actual = {p["name"]: p.get("rev") for p in manifest["packages"]}
    require(actual == expected, "Dependency manifest does not match exact pins")
    require(expected.get("mathlib") == MATHLIB_REV, "Unexpected Mathlib pin")
    require(all(p["type"] == "git" for p in manifest["packages"]),
            "Portable manifest must not contain local path dependencies")
    require(manifest["name"] == "milne_bounds", "Unexpected package name")
    modules = names("modules.txt")
    require(len(modules) == len(set(modules)), "Duplicate source module")
    require("MilneVerification" in modules, "Missing verification aggregator")
    require(not {"MilneReflection", "MilneSignature"} & set(modules),
            "Out-of-scope proof module in release")
    lakefile = (ROOT / "lakefile.lean").read_text()
    require(MATHLIB_REV in lakefile, "Lakefile does not pin expected Mathlib")
    roots = re.findall(r"`(Milne[A-Za-z0-9_]+)", lakefile)
    require(roots == modules, "Library roots differ from explicit allowlist")
    require(bool(names("audit_theorems.txt")), "Empty theorem audit list")
    return modules, expected


def source_check(modules: list[str]) -> tuple[dict[str, str], list[str]]:
    wanted = {ROOT / "Lean" / (m + ".lean") for m in modules}
    actual = set((ROOT / "Lean").rglob("*.lean"))
    require(actual == wanted,
            "Proof source set differs from allowlist. Missing: " +
            ", ".join(sorted(p.name for p in wanted - actual)) +
            "; extra: " + ", ".join(sorted(str(p) for p in actual - wanted)))
    hashes = {}
    external = set()
    visited = set()
    for module in modules:
        path = ROOT / "Lean" / (module + ".lean")
        require(not path.is_symlink(), "Delivered proof source is a symlink: " + module)
        text = mask_comments_and_strings(path.read_text())
        forbidden = FORBIDDEN & set(re.findall(r"[\w]+", text))
        require(not forbidden, module + " contains forbidden source token(s): " +
                ", ".join(sorted(forbidden)))
        for line in re.findall(r"^\s*import\s+([^\n]+)", text, re.MULTILINE):
            for imp in line.split():
                if imp.startswith("Mathlib.") or imp == "Mathlib":
                    external.add(imp)
                else:
                    require(imp in visited,
                            module + " imports a missing or out-of-order module: " + imp)
        hashes["Lean/" + path.name] = digest(path)
        visited.add(module)
    return hashes, sorted(external)


def audit_axioms(log: str, theorems: list[str]) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    pattern = re.compile(
        r"'([^'\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|"
        r"does not depend on any axioms)", re.MULTILINE)
    for match in pattern.finditer(log):
        name = match.group(1)
        axioms = sorted(x.strip() for x in (match.group(2) or "").split(",")
                        if x.strip())
        if name in found:
            require(found[name] == axioms, "Conflicting axiom reports: " + name)
        found[name] = axioms
    missing = set(theorems) - set(found)
    require(not missing, "Missing axiom reports: " + ", ".join(sorted(missing)))
    for name in theorems:
        unexpected = set(found[name]) - FOUNDATIONS
        require(not unexpected,
                name + " uses unapproved axiom(s): " + ", ".join(sorted(unexpected)))
    return {name: found[name] for name in theorems}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configuration-only", action="store_true",
                        help="check package metadata only; no Lean verification claim")
    parser.add_argument("--check-axiom-log", type=Path,
                        help="audit a supplied #print axioms log; does not run Lean")
    parser.add_argument("--source-only", action="store_true",
                        help="check copied source allowlist, imports, tokens and hashes")
    parser.add_argument("--fetch-cache", action="store_true",
                        help="fetch only external Mathlib imports and their dependencies")
    parser.add_argument("--serial", action="store_true",
                        help="build explicit module targets in dependency order")
    parser.add_argument("--lake", default="lake", help="Lake executable (default: PATH)")
    args = parser.parse_args()
    BUILD.mkdir(parents=True, exist_ok=True)
    modules, pins = configuration()
    if args.configuration_only:
        save(BUILD / "configuration-result.json",
             {"status": "configuration_passed", "lean_checked": False,
              "module_count": len(modules), "dependency_pins": pins})
        print("Configuration passed. Proof sources and Lean compilation were not checked.")
        return 0
    theorems = names("audit_theorems.txt")
    if args.check_axiom_log:
        log_path = args.check_axiom_log.resolve()
        results = audit_axioms(log_path.read_text(), theorems)
        save(BUILD / "supplied-log-audit.json",
             {"status": "supplied_axiom_log_passed", "compiler_run_this_check": False,
              "log_sha256": digest(log_path), "axioms": results})
        print("Supplied axiom log passed; this command did not run the Lean compiler.")
        return 0
    hashes, imports = source_check(modules)
    save(BUILD / "source-audit.json",
         {"status": "source_checks_passed", "lean_checked": False,
          "source_sha256": hashes, "mathlib_imports": imports})
    if args.source_only:
        print("Source checks passed. Lean compilation was not run.")
        return 0

    env = os.environ.copy()
    # The portable build must resolve imports through the pinned packages.
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "ELAN_TOOLCHAIN"):
        env.pop(key, None)
    # Prevent the dependency update hook from fetching all of Mathlib.
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    report = {"status": "running", "mode": "pinned_portable_lake_build",
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "source_sha256": hashes, "dependency_pins": pins, "commands": []}

    def run(label: str, command: list[str]) -> str:
        logfile = BUILD / (label + ".log")
        print("Running:", " ".join(command), flush=True)
        with logfile.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT, text=True, timeout=900)
        entry = {"label": label, "command": command, "exit_code": result.returncode,
                 "log": str(logfile.relative_to(ROOT)), "log_sha256": digest(logfile)}
        report["commands"].append(entry)
        save(BUILD / "verification-result.json", report)
        text = logfile.read_text()
        require(not re.search(r"\bwarning:", text), "Compiler warning: " + str(logfile))
        require(result.returncode == 0,
                "Command failed; inspect " + str(logfile) + "\n" + text[-5000:])
        return text

    try:
        version = run("00-lean-version", [args.lake, "env", "lean", "--version"])
        require(re.search(r"Lean \(version 4\.19\.0(?:[ ,)]|$)", version) is not None,
                "Lake did not select Lean 4.19.0: " + version.strip())
        configuration()  # Dependency materialization must not change the pins.
        for name, rev in pins.items():
            package = ROOT / ".lake" / "packages" / name
            require(package.is_dir() and not package.is_symlink(),
                    "Expected a private pinned Git checkout for dependency " + name)
            actual = subprocess.check_output(
                ["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
            require(actual == rev, "Dependency checkout does not match pin: " + name)
            dirty = subprocess.run(["git", "-C", str(package), "diff", "--quiet", "HEAD", "--"])
            require(dirty.returncode == 0, "Tracked dependency files changed: " + name)
        if args.fetch_cache:
            run("01-mathlib-cache", [args.lake, "exe", "cache", "get", *imports])
        # Force all task-owned sources to elaborate in this run.
        local_build = ROOT / ".lake" / "build"
        if local_build.exists():
            shutil.rmtree(local_build)
        if args.serial:
            for index, module in enumerate(modules):
                run("build-%02d-%s" % (index, module),
                    [args.lake, "build", "+" + module + ":olean"])
        else:
            run("02-build", [args.lake, "build", "MilneBounds"])
        audit_file = BUILD / "AxiomAudit.lean"
        audit_file.write_text("import MilneVerification\n\n" +
                              "\n".join("#check " + t + "\n#print axioms " + t for t in theorems) + "\n")
        log = run("03-axioms", [args.lake, "env", "lean", "-j1", "--trust=0",
                                "-DwarningAsError=true",
                                str(audit_file.relative_to(ROOT))])
        report["axioms"] = audit_axioms(log, theorems)
        new_hashes, _ = source_check(modules)
        require(new_hashes == hashes, "Proof sources changed during verification")
        report["status"] = "passed"
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save(BUILD / "verification-result.json", report)
        print("Pinned Lake build and all requested theorem axiom audits passed.")
        return 0
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        save(BUILD / "verification-result.json", report)
        raise


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print("Verification failed:", error, file=sys.stderr)
        sys.exit(1)
