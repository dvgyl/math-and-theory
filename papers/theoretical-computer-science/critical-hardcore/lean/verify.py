#!/usr/bin/env python3
"""Fresh-output verification against pinned, read-only dependency caches.

On Linux/WSL, use after `lake exe cache get` with the included manifest, or
supply a clean Mathlib checkout with exactly the pinned commits. This copies
every project proof into a fresh directory, never imports an old project .olean,
compiles every module with Lean's kernel enabled, and checks the printed axiom
dependencies of the actual final theorems. It does not rebuild Lean or Mathlib.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


PROJECT = Path(__file__).resolve().parent
EXPECTED_LEAN = "Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CENTRAL = {
    "CriticalHardcore.critical_hardcore_influence_rows",
    "CriticalHardcore.critical_hardcore_spectral_independence",
    "CriticalHardcore.critical_hardcore_pinned_rows",
    "CriticalHardcore.criticalInfluenceBound_le_real",
    "CriticalHardcore.regular_survival_sqrt_sum_le_scale",
}


def run(command, *, cwd=None):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def strip_comments(text):
    """Remove nested Lean block comments and ordinary line comments."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                quoted = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--mathlib", type=Path, default=PROJECT / ".lake/packages/mathlib")
    args = ap.parse_args()
    compiler = shutil.which(args.lean) or str(Path(args.lean).resolve())
    version = run([compiler, "--version"], cwd=PROJECT)
    if "version 4.19.0," not in version or "commit 6caaee842e94" not in version:
        raise SystemExit(f"Wrong Lean compiler: {version}")
    # Resolve an Elan shim before changing into the fresh source directory.
    prefix = Path(run([compiler, "--print-prefix"], cwd=PROJECT))
    installed_compiler = prefix / "bin" / "lean"
    if not installed_compiler.is_file():
        raise SystemExit(f"Lean installation has no compiler at {installed_compiler}")
    compiler = str(installed_compiler.resolve())
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    dependencies, paths = [], []
    mathlib = args.mathlib.resolve()
    for dep in manifest["packages"]:
        if dep["name"] == "mathlib":
            path = mathlib
        else:
            candidates = [PROJECT / ".lake/packages" / dep["name"],
                          mathlib / ".lake/packages" / dep["name"],
                          mathlib.parent / dep["name"]]
            path = next((p.resolve() for p in candidates if (p / ".git").exists()), None)
            if path is None:
                raise SystemExit(f"Missing pinned dependency {dep['name']}")
        head = run(["git", "rev-parse", "HEAD"], cwd=path)
        dirty = run(["git", "status", "--porcelain", "--untracked-files=no"], cwd=path)
        if head != dep["rev"] or dirty:
            raise SystemExit(f"Dependency is not clean at its pin: {dep['name']}")
        build = path / ".lake/build/lib/lean"
        paths.append(build)
        dependencies.append({"name": dep["name"], "commit": head, "clean": True})

    proofs = {"CriticalHardcore": PROJECT / "CriticalHardcore.lean"}
    proofs.update({".".join(p.relative_to(PROJECT).with_suffix("").parts): p
                   for p in sorted((PROJECT / "CriticalHardcore").glob("*.lean"))})
    imports = {}
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|opaque|native_decide|run_cmd|run_tac|implemented_by|trustLevel)\b")
    hashes = {}
    for module, source in proofs.items():
        data = source.read_bytes()
        clean = strip_comments(data.decode())
        found = forbidden.search(clean)
        if found:
            raise SystemExit(f"Disallowed proof mechanism {found.group()} in {source}")
        imports[module] = re.findall(r"^import\s+([\w.]+)", clean, re.MULTILINE)
        hashes[str(source.relative_to(PROJECT))] = hashlib.sha256(data).hexdigest()
    order, visited, active = [], set(), set()
    def visit(module):
        if module in visited:
            return
        if module in active:
            raise SystemExit("Local import cycle")
        active.add(module)
        for dep in imports[module]:
            if dep.startswith("CriticalHardcore"):
                if dep not in proofs:
                    raise SystemExit(f"Unresolved project import {dep}")
                visit(dep)
        active.remove(module)
        visited.add(module)
        order.append(module)
    for module in proofs:
        visit(module)

    reports = PROJECT.parent / "verification"
    reports.mkdir(exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="clean-", dir=reports))
    source_root, output_root = work / "src", work / "olean"
    source_root.mkdir()
    output_root.mkdir()
    for source in proofs.values():
        target = source_root / source.relative_to(PROJECT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    environment = dict(os.environ)
    environment["LEAN_PATH"] = ":".join(map(str, [output_root, source_root] + paths))
    records, audit_output = [], ""
    with (reports / "build.log").open("w") as log:
        log.write(version + "\nFresh project output: " + str(output_root) + "\n")
        log.write("Dependency compiled caches are reused read-only after commit and worktree checks.\n")
        for module in order:
            relative = proofs[module].relative_to(PROJECT)
            out = output_root / relative.with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            command = [compiler, "-j1", "-DautoImplicit=false", "-o", str(out), str(relative)]
            print(f"VERIFY {module}", flush=True)
            log.write("\n$ " + " ".join(command) + "\n")
            started = time.monotonic()
            result = subprocess.run(command, cwd=source_root, env=environment,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=300)
            log.write(result.stdout)
            log.write(f"EXIT {result.returncode}\n")
            log.flush()
            records.append({"module": module, "exit_code": result.returncode,
                            "seconds": round(time.monotonic() - started, 3)})
            if result.returncode:
                print(result.stdout)
                raise SystemExit(f"Verification failed: {module}")
            if module == "CriticalHardcore.Audit":
                audit_output = result.stdout
    axiom_records = {}
    for theorem, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_output, re.S):
        axioms = {a.strip() for a in body.split(",") if a.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise SystemExit(f"Unapproved axiom dependency in {theorem}: {axioms}")
        axiom_records[theorem] = sorted(axioms)
    if not CENTRAL <= axiom_records.keys():
        raise SystemExit("The central axiom audit did not run or its output was not recognized")
    (reports / "axioms.txt").write_text(audit_output)
    certificate = {"status": "PASS", "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "compiler": version, "fresh_output": str(output_root),
                   "dependency_policy": "Pinned clean sources; precompiled dependency caches reused read-only",
                   "dependencies": dependencies, "module_count": len(order),
                   "builds": records, "central_axioms": axiom_records,
                   "source_sha256": hashes}
    (reports / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
    print(f"PASS: {len(order)} fresh module builds; all central axioms are standard Lean foundations.")
    print(f"Certificate: {reports / 'certificate.json'}")


if __name__ == "__main__":
    main()
