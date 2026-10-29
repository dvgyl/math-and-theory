#!/usr/bin/env python3
"""Rebuild every local proof from source and audit the final theorem dependencies.

Default: use the pinned Lake project after `lake exe cache get`.
Offline alternative: --lean /path/to/lean --mathlib /path/to/pinned/mathlib4.
Neither mode uses supplied local object files. Mathlib dependency caches are
allowed, but the Mathlib checkout must match the pin and have no tracked edits.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import resource
import signal
import shutil


ROOT = Path(__file__).resolve().parent
PIN = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT = "AuditExactContraction"


def module_order():
    seen, ordered = set(), []

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        source = ROOT / (name + ".lean")
        for dep in re.findall(r"(?m)^import\s+(\S+)", source.read_text()):
            if (ROOT / (dep + ".lean")).exists():
                visit(dep)
        ordered.append(name)

    visit(AUDIT)
    return ordered


def without_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n': out.append('\n')
            i += 1
        elif source[i] == '"':
            out.append(' ')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == '\n': out.append('\n')
                    i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i]); i += 1
    if depth: raise ValueError('Unclosed block comment')
    return ''.join(out)

def fingerprint_dependencies(external, mathlib, leanbin):
    packages = [p for p in sorted(mathlib.parent.iterdir()) if p.is_dir()]
    locations = [(p.name, p, p/'.lake/build/lib/lean') for p in packages]
    locations.append(('lean-core', leanbin.parent/'src/lean', leanbin.parent/'lib/lean'))
    records, active = {}, set()
    def visit(module):
        if module in records or module in active: return
        active.add(module)
        rel = Path(*module.split('.'))
        found = [(name, src/rel.with_suffix('.lean'), obj/rel.with_suffix('.olean'))
            for name,src,obj in locations if (src/rel.with_suffix('.lean')).is_file()]
        if len(found)!=1: raise ValueError('Unresolved or ambiguous dependency: '+module)
        name,src,obj=found[0]
        if not obj.is_file(): raise ValueError('Missing compiled dependency: '+module)
        clean=without_comments(src.read_text())
        deps=[]
        if not re.search(r'^prelude\s*$',clean,re.M) and module!='Init': deps.append('Init')
        for line in re.findall(r'^import\s+([^\n]+)',clean,re.M): deps.extend(line.split())
        for dep in deps: visit(dep)
        records[module]={'module':module,'package':name,
            'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
            'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest()}
        active.remove(module)
    for module in external: visit(module)
    return [records[name] for name in sorted(records)]


def check_axioms(text, requested):
    report_names = re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", text)
    if len(report_names) != len(requested) or set(report_names) != requested:
        raise RuntimeError("Audit must report each requested theorem exactly once")
    audited = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        audited[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        audited[name] = set()
    if not requested:
        raise RuntimeError("no axiom audit requested")
    for name in sorted(requested):
        if name not in audited:
            raise RuntimeError("missing axiom audit: " + name)
        if audited[name] - STANDARD_AXIOMS:
            raise RuntimeError("unexpected axiom: " + name + " " + repr(audited[name]))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if bool(args.lean) != bool(args.mathlib):
        parser.error("supply both --lean and --mathlib, or neither")

    modules = module_order()
    extra_sources = {p.stem for p in ROOT.glob("*.lean")} - set(modules) - {"lakefile"}
    if extra_sources:
        raise SystemExit("Unbuilt local proof source(s): " + repr(sorted(extra_sources)))
    out = ROOT / ".lake" / "build" / "lib" / "lean"
    if out.is_symlink():
        raise RuntimeError("Local output directory must not be a symbolic link")
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SYSROOT", None)
    env["LEAN_NUM_THREADS"] = "1"
    resource.setrlimit(resource.RLIMIT_AS, (8*1024**3, 8*1024**3))
    mathlib = args.mathlib.resolve() if args.mathlib else ROOT / ".lake/packages/mathlib"
    if args.lean:
        lean = args.lean.resolve()
        paths = [out, mathlib / ".lake/build/lib/lean"]
        paths += sorted(mathlib.parent.glob("*/.lake/build/lib/lean"))
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
        env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
        prefix = [str(lean)]
    else:
        prefix = ["lake", "env", "lean"]

    runtime = ROOT / ".verification"
    runtime.mkdir(exist_ok=True)
    log_path = runtime / "verification_log.txt"
    external = sorted({dep for name in modules for line in re.findall(r"(?m)^import\s+([^\n]+)", without_comments((ROOT/(name+".lean")).read_text())) for dep in line.split() if not (ROOT/(dep+".lean")).exists()})
    with log_path.open("w", encoding="utf-8") as log:
        def record(message):
            log.write(message + "\n")
            log.flush()
            print(message, flush=True)

        def run(command):
            record("COMMAND " + " ".join(map(str, command)))
            start = time.monotonic()
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGTERM)
                try: process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise RuntimeError("compiler time limit exceeded")
            record(f"EXIT {code} ELAPSED_SECONDS {time.monotonic()-start:.3f}")
            if code:
                raise RuntimeError("command failed")

        try:
            record("VERIFICATION START " + datetime.now(timezone.utc).isoformat())
            record("LOCAL MODULE COUNT " + str(len(modules)))
            record("MATHLIB PIN " + PIN)
            rev = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"],
                                          text=True).strip()
            if rev != PIN:
                raise RuntimeError("Mathlib checkout does not match the pin: " + rev)
            subprocess.run(["git", "-C", str(mathlib), "diff", "--exit-code", "HEAD", "--"],
                           check=True, stdout=log, stderr=subprocess.STDOUT)
            record("MATHLIB TRACKED SOURCE INTEGRITY PASSED")
            locks = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
            if len(locks) != 9 or len({entry["name"] for entry in locks}) != 9:
                raise RuntimeError("Expected exactly nine unique pinned dependencies")
            pins = {}
            for entry in locks:
                dep = mathlib.parent / entry["name"]
                actual = subprocess.check_output(["git", "-C", str(dep), "rev-parse", "HEAD"], text=True).strip()
                if actual != entry["rev"]: raise RuntimeError("Dependency revision mismatch: " + entry["name"])
                subprocess.run(["git", "-C", str(dep), "diff", "--exit-code", "HEAD", "--"], check=True, stdout=log, stderr=subprocess.STDOUT)
                pins[entry["name"]] = actual
            compiler = args.lean.resolve() if args.lean else Path(subprocess.check_output(["lake", "env", "which", "lean"], cwd=ROOT, env=env, text=True).strip()).resolve()
            before = fingerprint_dependencies(external, mathlib, compiler.parent)
            fingerprints = {"dependency_pins": pins, "compiler_sha256": hashlib.sha256(compiler.read_bytes()).hexdigest(), "before": before}
            (runtime / "dependency-fingerprints.json").write_text(json.dumps(fingerprints, indent=2)+"\n")
            manifest = json.loads((ROOT / "source_hashes.json").read_text())
            expected_names = {m + ".lean" for m in modules}
            expected_names.update({"lakefile.lean", "lean-toolchain", "lake-manifest.json", "verify.py"})
            if set(manifest) != expected_names:
                raise RuntimeError("source hash manifest scope mismatch")
            for name in sorted(expected_names):
                body = (ROOT / name).read_bytes()
                digest = hashlib.sha256(body).hexdigest()
                if digest != manifest[name]:
                    raise RuntimeError("source hash mismatch: " + name)
                record("SHA256 " + name + " " + digest)
                if name.endswith(".lean"):
                    source = body.decode("utf-8")
                    if re.search(r"\b(?:sorry|admit|native_decide|skipKernelTC|implemented_by|ofReduceBool|ofReduceNat)\b", source):
                        raise RuntimeError("prohibited proof shortcut token: " + name)
                    if re.search(r"(?m)^\s*(?:axiom|constant)\s", source):
                        raise RuntimeError("custom axiom declaration: " + name)
            version = subprocess.check_output(prefix + ["--version"], cwd=ROOT,
                                              env=env, text=True).strip()
            record("TOOLCHAIN " + version)
            if not re.search(r"version 4\.19\.0(?:[ ,]|$)", version) or "6caaee842e94" not in version:
                raise RuntimeError("unexpected Lean toolchain")
            for name in modules:
                run(prefix + ["--trust=0", "-j1", "-DwarningAsError=true", "-o", str(out / (name + ".olean")),
                              name + ".lean"])

            requested = set(re.findall(r"(?m)^#print axioms\s+(\S+)",
                                       (ROOT / (AUDIT + ".lean")).read_text()))
            log.flush()
            text = log_path.read_text()
            check_axioms(text, requested)
            after = fingerprint_dependencies(external, mathlib, compiler.parent)
            if after != before: raise RuntimeError("External source/object closure changed during proof replay")
            fingerprints["after"] = after
            fingerprints["stable"] = True
            (runtime / "dependency-fingerprints.json").write_text(json.dumps(fingerprints, indent=2)+"\n")
            record("EXTERNAL SOURCE/OBJECT CLOSURE STABLE: " + str(len(before)))
            record("AXIOM AUDIT PASSED: " + str(len(requested)) + " declarations")
            record("Allowed standard foundations: " + ", ".join(sorted(STANDARD_AXIOMS)))
            record("VERIFICATION PASSED " + datetime.now(timezone.utc).isoformat())
            record("Every included local proof source was rebuilt with --trust=0 -j1.")
            record("No supplied local object file was used.")
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            record("VERIFICATION FAILED: " + str(error))
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
