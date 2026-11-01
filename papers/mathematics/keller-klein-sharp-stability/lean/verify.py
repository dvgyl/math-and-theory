#!/usr/bin/env python3
"""Fresh-output verification against pinned, read-only dependency caches.

Use after `lake exe cache get` with the included manifest. This copies every
project proof into a fresh directory, never imports an old project .olean,
compiles every module in dependency order with Lean's kernel enabled, and
checks the printed axiom dependencies of every audited declaration. The
groups are the unchanged 62 modules of the earlier keller-klein package, the
nine inherited support-gap modules, the 15 new stability modules, the
attainment module and the two-module conditional probability bridge. It does
not rebuild Lean or Mathlib.
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
import tempfile
import time


PROJECT = Path(__file__).resolve().parent
EXPECTED_LEAN = ("version 4.19.0,", "commit 6caaee842e94")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FLAT_GROUPS = ("support-gap", "stability", "attainment", "bridge")
# Expected number of `#print axioms` audits in each group.
AUDIT_COUNTS = {"support-gap": 46, "stability": 67, "attainment": 2, "bridge": 15}
CENTRAL = {
    "KellerKlein.small_coefficient_upper_concentration",
    "Breakthrough.GlobalGapRigidity.signed_supportGap_inverse",
    "Breakthrough.GlobalGapRigidity.signed_supportGap_inverse_equality_iff",
    "Breakthrough.ActualGlobalGapStability.signed_supportGap_phase_stability",
    "Breakthrough.ActualGlobalGapStability.all_caps_supportGap_stability",
    "Breakthrough.ExactSaturatedModulus.actual_saturated_modulus",
    "Breakthrough.ExactSaturatedModulus.actual_saturated_modulus_equality_iff",
    "Breakthrough.ActualSaturatedModulus.all_caps_exact_saturated_modulus",
    "Breakthrough.FixedFlatTradeoff.signed_supportGap_fixed_flat",
    "Breakthrough.SharpStabilityExamples.actual_sharp_stability_witness",
    "Breakthrough.SharpStabilityExamples.concrete_sharp_parameters",
    "Breakthrough.ExactModulusAttainment.actual_exact_modulus_family",
    "Breakthrough.FourShiftEnvelope.actual_four_shift_envelope",
}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|opaque|native_decide|run_cmd|run_tac|"
                       r"implemented_by|extern|trustLevel|skipKernelTC)\b")
AUDIT = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.S)
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


def run(command, *, cwd=None):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strip_comments(text):
    """Remove nested Lean block comments, line comments and string contents."""
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
    if depth or quoted:
        raise SystemExit("Unclosed comment or string")
    return "".join(out)


def dependency_paths(mathlib):
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    dependencies, paths = [], []
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
        paths.append(path / ".lake/build/lib/lean")
        dependencies.append({"name": dep["name"], "commit": head, "clean": True})
    return dependencies, paths


def collect_sources():
    """Map module name to (group, source path, path relative to the fresh root)."""
    sources = {"KellerKlein": ("KellerKlein", PROJECT / "KellerKlein.lean", Path("KellerKlein.lean"))}
    for path in sorted((PROJECT / "KellerKlein").rglob("*.lean")):
        relative = path.relative_to(PROJECT)
        sources[".".join(relative.with_suffix("").parts)] = ("KellerKlein", path, relative)
    for group in FLAT_GROUPS:
        for path in sorted((PROJECT / group).glob("*.lean")):
            if path.stem in sources:
                raise SystemExit(f"Repeated module name {path.stem}")
            sources[path.stem] = (group, path, Path(path.name))
    stray = {p for p in PROJECT.rglob("*.lean") if ".lake" not in p.parts
             and p.name != "lakefile.lean"} - {row[1] for row in sources.values()}
    if stray:
        raise SystemExit(f"Lean sources outside the verified groups: {sorted(map(str, stray))}")
    return sources


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--mathlib", type=Path, default=PROJECT / ".lake/packages/mathlib")
    ap.add_argument("--trust", type=int, choices=(0, 1), default=1,
                    help="Import policy: 1 trusts compiled imports, 0 rechecks imports; "
                         "new declarations are kernel checked in both modes")
    ap.add_argument("--output", type=Path,
                    help="Fresh report directory (default: a new temporary directory)")
    args = ap.parse_args()
    reports = (args.output.resolve() if args.output
               else Path(tempfile.mkdtemp(prefix="keller-klein-sharp-stability-")))
    reports.mkdir(parents=True, exist_ok=True)
    if (reports / "certificate.json").exists():
        (reports / "certificate.json").unlink()
    compiler = shutil.which(args.lean) or str(Path(args.lean).resolve())
    version = run([compiler, "--version"], cwd=PROJECT)
    if not all(token in version for token in EXPECTED_LEAN):
        raise SystemExit(f"Wrong Lean compiler: {version}")
    prefix = Path(run([compiler, "--print-prefix"], cwd=PROJECT))
    compiler = str((prefix / "bin" / "lean").resolve())
    dependencies, paths = dependency_paths(args.mathlib.resolve())

    sources = collect_sources()
    imports, hashes, expected_audits = {}, {}, {}
    for module, (group, source, _) in sources.items():
        data = source.read_bytes()
        clean = strip_comments(data.decode())
        found = FORBIDDEN.search(clean)
        if found:
            raise SystemExit(f"Disallowed proof mechanism {found.group()} in {source}")
        if re.search(r"set_option\s+debug\.", clean):
            raise SystemExit(f"Debug option in {source}")
        imports[module] = [name for line in re.findall(r"^import\s+([^\n]+)", clean, re.M)
                           for name in line.split()]
        for name in imports[module]:
            if name not in sources and not name.startswith(("Mathlib", "Lean", "Batteries")):
                raise SystemExit(f"Unresolved project import {name} in {module}")
        expected_audits[module] = re.findall(r"^#print axioms (\S+)", clean, re.M)
        hashes[str(source.relative_to(PROJECT))] = hashlib.sha256(data).hexdigest()
    for group, count in AUDIT_COUNTS.items():
        found = sum(len(expected_audits[m]) for m, row in sources.items() if row[0] == group)
        if found != count:
            raise SystemExit(f"Expected {count} axiom audits in {group}, found {found}")

    order, visited, active = [], set(), set()

    def visit(module):
        if module in visited:
            return
        if module in active:
            raise SystemExit("Local import cycle")
        active.add(module)
        for dep in imports[module]:
            if dep in sources:
                visit(dep)
        active.remove(module)
        visited.add(module)
        order.append(module)

    for module in sources:
        visit(module)

    work = Path(tempfile.mkdtemp(prefix="clean-", dir=reports))
    source_root, output_root = work / "src", work / "olean"
    source_root.mkdir()
    output_root.mkdir()
    for _, source, relative in sources.values():
        target = source_root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    environment = dict(os.environ)
    environment["LEAN_PATH"] = ":".join(map(str, [output_root, source_root] + paths))
    records, audits, audit_text = [], {}, []
    with (reports / "build.log").open("w") as log:
        log.write(version + "\nFresh project output: " + str(output_root) + "\n")
        log.write("Dependency compiled caches are reused read-only after commit and worktree checks.\n")
        for module in order:
            group, _, relative = sources[module]
            out = output_root / relative.with_suffix(".olean")
            out.parent.mkdir(parents=True, exist_ok=True)
            command = [compiler, f"--trust={args.trust}", "-j1",
                       "-DautoImplicit=false", "-Ddebug.skipKernelTC=false",
                       "-o", str(out), str(relative)]
            print(f"VERIFY {module}", flush=True)
            log.write("\n$ " + " ".join(command) + "\n")
            started = time.monotonic()
            result = subprocess.run(command, cwd=source_root, env=environment,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=1800)
            seconds = round(time.monotonic() - started, 3)
            log.write(result.stdout)
            log.write(f"EXIT {result.returncode}\n")
            log.flush()
            if result.returncode:
                print(result.stdout)
                raise SystemExit(f"Verification failed: {module}")
            found = {}
            for name, body in AUDIT.findall(result.stdout):
                axioms = {a.strip() for a in body.split(",") if a.strip()}
                if not axioms <= ALLOWED_AXIOMS:
                    raise SystemExit(f"Unapproved axiom dependency in {name}: {sorted(axioms)}")
                found[name] = sorted(axioms)
            for name in NO_AXIOMS.findall(result.stdout):
                found[name] = []
            expected = expected_audits[module]
            if group != "KellerKlein" and (
                    len(found) != len(expected) or
                    not all(any(n == e or n.endswith("." + e) for n in found) for e in expected)):
                raise SystemExit(f"Axiom audit output of {module} does not match its #print axioms commands")
            if found:
                audit_text.append(f"-- {module}\n" + result.stdout)
            audits.update(found)
            records.append({"module": module, "group": group, "exit_code": 0, "seconds": seconds,
                            "axiom_audits": len(found)})
    missing = CENTRAL - audits.keys()
    if missing:
        raise SystemExit(f"Central axiom audits missing: {sorted(missing)}")
    for relative, expected in hashes.items():
        if digest(PROJECT / relative) != expected:
            raise SystemExit(f"Source changed during verification: {relative}")
    (reports / "axioms.txt").write_text("\n".join(audit_text))
    group_counts = {group: sum(1 for m in order if sources[m][0] == group)
                    for group in ("KellerKlein",) + FLAT_GROUPS}
    certificate = {
        "status": "PASS",
        "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "compiler": version, "fresh_output": str(output_root),
        "dependency_policy": "Pinned clean source checkouts; compiled dependency caches reused "
                             "read-only; cache-to-source correspondence is trusted, not rechecked",
        "import_trust_level": args.trust, "new_declarations_kernel_checked": True,
        "compiler_options": [f"--trust={args.trust}", "-j1", "-DautoImplicit=false",
                             "-Ddebug.skipKernelTC=false"],
        "dependencies": dependencies, "module_count": len(order), "group_module_counts": group_counts,
        "axiom_audit_count": len(audits), "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "central_declarations": sorted(CENTRAL),
        "verifier_sha256": digest(__file__), "builds": records, "axioms": audits,
        "source_sha256": hashes,
        "scope": "Kernel-checked Lean statements only. The probability bridge takes its Gaussian, "
                 "Hollom-Portier, exponential and above-one tail inputs as explicit hypotheses; the "
                 "probability cap optima and the interval certificates are outside this check.",
    }
    (reports / "certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
    print(f"PASS: {len(order)} fresh module builds and {len(audits)} axiom audits; "
          "every audited declaration uses only propext, Classical.choice and Quot.sound.")
    print(f"Certificate: {reports / 'certificate.json'}")


if __name__ == "__main__":
    main()
