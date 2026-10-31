#!/usr/bin/env python3
"""Fresh Lean build, axiom audit and exact checks for this package.

Run from any directory, in a fresh copy of the package:

    python3 verify.py --output /tmp/singer-orbit-blocking-verification

The Lean step fetches the pinned Mathlib cache for the imported modules, builds the
library, including the kernel-checked search, runs Audit.lean, requires every declaration
named in theorem-map.json to depend only on propext, Classical.choice and Quot.sound, and
requires the module-wide audit in Audit.lean to report no other axiom. The exact step runs
the standard-library checker on the witness. Use --skip-lean to run only the exact step.
"""
import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / "lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|sorryAx|admit|axiom|native_decide|implemented_by|unsafe|"
                       r"extern|skipKernelTC|skipCheck)\b|Lean\.ofReduce[A-Z]\w*")
REPORT = re.compile(r"^'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|"
                    r"does not depend on any axioms)$", re.M)
SUMMARY = re.compile(r"SINGER_AXIOM_SUMMARY (\{.*\})")


def strip_comments(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            else:
                string = text[i] != '"'
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string, i = True, i + 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise SystemExit("Unterminated Lean comment or string")
    return "".join(out)


def lean_sources():
    return sorted(p for p in LEAN.rglob("*.lean") if ".lake" not in p.parts)


def scan_sources():
    for path in lean_sources():
        if FORBIDDEN.search(strip_comments(path.read_text())):
            raise SystemExit(f"Unaccepted proof construction in {path.relative_to(ROOT)}")
    return [p.relative_to(ROOT).as_posix() for p in lean_sources()]


def run(command, cwd, log):
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        stream.write(result.stdout)
    if result.returncode:
        sys.stdout.write(result.stdout[-4000:])
        raise SystemExit(f"Command failed: {' '.join(command)}")
    return result.stdout


def lean_step(out, reuse):
    if (LEAN / ".lake/build").exists() and not reuse:
        raise SystemExit("A local Lean build already exists; use a fresh copy or --reuse-build.")
    imports = set()
    for path in lean_sources():
        imports.update(re.findall(r"^import (Mathlib[\w.]*)\s*$", path.read_text(), re.M))
    run(["lake", "exe", "cache", "get", *sorted(imports)], LEAN, out / "cache.log")
    start = time.time()
    run(["lake", "build"], LEAN, out / "build.log")
    build_seconds = round(time.time() - start)
    text = run(["lake", "env", "lean", "Audit.lean"], LEAN, out / "axioms.log")
    reports = {}
    for name, axioms in REPORT.findall(text):
        reports[name] = sorted(a.strip() for a in axioms.split(",") if a.strip())
    targets = json.loads((ROOT / "theorem-map.json").read_text())["audited_declarations"]
    missing = sorted(set(targets) - set(reports))
    extra = sorted(set(reports) - set(targets))
    bad = {name: axioms for name, axioms in reports.items() if not set(axioms) <= ALLOWED}
    summaries = [json.loads(s) for s in SUMMARY.findall(text)]
    if missing or extra or bad or "error" in text or len(summaries) != 1:
        raise SystemExit(f"Axiom audit failed: missing={missing} extra={extra} bad={bad}")
    summary = summaries[0]
    if summary["rejected"] or set(summary["allowed_axioms"]) != ALLOWED:
        raise SystemExit(f"Module-wide axiom audit failed: {summary}")
    return {"audited_declarations": len(reports),
            "axioms": sorted(set().union(*reports.values())),
            "module_audit": {"modules": summary["modules"],
                             "declarations": summary["declarations"],
                             "rejected": summary["rejected"]},
            "build_seconds": build_seconds}


def exact_step(out):
    result = json.loads(run([sys.executable, "-I", str(ROOT / "certificate/check_singer.py"),
                             str(ROOT / "witnesses/witness21.json")], ROOT,
                            out / "check_singer.json"))
    if result.get("status") != "PASS":
        raise SystemExit("Exact check failed")
    return {"witness": result["witness"], "cap_four_search": result["cap_four_search"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, default=ROOT / ".verification")
    parser.add_argument("--skip-lean", action="store_true")
    parser.add_argument("--reuse-build", action="store_true")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = {"lean_sources": scan_sources()}
    if not args.skip_lean:
        report["lean"] = lean_step(out, args.reuse_build)
    report["exact"] = exact_step(out)
    (out / "report.json").write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "lean": "lean" in report,
                      "audited_declarations": report.get("lean", {}).get("audited_declarations"),
                      "search_nodes": report["exact"]["cap_four_search"]["nodes"]}))


if __name__ == "__main__":
    main()
