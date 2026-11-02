"""Validate the complete defining-module Lean axiom audit, including source coverage.

Usage: python3 scripts/check_axiom_audit.py --log build.log --project lean [--output inventory.json]
The script checks the audit output; it does not replace running Lean.
"""
from pathlib import Path
import argparse
import json
import re

# Modules that only import other modules and print axioms; they define nothing.
IMPORT_ONLY = {"HarmonicBoundary.WedgeAudit", "HarmonicBoundary.LocalFeasibility"}


def strip_comments(source):
    source = re.sub(r"/-.*?-/", " ", source, flags=re.S)
    return re.sub(r"--[^\n]*", " ", source)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = args.log.read_text()
    declarations = [json.loads(x) for x in re.findall(r"HB_AXIOM_DECL (\{[^\n]*\})", text)]
    summaries = [json.loads(x) for x in re.findall(r"HB_AXIOM_SUMMARY (\{[^\n]*\})", text)]
    if len(summaries) != 1:
        raise SystemExit(f"Expected exactly one audit summary; got {len(summaries)}")
    summary = summaries[0]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert set(summary["allowed_axioms"]) == allowed
    assert not summary["rejected"], summary["rejected"]
    assert len(declarations) == summary["total"]
    names = [d["name"] for d in declarations]
    assert len(names) == len(set(names)), "Duplicate declaration records"
    for d in declarations:
        assert set(d["axioms"]) <= allowed, d
        assert d["kind"] != "axiom", d
    production = sorted((args.project / "HarmonicBoundary").rglob("*.lean"))
    production = [p for p in production if p.name != "AxiomAudit.lean"]
    all_modules = {".".join(p.relative_to(args.project).with_suffix("").parts) for p in production}
    aggregate = {line.removeprefix("import ").strip()
                 for line in (args.project / "HarmonicBoundary.lean").read_text().splitlines() if line.strip()}
    top = {m for m in all_modules if m.count(".") == 1}
    assert aggregate == top, "Root module does not import every top-level module"
    local = {m for m in all_modules if m.startswith("HarmonicBoundary.LocalSystems.")}
    feasibility = (args.project / "HarmonicBoundary" / "LocalFeasibility.lean").read_text()
    assert {l.removeprefix("import ").strip() for l in feasibility.splitlines()
            if l.startswith("import ")} == local, "LocalFeasibility does not import every local module"
    expected_modules = all_modules - IMPORT_ONLY
    assert set(summary["modules"]) == expected_modules
    assert {d["module"] for d in declarations} == expected_modules
    banned = re.compile(r"\b(sorry|admit|native_decide|implemented_by|extern|ofReduceBool)\b|^\s*axiom\s", re.M)
    source_named = []
    for p in production:
        source = strip_comments(p.read_text())
        assert not banned.search(source), f"Banned construct in {p}"
        module = ".".join(p.relative_to(args.project).with_suffix("").parts)
        if module in IMPORT_ONLY:
            assert not re.search(r"^(?:private\s+)?(?:theorem|def|abbrev|structure|inductive|instance|lemma)\s",
                                 source, re.M), f"Declaration in import-only module {p}"
        for match in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
                                 r"(?:abbrev|def|theorem|lemma|structure|inductive)\s+([\w.]+)",
                                 source, re.M):
            source_named.append(match.group(1))
    missing = [s for s in source_named if not any(n == "HarmonicBoundary." + s or n.endswith("." + s)
                                                   for n in names)]
    assert not missing, sorted(missing)[:20]
    for module, count in summary["counts"].items():
        assert count == sum(d["module"] == module for d in declarations)
    assert "error:" not in text.lower(), "Lean build contains an error"
    assert "Build completed successfully" in text
    result = {
        "verified": True,
        "all_environment_declarations": len(declarations),
        "source_named_declarations": len(source_named),
        "modules": sorted(expected_modules),
        "counts": summary["counts"],
        "observed_axioms": sorted({a for d in declarations for a in d["axioms"]}),
        "declarations": declarations,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=1) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("declarations", "counts")}, indent=2))


if __name__ == "__main__":
    main()
