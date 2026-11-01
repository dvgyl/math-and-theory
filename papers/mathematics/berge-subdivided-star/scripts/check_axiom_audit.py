"""Validate a complete defining-module Lean axiom audit, including source coverage.

Usage: python3 scripts/check_axiom_audit.py --log build.log --project lean [--output inventory.json]
The script checks the audit output; it does not replace running Lean.
"""
from pathlib import Path
import argparse
import json
import re


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = args.log.read_text()
    declarations = [json.loads(x) for x in re.findall(r"OPT_B_AXIOM_DECL (\{[^\n]*\})", text)]
    summaries = [json.loads(x) for x in re.findall(r"OPT_B_AXIOM_SUMMARY (\{[^\n]*\})", text)]
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
    aggregate = (args.project / "BergeBroom.lean").read_text().strip()
    assert aggregate == "import BergeBroom.Main", "Unaudited aggregate declarations"
    production = sorted((args.project / "BergeBroom").rglob("*.lean"))
    production = [p for p in production if p.name != "AxiomAudit.lean"]
    expected_modules = {
        ".".join(p.relative_to(args.project).with_suffix("").parts) for p in production
    }
    assert set(summary["modules"]) == expected_modules
    assert {d["module"] for d in declarations} == expected_modules
    banned = re.compile(r"\b(sorry|admit|native_decide|implemented_by|extern)\b|^\s*axiom\s", re.M)
    source_named = []
    for p in production:
        source = p.read_text()
        assert not banned.search(source), f"Banned construct in {p}"
        for match in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
                                 r"(?:abbrev|def|theorem|lemma|structure|instance)\s+([\w.]+)",
                                 source, re.M):
            source_named.append(match.group(1))
    # Declarations live in namespace `Berge` (some in nested namespaces), so match by suffix.
    missing = [s for s in source_named if not any(n == "Berge." + s or n.endswith("." + s)
                                                   for n in names)]
    assert not missing, sorted(missing)
    for module, count in summary["counts"].items():
        assert count == sum(d["module"] == module for d in declarations)
    assert "error: " not in text.lower(), "Lean build contains an error"
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
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "declarations"}, indent=2))


if __name__ == "__main__":
    main()
