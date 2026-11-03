"""Validate a complete defining-module Lean axiom audit, including source coverage.

Usage: python3 scripts/check_axiom_audit.py --log build.log --project lean [--output inventory.json]
The log must contain `lake build Main ProjectAxiomAudit`.
The script checks the audit output; it does not replace running Lean.
"""
from pathlib import Path
import argparse
import json
import re


def strip_comments(text):
    """Remove Lean line and nested block comments and string literals."""
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
            elif text[i] == '"':
                string, i = False, i + 1
            else:
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
    return "".join(out)


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
    auxiliary = re.compile(r"(^|\.)(_cstage\d*|_spec_\d+|_elambda_\d+|_lambda_\d+|_closed_\d+|_boxed|_rarg)(\.|$)")
    for d in declarations:
        assert d["codegen_auxiliary"] == bool(auxiliary.search(d["name"])), d
        if d["codegen_auxiliary"]:
            # Lean 4.19 code-generation auxiliaries: compiler placeholders only.
            assert all(a in allowed or a == "lcProof" or auxiliary.search(a) for a in d["axioms"]), d
        else:
            assert set(d["axioms"]) <= allowed, d
            assert d["kind"] != "axiom", d
    assert summary["codegen_auxiliaries"] == sum(d["codegen_auxiliary"] for d in declarations)
    proper = [d for d in declarations if not d["codegen_auxiliary"]]
    # The nine content modules are the top-level Lean files other than the
    # aggregate `Main`, the selected-theorem `AxiomAudit` script, this audit
    # module and the Lake configuration.
    excluded = {"Main.lean", "AxiomAudit.lean", "ProjectAxiomAudit.lean", "lakefile.lean"}
    production = sorted(p for p in args.project.glob("*.lean") if p.name not in excluded)
    expected_modules = {p.stem for p in production}
    assert len(expected_modules) == 9, sorted(expected_modules)
    # The aggregate module may only import the production modules.
    aggregate = strip_comments((args.project / "Main.lean").read_text()).split()
    assert len(aggregate) % 2 == 0 and all(w == "import" for w in aggregate[0::2]), \
        "Unaudited aggregate declarations"
    assert set(aggregate[1::2]) == expected_modules, "Aggregate imports differ from the modules"
    assert set(summary["modules"]) == expected_modules
    assert {d["module"] for d in declarations} == expected_modules
    banned = re.compile(r"\b(sorry|admit|native_decide|implemented_by|extern|unsafe)\b"
                        r"|Lean\.ofReduce\w*|^\s*axiom\s", re.M)
    source_named = []
    for p in production + [args.project / "Main.lean", args.project / "AxiomAudit.lean",
                           args.project / "ProjectAxiomAudit.lean"]:
        source = strip_comments(p.read_text())
        assert not banned.search(source), f"Banned construct in {p}"
        if p.name in ("Main.lean", "AxiomAudit.lean", "ProjectAxiomAudit.lean"):
            continue
        for match in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
                                 r"(?:abbrev|def|theorem|lemma|structure)\s+([\w.]+)",
                                 source, re.M):
            source_named.append(match.group(1))
    # Declarations live in the modules' namespaces and nested namespaces.
    missing = [s for s in source_named
               if not any(n == s or n.endswith("." + s) for n in names)]
    assert not missing, sorted(missing)
    for module, count in summary["counts"].items():
        assert count == sum(d["module"] == module for d in declarations)
    assert "error: " not in text.lower(), "Lean build contains an error"
    assert "Build completed successfully" in text
    result = {
        "verified": True,
        "all_environment_declarations": len(declarations),
        "declarations_other_than_codegen_auxiliaries": len(proper),
        "codegen_auxiliaries": len(declarations) - len(proper),
        "codegen_auxiliaries_using_lcProof": sum("lcProof" in d["axioms"] for d in declarations),
        "source_named_declarations": len(source_named),
        "observed_axioms_outside_codegen_auxiliaries": sorted({a for d in proper for a in d["axioms"]}),
        "modules": sorted(expected_modules),
        "counts": summary["counts"],
        "declarations": declarations,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "declarations"}, indent=2))


if __name__ == "__main__":
    main()
