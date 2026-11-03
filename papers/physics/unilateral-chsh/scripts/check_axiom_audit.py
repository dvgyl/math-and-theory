"""Validate the whole-project Lean axiom audit, including source coverage.

Usage: python3 scripts/check_axiom_audit.py --log build.log --project lean [--output inventory.json]
The script checks the audit output printed by `lake build UnilateralAudit`;
it does not replace running Lean.
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


DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(?:abbrev|def|theorem|lemma|structure|instance|inductive)\s+([\w.']+)", re.M)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    project = args.project
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

    # The audited module list, modules.txt, the lakefile roots and the source files agree.
    listed = [l.strip() for l in (project / "modules.txt").read_text().splitlines()
              if l.strip() and not l.lstrip().startswith("#")]
    files = sorted(p.stem for p in (project / "Lean").glob("*.lean") if p.stem != "UnilateralAxiomAudit")
    assert sorted(listed) == files, "modules.txt differs from the source files"
    lakefile = (project / "lakefile.toml").read_text()
    main_roots = re.search(r'name = "UnilateralCHSHLib".*?roots = \[(.*?)\]', lakefile, re.S).group(1)
    assert re.findall(r'"(\w+)"', main_roots) == listed, "Lakefile roots differ from modules.txt"
    assert summary["modules"] == listed, "Audited modules differ from modules.txt"
    audit_source = strip_comments((project / "Lean" / "UnilateralAxiomAudit.lean").read_text())
    assert re.findall(r"^import (\w+)\s*$", audit_source, re.M)[:len(listed)] == listed

    banned = re.compile(r"\b(sorry|admit|native_decide|implemented_by|extern|unsafe)\b"
                        r"|Lean\.ofReduce\w*|ofReduceBool|^\s*axiom\s", re.M)
    source_named = {}
    for module in listed + ["UnilateralAxiomAudit"]:
        source = strip_comments((project / "Lean" / f"{module}.lean").read_text())
        assert not banned.search(source), f"Banned construct in {module}"
        if module != "UnilateralAxiomAudit":
            source_named[module] = DECLARATION.findall(source)
    for module, count in summary["counts"].items():
        assert count == sum(d["module"] == module for d in declarations)
        if count == 0:
            assert not source_named[module], f"{module} declares names but none were audited"
    missing = [(m, s) for m, found in source_named.items() for s in found
               if not any(n == s or n.endswith("." + s) for n in names)]
    assert not missing, sorted(missing)
    assert not re.search(r"^error", text, re.M | re.I) and "error: " not in text.lower(), \
        "Lean build contains an error"
    assert "Build completed successfully" in text
    result = {
        "verified": True,
        "all_environment_declarations": len(declarations),
        "declarations_other_than_codegen_auxiliaries": len(proper),
        "codegen_auxiliaries": len(declarations) - len(proper),
        "codegen_auxiliaries_using_lcProof": sum("lcProof" in d["axioms"] for d in declarations),
        "source_named_declarations": sum(len(v) for v in source_named.values()),
        "modules_without_declarations": sorted(m for m, c in summary["counts"].items() if c == 0),
        "observed_axioms_outside_codegen_auxiliaries": sorted({a for d in proper for a in d["axioms"]}),
        "modules": listed,
        "counts": summary["counts"],
        "declarations": declarations,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "declarations"}, indent=2))


if __name__ == "__main__":
    main()
