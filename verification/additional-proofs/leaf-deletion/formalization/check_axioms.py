#!/usr/bin/env python3
"""Reject incomplete or disallowed Lean #print axioms output.

This checks the audit's text and coverage. It does not run Lean, validate
proof terms, or establish that a supplied historical log is authentic.
"""
import re
import sys
from pathlib import Path

EXPECTED = frozenset({
    'LeafMode.Result.counterexample',
    'LeafMode.Result.question_8_1',
    'LeafMode.Result.tree_unique_mode',
    'LeafMode.Result.deleted_unique_mode',
    'LeafMode.coeff_dominationPolynomial',
    'LeafMode.Cert.f_power',
    'LeafMode.Cert.g_power',
    'LeafMode.Cert.h_power',
    'LeafMode.Cert.p_trend_checked',
    'LeafMode.Cert.q_trend_checked',
})
ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT = re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]$")
NO_AXIOMS = re.compile(r"^'([^']+)' does not depend on any axioms$")


def validate(output):
    """Return the declaration-to-axioms map, or raise ValueError."""
    if not output.strip():
        raise ValueError("empty axiom audit output")
    reports = {}
    for line_number, line in enumerate(output.splitlines(), 1):
        line = line.strip()
        match = REPORT.fullmatch(line)
        none = NO_AXIOMS.fullmatch(line)
        if match:
            name, body = match.groups()
            axioms = [item.strip() for item in body.split(",")] if body.strip() else []
            if any(not item for item in axioms):
                raise ValueError(f"malformed axiom list on line {line_number}")
        elif none:
            name = none.group(1)
            axioms = []
        elif "axiom" in line.lower():
            raise ValueError(f"unrecognized axiom report on line {line_number}")
        else:
            # Other audit text can include definitions and theorem types.
            continue
        if name not in EXPECTED:
            raise ValueError(f"unexpected audited declaration: {name}")
        if name in reports:
            raise ValueError(f"duplicate axiom report: {name}")
        if len(axioms) != len(set(axioms)):
            raise ValueError(f"duplicate axiom in report: {name}")
        forbidden = set(axioms) - ALLOWED
        if forbidden:
            raise ValueError(f"forbidden axioms for {name}: {', '.join(sorted(forbidden))}")
        reports[name] = tuple(axioms)
    missing = EXPECTED - reports.keys()
    if missing:
        raise ValueError(f"missing axiom reports: {', '.join(sorted(missing))}")
    return reports


def main(argv):
    if len(argv) != 1:
        print("usage: check_axioms.py AUDIT_OUTPUT", file=sys.stderr)
        return 2
    try:
        reports = validate(Path(argv[0]).read_text(encoding="utf-8", errors="strict"))
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Axiom audit rejected: {error}", file=sys.stderr)
        return 1
    print(f"Axiom audit accepted: {len(reports)} required declarations; only allowed axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
