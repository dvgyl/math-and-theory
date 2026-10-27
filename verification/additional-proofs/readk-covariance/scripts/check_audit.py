#!/usr/bin/env python3
"""Require one permitted axiom report for each selected theorem."""

from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check(text):
    expected = (ROOT / "verification/theorem-list.txt").read_text().splitlines()
    requested = re.findall(r"^#print axioms (\S+)\s*$", (ROOT / "Audit.lean").read_text(), re.M)
    if not expected or len(expected) != len(set(expected)) or expected != requested:
        raise ValueError("The theorem list must match the audit requests exactly.")
    pattern = re.compile(
        r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
        re.M,
    )
    reports = list(pattern.finditer(text))
    counts = Counter(report.group(1) for report in reports)
    if counts != Counter(expected):
        missing = sorted(set(expected) - set(counts))
        unexpected = sorted(set(counts) - set(expected))
        duplicates = sorted(name for name, count in counts.items() if count != 1)
        raise ValueError(f"Invalid report coverage. Missing: {missing}. Unexpected: {unexpected}. Duplicates: {duplicates}.")
    remainder = pattern.sub("", text)
    if re.search(r"depends on axioms|does not depend on any axioms|(^|: )error\b", remainder, re.M):
        raise ValueError("The audit contains a malformed report or a compiler error.")
    for report in reports:
        raw = report.group(2)
        axioms = [] if raw is None or not raw.strip() else [name.strip() for name in raw.split(",")]
        if any(not name for name in axioms) or len(axioms) != len(set(axioms)) or not set(axioms) <= ALLOWED:
            raise ValueError(f"Invalid axiom list for {report.group(1)}: {axioms}")
    for path in [ROOT / "Research.lean", ROOT / "Audit.lean", *sorted((ROOT / "Research").glob("*.lean"))]:
        match = re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", path.read_text())
        if match:
            raise ValueError(f"Disallowed source token in {path.relative_to(ROOT)}: {match.group()}")
    return len(expected)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 scripts/check_audit.py AUDIT_LOG")
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (OSError, ValueError) as error:
        raise SystemExit(str(error))
    print(f"PASS: exactly one axiom report for each of {count} requested theorems.")
    print(f"PASS: all reported axioms belong to {sorted(ALLOWED)}.")
    print("PASS: the project source scan found no prohibited proof tokens.")
