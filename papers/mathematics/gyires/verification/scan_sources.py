#!/usr/bin/env python3
"""Scan this family's Lean source for proof bypasses.

Only the eighteen listed Challenge placeholders are permitted.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[4] / "lean"
TOKENS = ["sorry", "admit", "axiom", "native_decide", "implemented_by", "extern", "unsafe", "ofReduceBool"]
pattern = re.compile(r"(?<![\w.'])(" + "|".join(TOKENS) + r")(?![\w'])")

def strip_comments_and_strings(text: str) -> str:
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            out.append(" ")
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            out.append(" ")
            depth -= 1
            i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


proof_directories = [
    "MathAndTheory/Mathematics/Gyires/CirculantFive",
    "MathAndTheory/Mathematics/Gyires",
]
proof_groups = {name: sorted(path for path in (root / name).rglob("*.lean")
                            if name.endswith("CirculantFive") or "CirculantFive" not in path.parts)
                for name in proof_directories}
proof_files = [path for group in proof_groups.values() for path in group]
expected_placeholders = {
    "Challenges/Mathematics/Gyires/CirculantFive.lean": 18,
}
interfaces = list(expected_placeholders) + [
    "Solutions/Mathematics/Gyires/CirculantFive.lean", "Solutions/Mathematics/Gyires/FourBlock.lean",
    "Solutions/Mathematics/Gyires/ExceptionalVector.lean"
]
missing = [name for name in interfaces if not (root / name).is_file()]
missing += [name for name, group in proof_groups.items() if not group]
files = proof_files + [root / name for name in interfaces if (root / name).is_file()]
problems, permitted = [], []
placeholder_counts = dict.fromkeys(expected_placeholders, 0)
for path in files:
    code = strip_comments_and_strings(path.read_text())
    rel = path.relative_to(root).as_posix()
    if rel in expected_placeholders:
        for module in re.findall(r"(?<![\w.'])import\s+(?:all\s+)?([^\s]+)", code):
            if module.split(".")[0] not in {"Init", "Lean", "Std", "Mathlib"}:
                problems.append(f"{rel}: local Challenge import: {module}")
    for lineno, line in enumerate(code.splitlines(), 1):
        for match in pattern.finditer(line):
            rel = path.relative_to(root).as_posix()
            entry = f"{rel}:{lineno}: {match.group(1)}"
            if match.group(1) == "sorry" and rel in expected_placeholders:
                permitted.append(entry)
                placeholder_counts[rel] += 1
            else:
                problems.append(entry)
        if "skipKernelTC" in line or "skipCheck" in line:
            problems.append(f"{path}:{lineno}: kernel-check option")
print(f"Lean source files: {len(files)}")
print(f"Permitted Challenge placeholders: {len(permitted)}")
print(f"Other bypass tokens: {len(problems)}")
for item in problems:
    print(item)
for name in missing:
    print("MISSING:", name)
ok = bool(proof_files) and not problems and not missing and placeholder_counts == expected_placeholders
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
