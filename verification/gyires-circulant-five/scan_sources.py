#!/usr/bin/env python3
"""Scan this family's Lean source for proof bypasses.

Only the ten Challenge placeholders are permitted.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[2] / "lean"
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
            depth += 1
            i += 2
        elif depth > 0 and text.startswith("-/", i):
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


files = sorted((root / "MathAndTheory/Mathematics/GyiresCirculant5").rglob("*.lean"))
files += [root / "Challenges/GyiresCirculant5.lean", root / "Solutions/GyiresCirculant5.lean"]
problems, permitted = [], []
for path in files:
    code = strip_comments_and_strings(path.read_text())
    for lineno, line in enumerate(code.splitlines(), 1):
        for match in pattern.finditer(line):
            rel = path.relative_to(root).as_posix()
            entry = f"{rel}:{lineno}: {match.group(1)}"
            if match.group(1) == "sorry" and rel == "Challenges/GyiresCirculant5.lean":
                permitted.append(entry)
            else:
                problems.append(entry)
        if "skipKernelTC" in line or "skipCheck" in line:
            problems.append(f"{path}:{lineno}: kernel-check option")
print(f"Lean source files: {len(files)}")
print(f"Permitted Challenge placeholders: {len(permitted)}")
print(f"Other bypass tokens: {len(problems)}")
for item in problems:
    print(item)
ok = not problems and len(permitted) == 10
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
