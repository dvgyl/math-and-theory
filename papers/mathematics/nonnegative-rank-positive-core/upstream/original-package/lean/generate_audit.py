#!/usr/bin/env python3
"""Generate an explicit type and transitive axiom audit of every source declaration."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent


def declarations(path):
    scopes = []
    found = []
    for line in path.read_text().splitlines():
        scope = re.match(r"^(namespace|section)(?:\s+(\S+))?\s*$", line)
        if scope:
            scopes.append((scope.group(1), scope.group(2) or ""))
            continue
        if re.match(r"^end(?:\s+\S+)?\s*$", line):
            if not scopes:
                raise ValueError(f"Unmatched scope in {path}")
            scopes.pop()
            continue
        decl = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([\w'.]+)", line)
        if decl:
            namespace = [name for kind, name in scopes if kind == "namespace"]
            found.append((decl.group(1), ".".join(namespace + [decl.group(2)])))
    if scopes:
        raise ValueError(f"Unclosed namespace in {path}")
    return found


def main():
    paths = sorted((ROOT / "MatCKronecker").glob("*.lean"))
    decls = [d for p in paths for d in declarations(p)]
    names = [name for _, name in decls]
    assert len(set(names)) == len(names)
    lines = ["module", "", "import MatCKronecker", "",
             "-- Actual definitions of the factorization relation and entrywise predicates.",
             "#print MatCKronecker.EntryNonneg", "#print MatCKronecker.HasNMF",
             "#print MatCKronecker.RationalEntries", ""]
    for kind, name in decls:
        lines += [f"-- {kind}", f"#check @{name}", f"#print axioms {name}", ""]
    (ROOT / "AxiomAudit.lean").write_text("\n".join(lines))
    print(f"Audit lists {len(decls)} declarations, including {sum(k in ('theorem','lemma') for k,_ in decls)} theorems.")


if __name__ == "__main__":
    main()
