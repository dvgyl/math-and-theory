"""Check the output of `lake env lean -j1 ../verification/gyires-circulant-five/AxiomAudit.lean`.

Usage (from the lean/ folder):

    lake env lean -j1 ../verification/gyires-circulant-five/AxiomAudit.lean > ../verification/gyires-circulant-five/axiom-audit.log
    python3 ../verification/gyires-circulant-five/check_axioms.py ../verification/gyires-circulant-five/axiom-audit.log

Every theorem listed in AxiomAudit.lean must appear in the output and may depend only on
Lean's three standard axioms; the scan of all declarations must report no declaration with
another axiom. Exits nonzero otherwise.
"""
import pathlib
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

here = pathlib.Path(__file__).resolve().parent
expected = re.findall(r"^#print axioms (\S+)", (here / "AxiomAudit.lean").read_text(), re.M)
text = pathlib.Path(sys.argv[1]).read_text()

found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", text, re.S):
    found[name] = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()

missing = [n for n in expected if n not in found]
bad = {n: sorted(found[n] - ALLOWED) for n in expected if n in found and found[n] - ALLOWED}
errors = [l for l in text.splitlines() if re.search(r"(^|: )error\b", l)]
scan = re.search(r"declaration scan: (\d+) declarations", text)
scan_bad = re.search(r"declaration scan: declarations with non-standard axioms: (\d+)", text)
scan_used = re.search(r"declaration scan: axioms used: \[(.*?)\]", text, re.S)
scan_axioms = {a.strip() for a in scan_used.group(1).split(",") if a.strip()} if scan_used else None

print(f"theorems listed: {len(expected)}; reported: {sum(n in found for n in expected)}")
used = set().union(*found.values()) if found else set()
print("axioms used by the listed theorems:", ", ".join(sorted(used)) or "none")
if scan:
    print(f"declarations scanned: {scan.group(1)}; "
          f"with non-standard axioms: {scan_bad.group(1) if scan_bad else '?'}")
    print("axioms used by all scanned declarations:", ", ".join(sorted(scan_axioms or [])) or "none")
for n in missing:
    print("MISSING:", n)
for n, a in bad.items():
    print("NON-STANDARD AXIOMS:", n, a)
for l in errors:
    print("ERROR LINE:", l)
scan_ok = (scan is not None and int(scan.group(1)) > 0 and scan_bad is not None and scan_bad.group(1) == "0"
           and scan_axioms is not None and scan_axioms <= ALLOWED)
if not scan_ok:
    print("DECLARATION SCAN: missing or failed")
ok = bool(expected) and len(expected) == len(set(expected)) and not missing and not bad and not errors and scan_ok
print("RESULT:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
