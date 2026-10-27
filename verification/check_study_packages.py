"""Check pinned study packages and complete source verification records."""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import re

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PIN419 = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
PIN435 = "56a005855ea17e0b0958f73ec801ae140b0a1679"
PROFILES = {
    "sharp-eighth": ("4.19.0", PIN419, 2, 12, "Audit.lean"),
    "universal-embezzlement": ("4.19.0", PIN419, 2, 15, "Audit.lean"),
    "galvin-zhang": ("4.19.0", PIN419, 18, 8, "Audit.lean"),
    "asymmetric-tutte": ("4.32.1", "520045ab14e26149ee970e2e617ca04b09bde5d6", 22, 6, "Audit.lean"),
}
REPORT = re.compile(r"^'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M)
HASH = re.compile(r"[0-9a-f]{64}\Z")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def parse_reports(text):
    require(not re.search(r"\b(?:sorry|warning|error)\b", text), "Compiler diagnostics are present.")
    reports = []
    remainder = REPORT.sub("", text)
    require(not re.search(r"depends on axioms|does not depend on any axioms|\bsorryAx\b", remainder),
            "An axiom report is malformed.")
    for match in REPORT.finditer(text):
        raw = match[2] or ""
        tokens = [s.strip() for s in raw.split(",")] if raw.strip() else []
        require(all(tokens) and len(tokens) == len(set(tokens)),
                "An axiom list has an empty or repeated entry.")
        axioms = sorted(tokens)
        require(set(axioms) <= ALLOWED, "A theorem uses an unpermitted axiom.")
        reports.append({"declaration": match[1], "axioms": axioms})
    return reports


def check_audit(package, name, output):
    """Require every report requested by the package audit."""
    audit = Path(package) / PROFILES[name][4]
    requested = re.findall(r"^#print axioms\s+(\S+)\s*$", audit.read_text(), re.M)
    reports = parse_reports(output)
    require(bool(requested) and Counter(requested) == Counter(r["declaration"] for r in reports),
            "The audit report coverage differs.")
    return len(reports)


def check(package, name, manifest):
    """Check exact source coverage, dependency pins, and compiler evidence."""
    package = Path(package)
    version, pin, count, report_count, audit = PROFILES[name]
    require(manifest.get("lean_version") == version and manifest.get("mathlib_revision") == pin,
            "The recorded toolchain differs.")
    require((package / "lean-toolchain").read_text().strip() == "leanprover/lean4:v" + version,
            "The Lean toolchain differs.")
    lock = json.loads((package / "lake-manifest.json").read_text())
    dependencies = lock.get("packages", [])
    require(bool(dependencies) and len({p["name"] for p in dependencies}) == len(dependencies),
            "The dependency list is empty or repeated.")
    require(all(p.get("type") == "git" and re.fullmatch(r"[0-9a-f]{40}", p.get("rev", ""))
                for p in dependencies), "A dependency is not pinned to a commit.")
    mathlib = [p for p in dependencies if p["name"] == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0]["rev"] == pin, "The Mathlib revision differs.")
    if name == "asymmetric-tutte":
        upstream = [p for p in dependencies if p["name"].strip("«»") == "tutte-threshold"]
        require(len(upstream) == 1 and upstream[0]["rev"] == "636352f0fef47b19d7d5de364858ccee2317fd66",
                "The upstream Tutte revision differs.")
        require(not (package / "Results").exists(), "The external Tutte source must not be bundled.")
    files = manifest["files"]
    source_names = {p for p in files if p.endswith(".lean") and p != "lakefile.lean"}
    require(len(source_names) == count, "The proof source count differs.")
    evidence = json.loads((package / "verification/source-checks.json").read_text())
    require(type(evidence.get("format_version")) is int and evidence["format_version"] == 1 and evidence.get("complete") is True,
            "The source verification record is incomplete.")
    require(evidence.get("lean_version") == version and evidence.get("mathlib_revision") == pin,
            "The source verification toolchain differs.")
    records = evidence.get("sources", [])
    require(len(records) == count and {r.get("source") for r in records} == source_names,
            "The source verification coverage differs.")
    total = 0
    audit_output = None
    for record in records:
        source = record["source"]
        require(type(record.get("compiler_exit_code")) is int and record["compiler_exit_code"] == 0
                and record.get("source_sha256") == files[source]["sha256"],
                "A source verification record differs.")
        require(isinstance(record.get("object_sha256"), str) and HASH.fullmatch(record["object_sha256"]),
                "A compiled object hash is missing.")
        log = "verification/compile/" + source[:-5].replace("/", ".") + ".txt"
        require(log in files and record.get("log_sha256") == files[log]["sha256"],
                "A compiler output record differs.")
        output = (package / log).read_text()
        reports = parse_reports(output)
        requested = re.findall(r"^#print axioms\s+(\S+)\s*$", (package / source).read_text(), re.M)
        require(Counter(requested) == Counter(r["declaration"] for r in reports)
                and record.get("axiom_reports") == reports, "A source axiom report differs.")
        total += len(reports)
        if source == audit:
            audit_output = output
    require(total == report_count and type(evidence.get("axiom_report_count")) is int
            and evidence["axiom_report_count"] == total,
            "The full axiom report count differs.")
    require(audit_output is not None, "The package audit output is missing.")
    check_audit(package, name, audit_output)
    for required in ["LICENSE", "CITATION.cff", "CITATION.bib", "README.md", "manuscript.tex", "manuscript.pdf"]:
        require(required in files, "A publication file is missing: " + required)
    return evidence


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", choices=sorted(PROFILES))
    parser.add_argument("--audit-log", required=True, type=Path)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent / "additional-proofs" / args.name
    print(json.dumps({"status": "PASS", "reports": check_audit(package, args.name, args.audit_log.read_text())}))
