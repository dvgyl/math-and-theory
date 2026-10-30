#!/usr/bin/env python3
"""Record the completed package verification without invoking Lake or a cache hook."""

from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations(path: Path) -> list[str]:
    scopes: list[tuple[str, str]] = []
    names: list[str] = []
    for line in path.read_text().splitlines():
        scope = re.match(r"^(namespace|section)(?:\s+(\S+))?\s*$", line)
        if scope:
            scopes.append((scope.group(1), scope.group(2) or ""))
            continue
        if re.match(r"^end(?:\s+\S+)?\s*$", line):
            require(bool(scopes), f"Unmatched scope end in {path.name}")
            scopes.pop()
            continue
        decl = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+([\w'.]+)", line)
        if decl:
            namespace = [name for kind, name in scopes if kind == "namespace"]
            names.append(".".join(namespace + [decl.group(1)]))
    return names


def main() -> None:
    source_paths = sorted((ROOT / "MatCP1Converse").glob("*.lean"))
    modules = {"MatCP1Converse": ROOT / "MatCP1Converse.lean"}
    modules.update({f"MatCP1Converse.{p.stem}": p for p in source_paths})
    reachable: set[str] = set()

    def visit(module: str) -> None:
        if module in reachable:
            return
        require(module in modules, f"Missing local module: {module}")
        reachable.add(module)
        for name in re.findall(r"^(?:public )?import (MatCP1Converse(?:\.[\w]+)*)$",
                               modules[module].read_text(), re.MULTILINE):
            visit(name)

    visit("MatCP1Converse")
    require(reachable == set(modules),
            f"Unexported project source modules: {sorted(set(modules) - reachable)}")

    all_theorems = sorted(name for path in source_paths for name in declarations(path))
    requested_audits = re.findall(r"^#print axioms (\S+)$",
                                 (ROOT / "AxiomAudit.lean").read_text(), re.MULTILINE)
    require(sorted(requested_audits) == all_theorems,
            "AxiomAudit.lean must cover each exported theorem exactly once")

    build_log = (ROOT / "verification/build.log").read_text()
    audit_log = (ROOT / "verification/axioms.log").read_text()
    environment_log = (ROOT / "verification/environment.log").read_text()
    require("version 4.35.0-rc3," in environment_log and
            "commit 470d5ce1400764999581fd26d5d72b00d990b0f4," in environment_log,
            "The recorded compiler does not match the pinned Lean build")
    require("Actual mathlib: 0db6cb99b412983de54b59ecc1b0b2747542cda3" in environment_log,
            "The recorded mathlib checkout does not match the pin")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc3",
            "The project toolchain file does not match the pin")
    require("Build completed successfully" in build_log, "Missing successful build record")
    require(not re.search(r"\berror:", build_log + audit_log), "Verification log contains an error")
    require("⋯" not in audit_log, "A printed theorem statement is elided")
    built = set(re.findall(r"\bBuilt (MatCP1Converse(?:\.[\w]+)*)(?=\s|$)", build_log))
    require(built == set(modules), "Fresh build log does not cover every project source module")

    audits: dict[str, list[str]] = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_log):
        axioms = [item.strip() for item in raw.split(",") if item.strip()]
        require(name not in audits, f"Repeated axiom audit: {name}")
        require(set(axioms) <= EXPECTED_AXIOMS, f"Unexpected axiom dependency for {name}: {axioms}")
        audits[name] = axioms
    require(sorted(audits) == all_theorems, "Audit log does not match the exported theorem set")

    for path in modules.values():
        require(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", path.read_text()),
                f"Forbidden proof construct in {path.relative_to(ROOT)}")

    build_started = re.search(r"^UTC: (\S+)$", environment_log, re.MULTILINE)
    require(build_started is not None, "Missing build timestamp")
    printed = re.findall(r"^#(?:print (?!axioms\b)|check @?)(\S+)$",
                         (ROOT / "AxiomAudit.lean").read_text(), re.MULTILINE)

    hashed_paths: set[Path] = set(ROOT.glob("*.lean")) | set(source_paths)
    hashed_paths.update(ROOT.glob("*.sh"))
    hashed_paths.update(ROOT.glob("*.py"))
    hashed_paths.update(ROOT.glob("*.md"))
    # The outer transcript is still receiving this script's own output. The
    # complete build, environment and axiom logs are stable and hashed below.
    hashed_paths.update(p for p in (ROOT / "verification").glob("*.log")
                        if p.name != "final_root_run.log")
    hashed_paths.update(ROOT / name for name in
                        ["lean-toolchain", "lakefile.toml", "lake-manifest.json"])

    sibling = ROOT.parent / "lean_p1"
    sibling_paths = sorted(set(sibling.glob("*.lean")) |
                           set((sibling / "MatCP1").glob("*.lean")) |
                           {sibling / name for name in
                            ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]})
    record = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "build_started_utc": build_started.group(1),
        "fresh_build_exit_code": 0,
        "axiom_audit_exit_code": 0,
        "scope": "Complete explicit dilation rank-distance/completion equivalence over every infinite field, arbitrary rectangular pencils and border sizes, distinct anchors without spectral avoidance; all structural inputs derived internally. Original barred/Kronecker correspondence remains ordinary mathematics, not Lean formalized.",
        "full_raw_dilation_theorem_formalized": True,
        "full_P1_barred_formulation_formalized": False,
        "novelty_verdict": "unresolved",
        "lean": "4.35.0-rc3",
        "lean_commit": "470d5ce1400764999581fd26d5d72b00d990b0f4",
        "mathlib": "0db6cb99b412983de54b59ecc1b0b2747542cda3",
        "reproduction_command": "bash verify.sh",
        "freshly_built_modules": sorted(built),
        "unexported_source_modules": [],
        "printed_actual_statements": printed,
        "audited_declarations": len(audits),
        "allowed_foundational_axioms": sorted(EXPECTED_AXIOMS),
        "axiom_audits": dict(sorted(audits.items())),
        "sha256": {str(path.relative_to(ROOT)): sha256(path)
                   for path in sorted(hashed_paths)},
        "local_dependency": {
            "path": "../lean_p1",
            "preserved_without_cleaning": True,
            "sha256": {str(path.relative_to(sibling)): sha256(path) for path in sibling_paths},
        },
        "hash_exclusion": "VERIFICATION.json is self-referential; verification/final_root_run.log is the still-active duplicate outer transcript. Stable environment, build and axiom logs are all hashed.",
        "evidence": "Generated after successful pinned environment checks, a clean rebuild of this package, exact-statement printing, the complete exported-theorem axiom audit, and proof-construct scans. The source, stable logs and dependency hashes are recorded. Dependency caches and the separately freshly verified cancellation package were preserved.",
    }
    (ROOT / "VERIFICATION.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Recorded {len(built)} freshly built modules and {len(audits)} kernel axiom audits.")


if __name__ == "__main__":
    main()
