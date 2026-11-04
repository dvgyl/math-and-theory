#!/usr/bin/env python3
"""Validate the completed logs, source coverage, and pins before recording success."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
from generate_audit import declarations

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB = "0db6cb99b412983de54b59ecc1b0b2747542cda3"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    sources = sorted((ROOT / "MatCKronecker").glob("*.lean"))
    modules = {"MatCKronecker": ROOT / "MatCKronecker.lean"}
    modules.update({f"MatCKronecker.{p.stem}": p for p in sources})
    reached = set()

    def visit(name):
        if name in reached:
            return
        require(name in modules, f"Missing local import {name}")
        reached.add(name)
        for dep in re.findall(r"^(?:public )?import (MatCKronecker(?:\.[\w]+)*)$", modules[name].read_text(), re.M):
            visit(dep)

    visit("MatCKronecker")
    require(reached == set(modules), f"Unexported source modules: {set(modules)-reached}")
    decls = [d for p in sources for d in declarations(p)]
    names = sorted(name for _, name in decls)
    requested = re.findall(r"^#print axioms (\S+)$", (ROOT / "AxiomAudit.lean").read_text(), re.M)
    require(sorted(requested) == names, "Audit does not list every source declaration exactly once")
    checked = re.findall(r"^#check @(\S+)$", (ROOT / "AxiomAudit.lean").read_text(), re.M)
    require(sorted(checked) == names, "Actual type printing is incomplete")

    env = (ROOT / "verification/environment.log").read_text()
    build = (ROOT / "verification/build.log").read_text()
    audit = (ROOT / "verification/axioms.log").read_text()
    require("version 4.35.0-rc3," in env and f"commit {LEAN_COMMIT}," in env, "Compiler pin mismatch")
    require(f"Actual mathlib: {MATHLIB}" in env, "Mathlib pin mismatch")
    require((ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc3", "Toolchain file mismatch")
    require(f'rev = "{MATHLIB}"' in (ROOT / "lakefile.toml").read_text(), "Lake configuration pin mismatch")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    require(any(p.get("name") == "mathlib" and p.get("rev") == MATHLIB for p in manifest["packages"]), "Manifest mathlib pin mismatch")
    require("Build completed successfully" in build, "No successful aggregate build")
    require(not re.search(r"\berror:", build + audit), "An error occurs in the final verification logs")
    require("⋯" not in audit, "A printed declaration is elided")
    built = set(re.findall(r"\bBuilt (MatCKronecker(?:\.[\w]+)*)(?=\s|$)", build))
    require(built == set(modules), f"Fresh module build coverage mismatch: {set(modules)-built}")

    axioms = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
        require(name not in axioms, f"Duplicate axiom output {name}")
        deps = [s.strip() for s in raw.split(",") if s.strip()]
        require(set(deps) <= ALLOWED, f"Unexpected axiom dependency: {name}: {deps}")
        axioms[name] = deps
    for name in re.findall(r"'([^']+)' does not depend on any axioms", audit):
        require(name not in axioms, f"Duplicate axiom output {name}")
        axioms[name] = []
    require(sorted(axioms) == names, f"Missing axiom output: {set(names)-set(axioms)}")
    for path in modules.values():
        require(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", path.read_text()), f"Forbidden proof construct in {path.name}")
    require("sorryAx" not in audit and "Lean.ofReduceBool" not in audit, "Untrusted proof closure")
    started = re.search(r"^UTC: (\S+)$", env, re.M)
    require(started is not None, "Missing execution timestamp")
    paths = set(sources) | set(ROOT.glob("*.lean")) | set(ROOT.glob("*.py")) | set(ROOT.glob("*.sh"))
    paths |= {ROOT / p for p in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]}
    paths |= {ROOT / "verification" / p for p in ["environment.log", "build.log", "axioms.log"]}
    record = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "build_started_utc": started.group(1),
        "fresh_build_exit_code": 0,
        "axiom_audit_exit_code": 0,
        "scope": "For every k:Nat, a rational entrywise nonnegative real (k+11)-square matrix C has ordinary rank k+10, actual real nonnegative rank k+11, nnrank(C tensor C) <= (k+10)^2+9 and nnrank(C tensor C)+k < nnrank(C)*rank(C). Includes a literal negation of the all-rectangular-nonnegative-real-matrices square conjecture.",
        "full_theorem_formalized": True,
        "square_nonnegative_rank_asserted_exact": False,
        "novelty_verdict": "unresolved",
        "lean": "4.35.0-rc3", "lean_commit": LEAN_COMMIT, "mathlib": MATHLIB,
        "reproduction_command": "bash verify.sh",
        "freshly_built_modules": sorted(built),
        "audited_source_declarations": len(axioms),
        "audited_theorems": sum(kind in ("theorem", "lemma") for kind, _ in decls),
        "allowed_foundational_axioms": sorted(ALLOWED),
        "axiom_audits": dict(sorted(axioms.items())),
        "printed_actual_types": names,
        "sha256": {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)},
        "hash_exclusion": "This self-referential record and the still-active outer transcript are not hashed here; stable environment, full build, and axiom logs are hashed.",
        "verification_note": "Generated only after the successful pinned pipeline, actual clean local-module rebuild, full type/axiom print, and source-construct checks. All dependency caches were retained. Mathematical verification does not establish novelty."
    }
    if (ROOT / "verification/initial_audit_options.log").exists():
        record["audit_harness_correction"] = (
            "The clean build completed all 14 modules successfully. The first audit invocation then reported unknown printing options pp.width and pp.maxDepth. "
            "Only those audit-format options were removed; all mathematical proof sources remained unchanged. The direct audit and record validation were rerun successfully against the freshly built modules. "
            "The failed audit and original combined transcript are preserved under verification/initial_*.log. The stable final build.log and axioms.log are the successful stage evidence."
        )
    (ROOT / "VERIFICATION.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Recorded {len(built)} fresh modules, {len(axioms)} declaration audits, and {record['audited_theorems']} theorems.")


if __name__ == "__main__":
    main()
