#!/usr/bin/env python3
"""Check the two unchanged Lean 4.19 release packages and their evidence."""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tomllib

from catalogue_paths import load_families


EXPECTED_MANIFESTS = {
    "readk-covariance": "2246d348b1569297c193dccb9fa79e0cc40d0265f528407c1b1b21c23c4d1be5",
    "thermal-kurtosis-counterexample": "b316ad24a8acc6a8936d17590634104e2d6b40fb8bd2051d78675cc8ed77f53c",
}
MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEX = re.compile(r"[0-9a-f]{64}\Z")
REPORT = re.compile(r"^'([^'\n]+)' (?:depends on axioms: \[([^\]\n]*)\]|does not depend on any axioms)$", re.M)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def valid_member(name):
    if not isinstance(name, str) or not name or "\\" in name:
        return False
    path = PurePosixPath(name)
    return not path.is_absolute() and path.as_posix() == name and all(
        part not in {"", ".", "..", ".git", ".lake", "__pycache__"} for part in path.parts
    )


def check_manifest(package, expected_digest):
    """Require exact release-file coverage and byte identity."""
    package = Path(package)
    require(package.is_dir() and not package.is_symlink(), f"Invalid package root: {package.name}")
    raw = (package / "manifest.json").read_bytes()
    require(digest(raw) == expected_digest, f"Changed package manifest: {package.name}")
    record = json.loads(raw)
    files = record.get("files")
    require(record.get("format_version") == 1 and isinstance(files, dict) and files,
            f"Invalid package manifest: {package.name}")
    require(all(valid_member(name) for name in files), f"Invalid package member: {package.name}")
    actual = set()
    for path in package.rglob("*"):
        rel = path.relative_to(package).as_posix()
        require(not path.is_symlink(), f"Symbolic link in package: {package.name}/{rel}")
        if path.is_file():
            actual.add(rel)
    require(actual == set(files) | {"manifest.json"},
            f"Package release-file coverage differs: {package.name}")
    for name, entry in files.items():
        require(isinstance(entry, dict) and set(entry) == {"bytes", "sha256"},
                f"Invalid package file record: {package.name}/{name}")
        require(isinstance(entry["bytes"], int) and entry["bytes"] >= 0
                and isinstance(entry["sha256"], str) and HEX.fullmatch(entry["sha256"]),
                f"Invalid package size or hash: {package.name}/{name}")
        data = (package / name).read_bytes()
        require(len(data) == entry["bytes"] and digest(data) == entry["sha256"],
                f"Changed package file: {package.name}/{name}")
    require(record.get("lean_version") == "4.19.0" and record.get("mathlib_revision") == MATHLIB,
            f"Wrong package toolchain: {package.name}")
    require(isinstance(record.get("formal_scope"), str) and record["formal_scope"].strip(),
            f"Missing package formal scope: {package.name}")
    return record


def check_readk(package, manifest):
    """Check read-k source coverage, lockfile, and stored axiom evidence."""
    files = manifest["files"]
    require((package / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0",
            "Wrong read-k Lean toolchain")
    lakefile = tomllib.loads((package / "lakefile.toml").read_text())
    mathlib = [item for item in lakefile.get("require", []) if item.get("name") == "mathlib"]
    require(len(mathlib) == 1 and mathlib[0].get("rev") == MATHLIB,
            "Wrong read-k Mathlib requirement")
    lock = json.loads((package / "lake-manifest.json").read_text())
    entries = lock.get("packages")
    require(isinstance(entries, list) and len(entries) == 9, "Wrong read-k dependency count")
    require(len({entry.get("name") for entry in entries}) == len(entries)
            and all(entry.get("type") == "git" and re.fullmatch(r"[0-9a-f]{40}", entry.get("rev", ""))
                    for entry in entries), "Invalid read-k dependency revision")
    locked_mathlib = [entry for entry in entries if entry["name"] == "mathlib"]
    require(len(locked_mathlib) == 1 and locked_mathlib[0]["rev"] == MATHLIB,
            "Wrong read-k Mathlib lock")
    source = json.loads((package / "verification/source-checks.json").read_text())
    lean_names = {name for name in files if name.endswith(".lean")}
    checked = source.get("sources")
    require(isinstance(checked, list) and len(checked) == 10 and len(lean_names) == 10,
            "Wrong read-k source count")
    require({entry.get("source") for entry in checked} == lean_names,
            "Incomplete read-k source evidence")
    for entry in checked:
        require(entry.get("source_sha256") == files[entry["source"]]["sha256"]
                and entry.get("compiler_exit_code") == 0,
                f"Invalid read-k compiler evidence: {entry['source']}")
    require(source.get("lean") == "4.19.0" and source.get("mathlib_commit") == MATHLIB,
            "Wrong read-k recorded toolchain")
    require(source.get("selected_axiom_reports") == 29
            and set(source.get("permitted_axioms", [])) == ALLOWED,
            "Wrong read-k axiom evidence")
    wrapper = source.get("wrapper", {})
    require(wrapper.get("script") == "verify.sh" and wrapper.get("exit_code") == 0
            and wrapper.get("script_sha256") == files["verify.sh"]["sha256"],
            "Wrong read-k wrapper evidence")
    checksums = {}
    for line in (package / "SOURCE_SHA256SUMS").read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        require(match is not None and match.group(2) not in checksums,
                "Invalid read-k source checksum list")
        checksums[match.group(2)] = match.group(1)
    required = lean_names | {"lakefile.toml", "lake-manifest.json", "lean-toolchain", "verify.sh",
                             "verification/theorem-list.txt", "scripts/check_audit.py",
                             "scripts/finite_checks.py", "scripts/test_verifiers.py"}
    require(set(checksums) == required and all(checksums[name] == files[name]["sha256"] for name in required),
            "Incomplete read-k source checksum list")
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("readk_check_audit", package / "scripts/check_audit.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    count = module.check((package / "verification/axioms.txt").read_text())
    require(count == 29, "Wrong read-k axiom report count")


def thermal_axioms(source_text, output):
    """Require every requested thermal axiom report exactly once."""
    requested = re.findall(r"^#print axioms (\S+)\s*$", source_text, re.M)
    require(len(requested) == 2 and len(set(requested)) == 2,
            "Wrong thermal axiom requests")
    reports = list(REPORT.finditer(output))
    names = [match.group(1) for match in reports]
    require(len(reports) == 2 and set(names) == set(requested) and len(set(names)) == 2,
            "Missing, repeated, or unexpected thermal axiom reports")
    remainder = REPORT.sub("", output)
    require(not re.search(r"depends on axioms|does not depend on any axioms|(^|: )error:", remainder, re.M),
            "Malformed thermal axiom report or compiler error")
    for match in reports:
        raw = match.group(2)
        axioms = [] if raw is None or not raw.strip() else [item.strip() for item in raw.split(",")]
        require(all(axioms) and len(axioms) == len(set(axioms)) and set(axioms) <= ALLOWED,
                f"Forbidden thermal axiom: {match.group(1)}")
    return len(reports)


def check_thermal(package, manifest):
    """Check thermal source, wrapper, and recorded compiler output."""
    files = manifest["files"]
    source = json.loads((package / "source-checks.json").read_text())
    lean_names = {name for name in files if name.endswith(".lean")}
    require(lean_names == {"ThermalKurtosis.lean"} and source.get("source") in lean_names,
            "Wrong thermal source coverage")
    require(source.get("source_sha256") == files["ThermalKurtosis.lean"]["sha256"]
            and source.get("compiler_exit_code") == 0,
            "Wrong thermal compiler evidence")
    require(source.get("lean") == "4.19.0" and source.get("mathlib_commit") == MATHLIB,
            "Wrong thermal recorded toolchain")
    require(source.get("axiom_reports_in_source") == 2
            and set(source.get("permitted_axioms", [])) == ALLOWED,
            "Wrong thermal axiom evidence")
    wrapper = source.get("wrapper", {})
    require(wrapper.get("script") == "verify.sh" and wrapper.get("exit_code") == 0
            and wrapper.get("script_sha256") == files["verify.sh"]["sha256"],
            "Wrong thermal wrapper evidence")
    script = (package / "verify.sh").read_text()
    require(re.search(r"^expected_revision=" + MATHLIB + r"$", script, re.M) is not None
            and "Lean (version 4.19.0," in script,
            "Wrong thermal wrapper pins")
    thermal_axioms((package / "ThermalKurtosis.lean").read_text(),
                   (package / "verification.log").read_text())


def check_packages(root, families):
    """Check both standalone packages and return their release manifests."""
    standalone = {family["id"]: family for family in families
                  if family["formalization"]["kind"] == "standalone"}
    require(set(standalone) == set(EXPECTED_MANIFESTS), "Standalone family set differs")
    manifests = {}
    for name, family in standalone.items():
        package = Path(root) / family["formalization"]["root"]
        manifest = check_manifest(package, EXPECTED_MANIFESTS[name])
        paper = Path(family["paper"]).relative_to(family["formalization"]["root"]).as_posix()
        require(paper in manifest["files"] and paper[:-4] + ".tex" in manifest["files"],
                f"Missing package manuscript: {name}")
        if name == "readk-covariance":
            check_readk(package, manifest)
        else:
            check_thermal(package, manifest)
        manifests[name] = manifest
    return manifests


def check_arithmetic(root, families):
    """Compare fresh exact arithmetic with the two stored JSON records."""
    for family in families:
        name = family["id"]
        if name not in EXPECTED_MANIFESTS:
            continue
        package = Path(root) / family["formalization"]["root"]
        script, record = ({
            "readk-covariance": ("scripts/finite_checks.py", "verification/finite-checks.json"),
            "thermal-kurtosis-counterexample": ("model_check.py", "model_check_output.json"),
        })[name]
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        result = subprocess.run([sys.executable, str(package / script)], cwd=package, env=env,
                                capture_output=True, text=True, check=True)
        require(json.loads(result.stdout) == json.loads((package / record).read_text()),
                f"Fresh arithmetic differs: {name}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arithmetic", action="store_true")
    parser.add_argument("--thermal-log", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    families = load_families(root)
    manifests = check_packages(root, families)
    if args.arithmetic:
        check_arithmetic(root, families)
    if args.thermal_log:
        package = root / "verification/additional-proofs/thermal-kurtosis-counterexample"
        thermal_axioms((package / "ThermalKurtosis.lean").read_text(), args.thermal_log.read_text())
    print(json.dumps({"status": "PASS", "standalone_packages": len(manifests),
                      "fresh_arithmetic": args.arithmetic, "fresh_thermal_axioms": bool(args.thermal_log)}))
