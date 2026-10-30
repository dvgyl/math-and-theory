#!/usr/bin/env python3
"""Recompile every project proof in a fresh directory and audit its axioms.

Prepare dependencies first with `lake exe cache get`. This verifier reuses
only dependencies at the exact Git commits in lake-manifest.json. It copies
no project .olean files into the fresh directory. All twenty-two proof modules are
checked with Lean's kernel trust level 0 and warnings treated as errors.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

MODULES = ["CoreDefs", "CESTensor", "TilesBase", "TilesTensor", "ConeExclusion", "Main",
           "GeneralDefs", "CESTensorGeneral", "TensorProjection", "GenericCone", "Hierarchy", "AllK",
           "RankBridge", "BlockRank", "UPBRank", "TensorProductProjection", "TilesUPB",
           "SchmidtUpper", "StrongTensor", "PowerFamily", "Normalization", "NormalizedPower"]
CENTRAL_THEOREMS = {
    "Main": ["explicit_ppt_counterexample", "ppt_not_subset_dsp2"],
    "AllK": ["all_levels_explicit_counterexamples", "no_uniform_finite_cutoff"],
    "StrongTensor": ["upb_strong_minimum_rank", "tiles_strong_minimum_rank"],
    "PowerFamily": ["upb_tensor_no_sr", "tilesPower_schmidtNumber_exact",
                    "tilesPower_support_minimum", "sharp_tiles_power_family"],
    "NormalizedPower": ["tilesDensity_schmidtNumber_exact", "tilesDensity_succ",
                        "normalized_sharp_tiles_power_family"],
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def strip_comments(text):
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    result.append("\n")
                i += 1
        elif string:
            result.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                result.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    string = False
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.append(" ")
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            if text[i] == '"':
                string = True
            result.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unclosed comment/string in Lean source")
    return "".join(result)


def run(args, cwd, env):
    p = subprocess.run(args, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return p.returncode, p.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path,
                        help="Optional directory containing pinned lean and lake binaries")
    parser.add_argument("--keep-workdir", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    out = root / "verification"
    out.mkdir(exist_ok=True)
    env = os.environ.copy()
    if args.lean_bin:
        env["PATH"] = str(args.lean_bin.resolve()) + os.pathsep + env.get("PATH", "")
    # A caller's Lean search path must not import stale project objects.
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    report = {"status": "running", "modules": [], "dependencies": [],
              "allowed_axioms": sorted(ALLOWED_AXIOMS),
              "kernel_trust_level": 0, "warnings_as_errors": True,
              "project_objects_reused": False, "dependency_objects_reused": True}
    logs = []
    files = [f"{m}.lean" for m in MODULES] + ["lakefile.lean", "lean-toolchain", "lake-manifest.json"]
    report["source_sha256"] = {}
    forbidden = r"\b(?:sorry|admit|axiom|sorryAx|native_decide|unsafe|implemented_by|extern|skipKernelTC)\b"
    for name in files:
        path = root / name
        report["source_sha256"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
        if name.endswith(".lean") and re.search(forbidden, strip_comments(path.read_text())):
            raise RuntimeError(f"Forbidden proof escape or axiom declaration in {name}")
    temp = Path(tempfile.mkdtemp(prefix="ppt-cone-clean-"))
    report["fresh_workdir"] = str(temp)
    try:
        for name in files:
            shutil.copy2(root / name, temp / name)
        packages = temp / ".lake" / "packages"
        packages.mkdir(parents=True)
        for item in manifest["packages"]:
            source = (root / ".lake" / "packages" / item["name"]).resolve()
            if not source.is_dir():
                raise RuntimeError("Missing dependencies; run lake exe cache get first")
            code, rev = run(["git", "rev-parse", "HEAD"], source, env)
            if code or rev.strip() != item["rev"]:
                raise RuntimeError(f"Dependency pin mismatch: {item['name']}: {rev}")
            code, changes = run(["git", "diff", "--name-only", "HEAD"], source, env)
            if code or changes.strip():
                raise RuntimeError(f"Tracked dependency files modified: {item['name']}: {changes}")
            (packages / item["name"]).symlink_to(source, target_is_directory=True)
            report["dependencies"].append({"name": item["name"], "revision": rev.strip()})
        build = temp / ".lake" / "build" / "lib" / "lean"
        build.mkdir(parents=True)
        code, version = run(["lake", "env", "lean", "--version"], temp, env)
        logs.append(version)
        if code or "version 4.19.0" not in version or "6caaee842e94" not in version:
            raise RuntimeError(f"Unexpected Lean compiler: {version}")
        report["lean_version"] = version.strip()
        for module in MODULES:
            print(f"Checking {module}.lean with a fresh project object ...", flush=True)
            command = ["lake", "env", "lean", "--trust=0", "-j1",
                       "-DwarningAsError=true", "-DautoImplicit=false",
                       "-o", str(build / f"{module}.olean"), f"{module}.lean"]
            start = time.monotonic()
            code, text = run(command, temp, env)
            elapsed = time.monotonic() - start
            logs.extend(["COMMAND: " + " ".join(command) + "\n", text,
                         f"EXIT: {code}; SECONDS: {elapsed:.3f}\n"])
            report["modules"].append({"name": module, "exit_code": code,
                                      "seconds": round(elapsed, 3)})
            (out / "clean_build.log").write_text("".join(logs))
            if code:
                raise RuntimeError(f"Lean verification failed for {module}:\n{text}")
            if module in CENTRAL_THEOREMS:
                axioms = {}
                for theorem in CENTRAL_THEOREMS[module]:
                    pattern = re.escape("PPTCone." + theorem) + r".*?depends on axioms:\s*\[(.*?)\]"
                    match = re.search(pattern, text, flags=re.S)
                    if not match:
                        raise RuntimeError(f"Missing axiom audit for {theorem}: {text}")
                    found = {x.strip() for x in match.group(1).split(",") if x.strip()}
                    if not found <= ALLOWED_AXIOMS:
                        raise RuntimeError(f"Unexpected axiom for {theorem}: {found}")
                    axioms[theorem] = sorted(found)
                report.setdefault("central_theorem_axioms", {}).update(axioms)
        report["status"] = "passed"
        print(f"All {len(MODULES)} modules passed; central axioms are standard Lean foundations.", flush=True)
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        (out / "clean_build.log").write_text("".join(logs))
        (out / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
        if not args.keep_workdir:
            shutil.rmtree(temp)


if __name__ == "__main__":
    main()
