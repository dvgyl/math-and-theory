#!/usr/bin/env python3
"""Rebuild every E3 project module in a fresh directory and audit endpoint axioms.

The optional --reuse-packages uses existing pinned dependencies, never project
oleans. Without it Lake fetches the manifest's dependencies as usual. The script
does not install Lean or silently change any dependency revision.
"""

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from E3_audit_support import audit_endpoints, ALLOWED_AXIOMS


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--reuse-packages", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    source = root / "e3_lean"
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    out = (args.output or root / "e3_verification" / stamp).resolve()
    out.mkdir(parents=True, exist_ok=False)
    fresh = out / "fresh"
    fresh.mkdir()
    record = {"started_utc": utc(), "source_root": str(root),
              "fresh_project": str(fresh), "commands": [], "sources": {},
              "dependency_mode": "reused pinned dependency build cache" if args.reuse_packages
              else "Lake-managed manifest dependencies", "success": False}
    record_path = out / "verification.json"

    def save():
        record_path.write_text(json.dumps(record, indent=2) + "\n")

    def run(argv, logname):
        item = {"argv": list(map(str, argv)), "started_utc": utc(), "log": logname}
        record["commands"].append(item)
        save()
        print("RUN", " ".join(item["argv"]), flush=True)
        with (out / logname).open("w") as log:
            proc = subprocess.run(argv, cwd=fresh, env=env,
                                  stdout=log, stderr=subprocess.STDOUT)
        item.update(exit_code=proc.returncode, finished_utc=utc(),
                    log_sha256=digest(out / logname))
        save()
        if proc.returncode:
            print((out / logname).read_text()[-18000:], flush=True)
            raise RuntimeError(f"Command failed ({proc.returncode}); see {out / logname}")
        return (out / logname).read_text()

    try:
        selected = [source / p for p in
                    ("lean-toolchain", "lakefile.toml", "lake-manifest.json",
                     "InfoE3.lean", "AxiomAudit.lean", "IndependentScopeAudit.lean")]
        selected += sorted((source / "InfoE3").rglob("*.lean"))
        forbidden = re.compile(r"^\s*(?:axiom|constant|opaque\s+\w+\s*:\s*Prop\s*$)|\b(?:sorry|admit|native_decide|sorryAx)\b", re.M)
        for src in selected:
            rel = src.relative_to(source)
            if src.suffix == ".lean" and forbidden.search(src.read_text()):
                raise RuntimeError(f"Forbidden declaration/admission requires inspection: {rel}")
            dest = fresh / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dest)
            record["sources"][str(rel)] = digest(src)
        record["initial_project_oleans"] = list(map(str, fresh.rglob("*.olean")))
        if record["initial_project_oleans"]:
            raise RuntimeError("Fresh directory unexpectedly contains project oleans")
        if args.reuse_packages:
            packages = args.reuse_packages.resolve(strict=True)
            (fresh / ".lake").mkdir()
            (fresh / ".lake" / "packages").symlink_to(packages, target_is_directory=True)
            record["dependency_cache"] = str(packages)
        env = os.environ.copy()
        env["LEAN_NUM_THREADS"] = "1"
        record["lean_num_threads"] = 1
        save()
        if not args.reuse_packages:
            run([args.lake, "exe", "cache", "get"], "dependency_cache.log")
        version = run([args.lake, "env", "lean", "--version"], "lean_version.log")
        record["lean_version"] = version.strip()
        # Compile in dependency order, one process and one Lean thread at a time.
        # No project build product is reused. This avoids an unbounded parallel
        # collection of exact finite certificate checks on high-core hosts.
        modules = {}
        for src in selected:
            if src.suffix == ".lean" and src.name != "AxiomAudit.lean":
                rel = src.relative_to(source)
                modules[".".join(rel.with_suffix("").parts)] = rel
        compiled = set()
        pending = set()
        order = []
        def visit(name):
            if name in compiled:
                return
            if name in pending:
                raise RuntimeError("Cyclic project imports: " + name)
            pending.add(name)
            rel = modules[name]
            imports = re.findall(r"^import\s+(\S+)", (fresh / rel).read_text(), re.M)
            for dep in imports:
                if dep in modules:
                    visit(dep)
            target = fresh / ".lake" / "build" / "lib" / "lean" / rel.with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            run([args.lake, "env", "lean", "-j1", "-o", str(target), str(rel)],
                "build_" + name.replace(".", "_") + ".log")
            pending.remove(name)
            compiled.add(name)
            order.append(name)
        for name in sorted(modules):
            visit(name)
        record["fresh_module_order"] = order
        record["fresh_modules_compiled"] = len(order)
        audit = run([args.lake, "env", "lean", "-j1", "AxiomAudit.lean"], "axiom_audit.log")
        reports = audit_endpoints((fresh / "AxiomAudit.lean").read_text(), audit)
        manifest = json.loads((fresh / "lake-manifest.json").read_text())
        dependency_checks = []
        for pkg in manifest["packages"]:
            folder = fresh / ".lake" / "packages" / pkg["name"]
            head = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
            dirty = subprocess.check_output(["git", "-C", str(folder), "status", "--porcelain", "--untracked-files=no"], text=True).splitlines()
            entry = {"name": pkg["name"], "pinned": pkg["rev"], "actual": head,
                     "matches": head == pkg["rev"], "tracked_changes": dirty}
            dependency_checks.append(entry)
            if not entry["matches"] or dirty:
                raise RuntimeError(f"Dependency pin/worktree mismatch: {pkg['name']}")
        record["dependency_checks"] = dependency_checks
        record["axiom_reports"] = len(reports)
        record["axiom_endpoint_reports"] = reports
        record["allowed_axioms"] = sorted(ALLOWED_AXIOMS)
        record["success"] = True
    except Exception as exc:
        record["failure"] = str(exc)
        print(str(exc), file=sys.stderr, flush=True)
    finally:
        record["finished_utc"] = utc()
        save()
        print(str(record_path), flush=True)
    return 0 if record["success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
