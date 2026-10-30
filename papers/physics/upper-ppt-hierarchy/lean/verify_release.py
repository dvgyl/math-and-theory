#!/usr/bin/env python3
"""Freeze and independently verify the all-depth upper-PPT noncollapse research release.

Project proof objects are always rebuilt in a fresh directory. Every compilation,
including the complete generated axiom audit, uses Lean --trust=0. Only the new
objects and pristine, commit-pinned dependency libraries enter LEAN_PATH.
"""
from __future__ import annotations

import argparse
import datetime as dt
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from threading import Condition

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MEMORY_BUDGET_GB = 6.0
TWO_COPY_CHECK_LIMIT = 2
LEAN_VERSION = "4.19.0"
LEAN_COMMIT = "6caaee842e94"
MATHLIB_COMMIT = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
CONFIG_FILES = ["verify_release.py", "modules.json", "lakefile.lean", "lake-manifest.json",
                "lean-toolchain", "REPRODUCE.txt"]
EXTERNAL_ROOTS = {"Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq",
                  "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli"}
CURRENT_MODULES = {'BellPositivity', 'BellTypes', 'MatrixReduction', 'FoldSystem', 'ChainGap', 'InverseSign', 'BellBridge', 'AllDepth', 'RationalLift', 'ParameterBounds', 'BellFoldSystem', 'ReverseOrbit', 'GenericHierarchy', 'SignConcentration', 'MatrixHierarchy', 'Certificate', 'ArbitraryHierarchy'}
NAME = r"[A-Za-z_][A-Za-z0-9_'.]*"
PROHIBITED = re.compile(
    r"\b(sorry|admit|axiom|axioms|constant|unsafe|native_decide|implemented_by|"
    r"opaque|run_tac|run_elab|elab|macro|initialize|builtin_initialize)\b")
AUDIT_RESULT = re.compile(
    r"'([^\n]+?)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)")


def utc() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def estimated_memory_gb(module: str) -> float:
    if module.startswith("TwoCopyCheck"):
        return 3.0
    if module.startswith(("HigherAxis", "HigherInteger", "HigherCheck")):
        return 3.0
    return 0.5


class CompilationBudget:
    """Conservative scheduling estimates, not an operating-system RSS cap."""

    def __init__(self) -> None:
        self.condition = Condition()
        self.used_gb = 0.0
        self.two_copy_checks = 0
        self.peak_gb = 0.0
        self.peak_two_copy_checks = 0

    @contextmanager
    def reserve(self, module: str):
        estimate = estimated_memory_gb(module)
        is_two_copy = module.startswith("TwoCopyCheck")
        with self.condition:
            self.condition.wait_for(lambda:
                self.used_gb + estimate <= MEMORY_BUDGET_GB and
                (not is_two_copy or self.two_copy_checks < TWO_COPY_CHECK_LIMIT))
            self.used_gb += estimate
            self.two_copy_checks += int(is_two_copy)
            self.peak_gb = max(self.peak_gb, self.used_gb)
            self.peak_two_copy_checks = max(self.peak_two_copy_checks, self.two_copy_checks)
        try:
            yield estimate
        finally:
            with self.condition:
                self.used_gb -= estimate
                self.two_copy_checks -= int(is_two_copy)
                self.condition.notify_all()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def command(argv: list[str], cwd: Path | None = None) -> str:
    return subprocess.check_output(argv, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def strip_comments_and_strings(source: str) -> str:
    """Preserve line boundaries while removing Lean's nested comments and strings."""
    result: list[str] = []
    index = depth = 0
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                depth += 1
                result.extend("  ")
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if source[index] == "\n" else " ")
                index += 1
        elif source.startswith("/-", index):
            depth = 1
            result.extend("  ")
            index += 2
        elif source.startswith("--", index):
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            result.extend(" " * (end - index))
            index = end
        elif source[index] == '"':
            result.append(" ")
            index += 1
            closed = False
            while index < len(source):
                char = source[index]
                if char == '"':
                    result.append(" ")
                    index += 1
                    closed = True
                    break
                if char == "\\":
                    result.extend("  ")
                    index += 2
                else:
                    result.append("\n" if char == "\n" else " ")
                    index += 1
            if not closed:
                raise RuntimeError("Unclosed Lean string")
        else:
            result.append(source[index])
            index += 1
    if depth:
        raise RuntimeError("Unclosed Lean block comment")
    return "".join(result)


def source_metadata(path: Path) -> tuple[list[str], list[str]]:
    code = strip_comments_and_strings(path.read_text())
    found = PROHIBITED.search(code)
    if found:
        raise RuntimeError(f"Prohibited Lean source token in {path.name}: {found.group()}")
    for line in code.splitlines():
        if re.search(r"\bset_option\b", line):
            if re.search(r"trust|check|debug|warningAsError\s+false|autoImplicit\s+true", line,
                         flags=re.IGNORECASE):
                raise RuntimeError(f"Trust/check option override in {path.name}: {line.strip()}")
        if re.match(r"\s*#(?:eval|reduce|check_failure|guard_msgs)\b", line):
            raise RuntimeError(f"Non-proof executable directive in {path.name}: {line.strip()}")
    imports: list[str] = []
    declarations: list[str] = []
    scopes: list[tuple[str, str | None]] = []
    declaration_re = re.compile(
        rf"^\s*(?:@\[[^]]*\]\s*)*(?P<mods>(?:(?:noncomputable|private|protected)\s+)*)"
        rf"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+(?P<name>{NAME})")
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            entries = stripped[7:].split()
            if not entries or any(re.fullmatch(NAME, name) is None for name in entries):
                raise RuntimeError(f"Unrecognized import in {path.name}: {stripped}")
            imports.extend(entries)
            continue
        match = re.match(rf"namespace\s+({NAME})\s*$", stripped)
        if match:
            scopes.append(("namespace", match.group(1)))
            continue
        match = re.match(rf"(?:noncomputable\s+)?section(?:\s+({NAME}))?\s*$", stripped)
        if match:
            scopes.append(("section", match.group(1)))
            continue
        match = re.match(rf"end(?:\s+({NAME}))?\s*$", stripped)
        if match:
            if not scopes:
                raise RuntimeError(f"Unmatched end in {path.name}: {stripped}")
            _, opened_name = scopes.pop()
            if match.group(1) and opened_name != match.group(1):
                raise RuntimeError(f"Scope-name mismatch in {path.name}: {stripped}")
            continue
        match = declaration_re.match(line)
        if match and "private" not in match.group("mods").split():
            name = match.group("name")
            if name.startswith("_root_."):
                name = name[7:]
            else:
                prefix = ".".join(scope_name for kind, scope_name in scopes
                                  if kind == "namespace" and scope_name)
                if prefix:
                    name = prefix + "." + name
            declarations.append(name)
    # A top-level noncomputable section may intentionally remain open to EOF.
    if any(kind == "namespace" for kind, _ in scopes):
        raise RuntimeError(f"Unclosed namespace in {path.name}")
    return imports, declarations


def project_plan(src: Path) -> tuple[list[str], list[str]]:
    settings = json.loads((src / "modules.json").read_text())
    modules = settings["modules"]
    if not modules or len(modules) != len(set(modules)):
        raise RuntimeError("Module manifest must contain distinct current project modules")
    if any(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) is None for name in modules):
        raise RuntimeError("Release module names must be simple flat identifiers")
    if set(modules) & (EXTERNAL_ROOTS | {"AxiomAudit"}):
        raise RuntimeError("Project module names may not shadow dependencies or the generated audit")
    main_module = settings.get("main_module", "AllDepth")
    if main_module not in modules:
        raise RuntimeError("The manifest main_module must be included in the release")
    if set(modules) != CURRENT_MODULES:
        raise RuntimeError("Only the reviewed all-depth upper-PPT modules belong in this release")
    dependencies: dict[str, set[str]] = {}
    declarations: list[str] = []
    for module in modules:
        imports, names = source_metadata(src / (module + ".lean"))
        dependencies[module] = set()
        for imported in imports:
            if imported in modules:
                dependencies[module].add(imported)
            elif imported.split(".", 1)[0] not in EXTERNAL_ROOTS:
                raise RuntimeError(f"Unlisted or historical project import in {module}: {imported}")
        declarations.extend(names)
    order: list[str] = []
    while len(order) < len(modules):
        ready = [name for name in modules if name not in order and dependencies[name] <= set(order)]
        if not ready:
            raise RuntimeError("Project import cycle")
        order.extend(ready)
    audit = settings.get("audit", {"mode": "all_public_declarations"})
    if audit.get("mode") != "all_public_declarations":
        raise RuntimeError("This release requires every public project declaration in the audit")
    declarations.extend(audit.get("extra_declarations", []))
    audit_names = list(dict.fromkeys(declarations))
    if not audit_names:
        raise RuntimeError("Empty axiom audit")
    if any(re.fullmatch(NAME, name) is None for name in audit_names):
        raise RuntimeError("Invalid audited declaration name")
    return order, audit_names


def audit_text(modules: list[str], names: list[str]) -> str:
    lines = ["-- Generated from modules.json by verify_release.py --freeze."]
    lines.extend("import " + module for module in modules)
    lines.append("")
    lines.extend("#print axioms " + name for name in names)
    return "\n".join(lines) + "\n"


def freeze(src: Path, force: bool) -> None:
    target = src / "release-freeze.json"
    if target.exists() and not force:
        raise RuntimeError("A freeze already exists; review changes before explicitly using --force")
    modules, names = project_plan(src)
    (src / "AxiomAudit.lean").write_text(audit_text(modules, names))
    files = CONFIG_FILES + [module + ".lean" for module in modules] + ["AxiomAudit.lean"]
    frozen = {"schema_version": 1, "frozen_utc": utc(), "modules": modules,
              "audit_declarations": names, "audit_count": len(names),
              "files_sha256": {name: sha(src / name) for name in files}}
    write_json(target, frozen)
    print(f"FROZEN: {len(modules)} project modules, {len(names)} audited declarations.")
    print("This freezes sources; it does not constitute a successful verification.")


def parse_axiom_audit(log_text: str, expected_names: list[str]) -> dict[str, list[str]]:
    rows = AUDIT_RESULT.findall(log_text)
    observed: dict[str, list[str]] = {}
    for name, raw_axioms in rows:
        if name in observed:
            raise RuntimeError("Duplicate audit output for " + name)
        axioms = {entry.strip() for entry in raw_axioms.split(",") if entry.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unapproved axiom dependencies of {name}: {sorted(axioms)}")
        observed[name] = sorted(axioms)
    if set(observed) != set(expected_names) or len(rows) != len(expected_names):
        missing = sorted(set(expected_names) - set(observed))
        unexpected = sorted(set(observed) - set(expected_names))
        raise RuntimeError(f"Incomplete axiom audit: got {len(rows)}, expected {len(expected_names)}; "
                           f"missing={missing}; unexpected={unexpected}")
    return observed


def verify(args: argparse.Namespace, src: Path) -> None:
    out = args.out.resolve()
    if out.exists() and (not out.is_dir() or any(out.iterdir())):
        raise RuntimeError("Verification output must be a new or empty directory")
    out.mkdir(parents=True, exist_ok=True)
    receipt_path = out / "receipt.json"
    receipt: dict = {"status": "VALIDATING", "started_utc": utc(), "modules": []}
    write_json(receipt_path, receipt)
    try:
        frozen_config = json.loads((src / "release-freeze.json").read_text())
        modules, audit_names = project_plan(src)
        if modules != frozen_config["modules"] or audit_names != frozen_config["audit_declarations"]:
            raise RuntimeError("Source/module/audit plan differs from the reviewed source freeze")
        if len(audit_names) != frozen_config["audit_count"]:
            raise RuntimeError("Frozen audit count mismatch")
        if (src / "AxiomAudit.lean").read_text() != audit_text(modules, audit_names):
            raise RuntimeError("AxiomAudit.lean differs from the complete generated audit")
        for name, expected in frozen_config["files_sha256"].items():
            if sha(src / name) != expected:
                raise RuntimeError("Frozen source/configuration hash mismatch: " + name)
        manifest = json.loads((src / "lake-manifest.json").read_text())
        mathlib = args.mathlib.resolve()
        packages_dir = (args.packages_dir.resolve() if args.packages_dir else mathlib / ".lake/packages")
        pins: dict = {}
        libraries: list[Path] = []
        for package in manifest["packages"]:
            if package["type"] != "git" or re.fullmatch(r"[0-9a-f]{40}", package["rev"]) is None:
                raise RuntimeError("Every dependency must be pinned to a full git commit")
            directory = mathlib if package["name"] == "mathlib" else packages_dir / package["name"]
            actual = command(["git", "-C", str(directory), "rev-parse", "HEAD"])
            if actual != package["rev"]:
                raise RuntimeError(f"Dependency revision mismatch for {package['name']}: {actual}")
            dirty = command(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=all"])
            if dirty:
                raise RuntimeError(f"Dependency checkout is not pristine: {package['name']}\n{dirty}")
            if package["name"] == "mathlib" and actual != MATHLIB_COMMIT:
                raise RuntimeError("Unexpected mathlib commit")
            library = directory / ".lake/build/lib/lean"
            if package["name"] == "mathlib" and not library.is_dir():
                raise RuntimeError("Dependency object library missing: " + str(library))
            # Build-only dependencies such as Cli may have no Lean object cache.
            # Any genuinely imported missing module will fail in Lean itself.
            if library.is_dir():
                libraries.append(library)
            pins[package["name"]] = {"revision": actual, "url": package["url"], "directory": str(directory),
                                    "object_library": str(library) if library.is_dir() else None}
        if "mathlib" not in pins:
            raise RuntimeError("Missing pinned mathlib dependency")
        # Project names must resolve only to freshly built current-release objects.
        for library in libraries:
            for module in modules + ["AxiomAudit"]:
                for suffix in (".olean", ".ilean"):
                    if (library / (module + suffix)).exists():
                        raise RuntimeError("Dependency library shadows current project module: " +
                                           str(library / (module + suffix)))
        dist = args.lean_home.resolve()
        lean = dist / "bin/lean"
        for module in modules + ["AxiomAudit"]:
            for suffix in (".olean", ".ilean"):
                path = dist / "lib/lean" / (module + suffix)
                if path.exists():
                    raise RuntimeError("Lean system library shadows current project module: " + str(path))
        version = command([str(lean), "--version"])
        if f"version {LEAN_VERSION}" not in version or LEAN_COMMIT not in version:
            raise RuntimeError("Unexpected Lean release: " + version)
        if (src / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.19.0":
            raise RuntimeError("Unexpected lean-toolchain")
        frozen = out / "sources"
        objects = out / "objects"
        logs = out / "logs"
        for directory in (frozen, objects, logs):
            directory.mkdir()
        for name in frozen_config["files_sha256"]:
            shutil.copy2(src / name, frozen / name)
        shutil.copy2(src / "release-freeze.json", frozen / "release-freeze.json")
        env = {key: value for key, value in os.environ.items() if not key.startswith("LEAN_")}
        env["LEAN_PATH"] = os.pathsep.join(map(str, [objects] + libraries))
        env["LEAN_SYSROOT"] = str(dist)
        receipt.update({"status": "RUNNING", "lean_version": version,
                        "lean_binary_sha256": sha(lean), "pinned_dependencies": pins,
                        "freeze_sha256": sha(src / "release-freeze.json"),
                        "frozen_files_sha256": frozen_config["files_sha256"],
                        "lean_path": env["LEAN_PATH"], "lean_sysroot": str(dist),
                        "allowed_axioms": sorted(ALLOWED_AXIOMS),
                        "expected_audit_count": len(audit_names),
                        "verification_policy": "Every module and full audit use --trust=0; fresh project objects only"})
        write_json(receipt_path, receipt)
        dependencies = {
            module: set(source_metadata(frozen / (module + ".lean"))[0]) & set(modules)
            for module in modules
        }
        receipt["parallel_jobs"] = args.jobs
        receipt["scheduler"] = {
            "estimated_memory_budget_gb": MEMORY_BUDGET_GB,
            "max_simultaneous_two_copy_checks": TWO_COPY_CHECK_LIMIT,
            "two_copy_check_estimate_gb": 3.0,
            "higher_finite_check_estimate_gb": 3.0,
            "other_module_estimate_gb": 0.5,
            "note": "Conservative scheduling estimates; not an operating-system RSS guarantee",
        }
        write_json(receipt_path, receipt)
        budget = CompilationBudget()

        def compile_one(module: str) -> dict:
            with budget.reserve(module) as estimate:
                argv = [str(lean), "--trust=0", "-j1", "-DwarningAsError=true", "-DautoImplicit=false",
                        "-o", str(objects / (module + ".olean")), module + ".lean"]
                print(f"Checking {module} (trust=0)", flush=True)
                started = time.monotonic()
                log = logs / (module + ".log")
                with log.open("w") as stream:
                    result = subprocess.run(argv, cwd=frozen, env=env, stdout=stream,
                                            stderr=subprocess.STDOUT)
                record = {"module": module, "trust": 0, "returncode": result.returncode,
                          "command": argv, "cwd": str(frozen), "log_sha256": sha(log),
                          "estimated_memory_gb": estimate,
                          "elapsed_seconds": round(time.monotonic() - started, 3)}
                object_path = objects / (module + ".olean")
                if result.returncode == 0:
                    if not object_path.is_file():
                        raise RuntimeError("Compiler produced no object for " + module)
                    record["object_sha256"] = sha(object_path)
                return record

        completed: set[str] = set()
        while len(completed) < len(modules):
            ready = [module for module in modules
                     if module not in completed and dependencies[module] <= completed]
            if not ready:
                raise RuntimeError("No ready module in verified import graph")
            failures: list[dict] = []
            # Every job in this wave depends only on completed prior waves.
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                futures = {pool.submit(compile_one, module): module for module in ready}
                for future in as_completed(futures):
                    record = future.result()
                    receipt["modules"].append(record)
                    write_json(receipt_path, receipt)
                    if record["returncode"]:
                        failures.append(record)
                    else:
                        completed.add(record["module"])
            if failures:
                for record in failures:
                    print((logs / (record["module"] + ".log")).read_text(), flush=True)
                raise RuntimeError("Lean compilation failed: " +
                                   ", ".join(record["module"] for record in failures))
        record = compile_one("AxiomAudit")
        receipt["modules"].append(record)
        receipt["modules"].sort(key=lambda row: (modules + ["AxiomAudit"]).index(row["module"]))
        write_json(receipt_path, receipt)
        if record["returncode"]:
            print((logs / "AxiomAudit.log").read_text(), flush=True)
            raise RuntimeError("Complete axiom audit compilation failed")
        receipt["audited_axioms"] = parse_axiom_audit(
            (logs / "AxiomAudit.log").read_text(), audit_names)
        receipt["observed_audit_count"] = len(receipt["audited_axioms"])
        receipt["scheduler"]["observed_peak_estimate_gb"] = budget.peak_gb
        receipt["scheduler"]["observed_peak_simultaneous_two_copy_checks"] = budget.peak_two_copy_checks
        for name, expected in frozen_config["files_sha256"].items():
            if sha(src / name) != expected or sha(frozen / name) != expected:
                raise RuntimeError("Source/configuration changed during verification: " + name)
        if sha(src / "release-freeze.json") != receipt["freeze_sha256"]:
            raise RuntimeError("Source freeze changed during verification")
        # Recheck dependency source pins/cleanliness after the complete proof replay.
        for name, pin in pins.items():
            directory = pin["directory"]
            if command(["git", "-C", directory, "rev-parse", "HEAD"]) != pin["revision"]:
                raise RuntimeError("Dependency changed during verification: " + name)
            if command(["git", "-C", directory, "status", "--porcelain", "--untracked-files=all"]):
                raise RuntimeError("Dependency source modified during verification: " + name)
        receipt.update({"status": "PASS", "finished_utc": utc(), "all_audited_axioms_standard": True})
        write_json(receipt_path, receipt)
        print(f"PASS: {len(modules)} fresh project modules; {len(audit_names)} declarations audited; all trust=0.",
              flush=True)
    except BaseException as error:
        receipt.update({"status": "FAILED", "finished_utc": utc(),
                        "failure": type(error).__name__ + ": " + str(error)})
        write_json(receipt_path, receipt)
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--freeze", action="store_true", help="Generate full audit and freeze reviewed release sources")
    parser.add_argument("--force", action="store_true", help="Explicitly replace an existing reviewed source freeze")
    parser.add_argument("--lean-home", type=Path, help="Lean 4.19.0 distribution directory")
    parser.add_argument("--mathlib", type=Path, help="Pristine pinned mathlib checkout with its object cache")
    parser.add_argument("--packages-dir", type=Path, help="Dependency package directory; default: MATHLIB/.lake/packages")
    parser.add_argument("--out", type=Path, help="New or empty isolated verification directory")
    parser.add_argument("--jobs", type=int, default=1,
                        help="Independent compiler jobs per dependency wave (1 to 4; default 1)")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        parser.error("--jobs must be between 1 and 4")
    src = args.source_dir.resolve()
    if sha(Path(__file__).resolve()) != sha(src / "verify_release.py"):
        raise RuntimeError("Running verifier differs from the release's reviewed verifier")
    if args.freeze:
        freeze(src, args.force)
    else:
        if args.force:
            parser.error("--force is only valid with --freeze")
        if args.lean_home is None or args.mathlib is None or args.out is None:
            parser.error("Verification requires --lean-home, --mathlib, and --out")
        verify(args, src)


if __name__ == "__main__":
    main()
