"""Check package integrity, import coverage, and final axiom reports."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import re
import tomllib

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative_name(name):
    path = PurePosixPath(name)
    require(bool(name) and not path.is_absolute() and path.as_posix() == name,
            "A package path is invalid.")
    require("\\" not in name and not any(part in {".", ".."} for part in path.parts),
            "A package path is invalid.")
    return name


def check(root=ROOT):
    root = Path(root)
    manifest = json.loads((root / "manifest.json").read_text())
    require(manifest["format_version"] == 1, "The package format is unsupported.")
    files = manifest["files"]
    require(isinstance(files, dict) and bool(files), "The file manifest is empty.")
    actual = set()
    require(not root.is_symlink(), "The package directory is a symbolic link.")
    for directory, names, filenames in os.walk(root):
        current = Path(directory)
        for name in names + filenames:
            require(not (current / name).is_symlink(), "A package path is a symbolic link.")
        if current == root:
            names[:] = [name for name in names if name not in {".lake", ".verification", "__pycache__"}]
        for name in filenames:
            actual.add((current / name).relative_to(root).as_posix())
    require(actual == set(files) | {"manifest.json"}, "The package file coverage differs.")
    for name, record in files.items():
        path = root / relative_name(name)
        require(path.stat().st_size == record["bytes"] and digest(path) == record["sha256"],
                f"File integrity failed: {name}")
    sources = json.loads((root / "sources.json").read_text())
    entries = sources["modules"]
    modules = {entry["module"]: entry for entry in entries}
    require(len(entries) == len(modules) == sources["source_count"] == 70,
            "The module coverage differs.")
    require(sum(entry["bytes"] for entry in entries) == sources["source_bytes"] == 232784,
            "The source byte count differs.")
    source_files = {name for name in files if name.startswith("src/")}
    require(source_files == {entry["path"] for entry in entries}, "The source file coverage differs.")
    for entry in entries:
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", entry["module"]),
                "A module name is invalid.")
        name = relative_name(entry["path"])
        require(name == "src/" + entry["module"].replace(".", "/") + ".lean",
                "A source path does not match its module.")
        path = root / name
        require(digest(path) == entry["sha256"] and path.stat().st_size == entry["bytes"],
                f"Source integrity failed: {name}")
        imports = re.findall(r"^(?:public )?import ([A-Za-z0-9_.]+)", path.read_text(), re.M)
        require(imports == entry["imports"], f"The imports differ: {name}")
        require(all(module in modules or module.startswith(("Mathlib.", "Lean.")) for module in imports),
                f"An import is missing: {name}")
    config = tomllib.loads((root / "lakefile.toml").read_text())
    require(config["name"] == "gyiresRankTwo", "The package name differs.")
    library = config["lean_lib"][0]
    require(library["srcDir"] == "src" and library["roots"] == ["RangeAudit"],
            "The library source root differs.")
    require(set(library["globs"]) == set(modules) and len(library["globs"]) == 70,
            "The configured module coverage differs.")
    revision = sources["mathlib_revision"]
    require(revision == "56a005855ea17e0b0958f73ec801ae140b0a1679", "The Mathlib revision differs.")
    require(config["require"][0]["rev"] == revision, "The configured Mathlib revision differs.")
    lock = json.loads((root / "lake-manifest.json").read_text())
    require(lock["name"] == config["name"], "The dependency package name differs.")
    packages = {package["name"]: package for package in lock["packages"]}
    require(len(packages) == len(lock["packages"]), "The dependency list has repeated names.")
    require(packages["mathlib"]["rev"] == revision, "The locked Mathlib revision differs.")
    require(all(re.fullmatch(r"[0-9a-f]{40}", package["rev"]) for package in packages.values()),
            "A dependency revision is not fixed.")
    require((root / "lean-toolchain").read_text().strip() == sources["lean_toolchain"]
            == "leanprover/lean4:v4.35.0", "The Lean version differs.")
    expected = json.loads((root / "expected-axioms.json").read_text())
    reports = re.findall(r"^#print axioms (\S+)$", (root / "src/RangeAudit.lean").read_text(), re.M)
    require(reports == expected["theorems"] and len(set(reports)) == 1,
            "The final theorem report coverage differs.")
    return modules, expected


def build_order(modules):
    result, active, complete = [], set(), set()
    def visit(module):
        if module in complete:
            return
        require(module not in active, "The project import graph has a cycle.")
        active.add(module)
        for imported in modules[module]["imports"]:
            if imported in modules:
                visit(imported)
        active.remove(module)
        complete.add(module)
        result.append(module)
    visit("RangeAudit")
    require(len(result) == len(modules) == 70, "The entry module does not use the exact source set.")
    return result


def check_axioms(path, expected):
    content = Path(path).read_text()
    require(not re.search(r"\b(error|warning)\s*:|sorryAx", content, re.I),
            "The axiom output contains an error, warning, or proof hole.")
    pattern = re.compile(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]")
    reports = pattern.findall(content)
    require([name for name, _ in reports] == expected["theorems"],
            "The axiom report coverage differs.")
    allowed = set(expected["permitted_axioms"])
    require(allowed == {"propext", "Classical.choice", "Quot.sound"},
            "The permitted axiom set differs.")
    for name, values in reports:
        axioms = {value.strip() for value in values.split(",") if value.strip()}
        require(axioms <= allowed, f"Unexpected axiom: {name}")
    require(not pattern.sub("", content).strip(), "The axiom output contains unrecognized text.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--axiom-log", type=Path)
    args = parser.parse_args()
    try:
        modules, expected = check()
        build_order(modules)
        if args.axiom_log:
            check_axioms(args.axiom_log, expected)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, str(error) + "\n")
    print("Package integrity and all 70 module imports passed.")
    if args.axiom_log:
        print("The final axiom report passed.")
