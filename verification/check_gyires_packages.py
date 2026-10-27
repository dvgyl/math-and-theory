"""Check the source coverage of the separate Gyires proof packages."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_six(root):
    root = Path(root)
    source = root / "sources"
    manifest_path = root / "source-manifest.json"
    raw = manifest_path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == (root / "source-manifest.sha256").read_text().split()[0],
            "The order-six manifest hash differs.")
    manifest = json.loads(raw)
    require(manifest.get("root_module") == "SixTheoremChecks"
            and manifest.get("source_count") == 3091 and manifest.get("source_bytes") == 399233748,
            "The order-six source coverage differs.")
    entries = manifest["sources"]
    modules = {entry["module"]: entry for entry in entries}
    require(len(modules) == len(entries) == 3091, "The order-six module list differs.")
    seen = set()
    total = 0
    for name, entry in modules.items():
        require(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", name),
                "An order-six module name is invalid.")
        relative = name.replace(".", "/") + ".lean"
        require(entry["path"] == relative, "An order-six source path differs.")
        path = source / relative
        require(not path.is_symlink(), "An order-six source is a symbolic link.")
        raw = path.read_bytes()
        require(len(raw) == entry["bytes"] and hashlib.sha256(raw).hexdigest() == entry["sha256"],
                "An order-six source hash differs: " + relative)
        imports = re.findall(r"^(?:public )?import ([A-Za-z_0-9.]+)", raw.decode(), re.M)
        require(imports == entry["imports"], "An order-six import list differs: " + relative)
        total += len(raw)
        seen.add(relative)
    actual = set()
    for path in source.rglob("*"):
        require(not path.is_symlink(), "An order-six source path is a symbolic link.")
        if path.is_file():
            actual.add(path.relative_to(source).as_posix())
    attribution = {"MathAndTheory/Mathematics/GyiresCirculant5/LICENSE",
                   "MathAndTheory/Mathematics/GyiresCirculant5/PROVENANCE.md"}
    require(actual == seen | attribution and total == 399233748, "The order-six source file set differs.")
    reached, visiting = set(), set()

    def visit(name):
        require(name not in visiting, "The order-six import graph has a cycle.")
        if name in reached:
            return
        visiting.add(name)
        for imported in modules[name]["imports"]:
            if imported in modules:
                visit(imported)
        visiting.remove(name)
        reached.add(name)

    visit("SixTheoremChecks")
    require(reached == set(modules), "An order-six source is outside the theorem dependency graph.")
    return len(modules)


if __name__ == "__main__":
    count = check_six(ROOT / "gyires-circulant-six")
    subprocess.run([sys.executable, "-B", str(ROOT / "gyires-permutation-polynomial/check_package.py")], check=True)
    print(json.dumps({"status": "PASS", "order_six_sources": count, "permutation_sources": 405,
                      "scope": "Source integrity and import coverage. No Lean compilation in this command."}))
