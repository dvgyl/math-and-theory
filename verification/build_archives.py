#!/usr/bin/env python3
"""Export one complete source archive and individually indexed manuscripts."""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile
import zipfile

from publication_files import HASHES, load_publication_files
from verify_hashes import verify
from catalogue_paths import validate_families
from check_embedded_packages import check_packages, EXPECTED_MANIFESTS


def check_output(path):
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise ValueError(f"The output must be a regular file: {path.name}")


def atomic_write(path, content):
    check_output(path)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(content)
    try:
        check_output(path)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def build(root, output):
    root, output = Path(root).resolve(), Path(output).resolve()
    verify(root)
    names = load_publication_files(root)
    if root == output or root in output.parents:
        raise ValueError("The archive output directory must be outside the source repository.")
    output.mkdir(parents=True, exist_ok=True)
    contents = {path: (root / path).read_bytes() for path in names}
    hashes = json.loads(contents[HASHES])["files"]
    if set(hashes) != set(names) - {HASHES}:
        raise ValueError("The source manifest changed during archive preparation.")
    for name, digest in hashes.items():
        if hashlib.sha256(contents[name]).hexdigest() != digest:
            raise ValueError(f"Source changed during archive preparation: {name}")
    families = validate_families(root, json.loads(contents["catalogue.json"]), set(names))
    standalone_roots = [family["formalization"]["root"] + "/" for family in families
                        if family["formalization"]["kind"] == "standalone"]
    manifests = {}
    registry = {}
    if standalone_roots:
        registry_path = "verification/curated-packages.json"
        registry = json.loads(contents[registry_path])["packages"]
        with tempfile.TemporaryDirectory() as folder:
            snapshot = Path(folder)
            for name, content in contents.items():
                if name == registry_path or any(name.startswith(prefix) for prefix in standalone_roots):
                    target = snapshot / name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(content)
            manifests = check_packages(snapshot, families)
    manifest_digest = hashlib.sha256(contents[HASHES]).hexdigest()
    archive = output / "math-and-theory-source.zip"
    for path in [archive, output / "packages.json", *(output / f"{family['id']}.pdf" for family in families)]:
        check_output(path)
    metadata = []
    for family in families:
        name = family["id"]
        entry = {
            "family": name,
            "manuscript": f"math-and-theory/{family['paper']}",
            "source_manifest_sha256": manifest_digest,
            "scope": "See the manuscript and formal guide for the exact theorem and verification scope.",
        }
        if family["formalization"]["kind"] == "standalone":
            package = manifests[name]
            entry["scope"] = package["formal_scope"]
            proof = {"kind": "standalone",
                     "root": f"math-and-theory/{family['formalization']['root']}"}
            if name in registry:
                proof["manifest_sha256"] = registry[name]["release_manifest_sha256"]
                proof["proof_roots"] = package["proof_roots"]
            else:
                proof.update(manifest_sha256=EXPECTED_MANIFESTS[name],
                             lean_version=package["lean_version"],
                             mathlib_revision=package["mathlib_revision"])
            entry["formalization"] = proof
        metadata.append(entry)
    members = {f"math-and-theory/{path}": content for path, content in contents.items()}
    members["PACKAGE.json"] = (json.dumps({"format_version": 2, "manuscripts": metadata},
                                         indent=2) + "\n").encode()
    with tempfile.NamedTemporaryFile(dir=output, delete=False) as stream:
        temporary = Path(stream.name)
    try:
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as bundle:
            for member, content in sorted(members.items()):
                info = zipfile.ZipInfo(member, date_time=(2000, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                bundle.writestr(info, content)
        with zipfile.ZipFile(temporary) as bundle:
            if set(bundle.namelist()) != set(members) or bundle.testzip() is not None:
                raise ValueError(f"Archive integrity check failed: {archive.name}")
            for member, content in members.items():
                if bundle.read(member) != content:
                    raise ValueError(f"Archive member differs: {member}")
        check_output(archive)
        temporary.replace(archive)
    finally:
        temporary.unlink(missing_ok=True)
    archive_digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    results = []
    for family in families:
        name = family["id"]
        pdf = output / f"{name}.pdf"
        atomic_write(pdf, contents[family["paper"]])
        results.append({"family": name, "pdf": pdf.name, "archive": archive.name,
                        "pdf_sha256": hashlib.sha256(contents[family["paper"]]).hexdigest(),
                        "archive_sha256": archive_digest,
                        "archive_members": len(members)})
    atomic_write(output / "packages.json", (json.dumps(results, indent=2) + "\n").encode())
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    print(json.dumps(build(root, args.output.resolve()), indent=2))
