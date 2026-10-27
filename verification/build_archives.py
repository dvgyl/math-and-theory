#!/usr/bin/env python3
"""Build manuscript packages from the checked publication manifest."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tempfile
import zipfile

from publication_files import HASHES, load_publication_files
from verify_hashes import verify


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
    catalogue = json.loads(contents["catalogue.json"])
    manifest_digest = hashlib.sha256(contents[HASHES]).hexdigest()
    families = [family["id"] for family in catalogue["families"]]
    if not families or len(families) != len(set(families)) or any(
        not isinstance(name, str) or re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name) is None
        for name in families
    ):
        raise ValueError("The catalogue must contain unique valid family identifiers.")
    for name in families:
        check_output(output / f"{name}.pdf")
        check_output(output / f"{name}-archival-package.zip")
    check_output(output / "packages.json")
    results = []
    for name in families:
        pdf = output / f"{name}.pdf"
        archive = output / f"{name}-archival-package.zip"
        atomic_write(pdf, contents[f"preprints/{name}/paper.pdf"])
        metadata = {
            "family": name,
            "manuscript": f"math-and-theory/preprints/{name}/paper.pdf",
            "source_manifest_sha256": manifest_digest,
            "scope": "See the manuscript and formal guide for the exact theorem and verification scope.",
        }
        members = {f"math-and-theory/{path}": content for path, content in contents.items()}
        members["PACKAGE.json"] = (json.dumps(metadata, indent=2) + "\n").encode()
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
        results.append({"family": name, "pdf": pdf.name, "archive": archive.name,
                        "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
                        "archive_sha256": hashlib.sha256(archive.read_bytes()).hexdigest(),
                        "archive_members": len(members)})
    atomic_write(output / "packages.json", (json.dumps(results, indent=2) + "\n").encode())
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    print(json.dumps(build(root, args.output.resolve()), indent=2))
