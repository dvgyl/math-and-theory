#!/usr/bin/env python3
"""Check generated CI work copies without changing the release packages."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git(path, *args):
    return subprocess.run(["git", "-C", str(path), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


def check_dependencies(workcopy):
    """Require every read-k checkout to match its Lake lock."""
    workcopy = Path(workcopy)
    lock = json.loads((workcopy / "lake-manifest.json").read_text())
    packages = lock["packages"]
    require(len(packages) == 9 and len({entry["name"] for entry in packages}) == 9,
            "The read-k lock does not list nine unique dependencies.")
    for entry in packages:
        checkout = workcopy / ".lake/packages" / entry["name"]
        require(checkout.is_dir() and not checkout.is_symlink() and (checkout / ".git").exists(),
                f"Missing dependency checkout: {entry['name']}")
        require(git(checkout, "rev-parse", "HEAD") == entry["rev"],
                f"Wrong dependency revision: {entry['name']}")
        subprocess.run(["git", "-C", str(checkout), "diff", "--quiet", "HEAD", "--"], check=True)
    return len(packages)


def check_copy(original, workcopy, source_only=False):
    """Check the source files after a wrapper writes generated evidence."""
    original = Path(original)
    workcopy = Path(workcopy)
    require(original.is_dir() and workcopy.is_dir() and not original.is_symlink()
            and not workcopy.is_symlink(), "Invalid package or work-copy directory")
    require((original / "manifest.json").read_bytes() == (workcopy / "manifest.json").read_bytes(),
            "The work copy changed its release manifest.")
    manifest = json.loads((original / "manifest.json").read_text())
    names = set(manifest["files"])
    if source_only:
        names = set()
        for line in (original / "SOURCE_SHA256SUMS").read_text().splitlines():
            expected, name = line.split("  ", 1)
            require(expected == manifest["files"][name]["sha256"],
                    f"Source checksum differs from the release manifest: {name}")
            names.add(name)
    for name in names:
        path = workcopy / name
        require(not path.is_symlink(), f"Symbolic link in work copy: {name}")
        actual = path.read_bytes()
        entry = manifest["files"][name]
        require(len(actual) == entry["bytes"] and hashlib.sha256(actual).hexdigest() == entry["sha256"],
                f"Changed source or build-control file in work copy: {name}")
    return len(names)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=("readk", "thermal"))
    parser.add_argument("original", type=Path)
    parser.add_argument("workcopy", type=Path)
    args = parser.parse_args()
    count = check_copy(args.original, args.workcopy, source_only=args.kind == "readk")
    if args.kind == "readk":
        check_dependencies(args.workcopy)
    print(f"PASS: {count} unchanged package files; {args.kind} dependency checks passed.")
