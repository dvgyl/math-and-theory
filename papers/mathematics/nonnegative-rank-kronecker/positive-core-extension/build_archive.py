#!/usr/bin/env python3
"""Create the source-and-evidence release archive without dependency/build caches.

The fixed ZIP member timestamp makes the archive reproducible from unchanged
deliverable bytes. The manifest hashes every packaged file except itself.
"""

import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent


def include(path):
    relative = path.relative_to(ROOT)
    if not path.is_file() or any(x in relative.parts for x in (".lake", "__pycache__")):
        return False
    if relative.as_posix() in {"manuscript.aux", "manuscript.log", "manuscript.out",
                              "release-manifest.json"}:
        return False
    return True


if __name__ == "__main__":
    files = sorted(p for p in ROOT.rglob("*") if include(p))
    manifest = {"archive_root": ROOT.name,
                "excluded": ["Lean dependency and project build caches", "Python bytecode",
                             "temporary LaTeX outputs"],
                "files": {p.relative_to(ROOT).as_posix():
                          {"sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                           "bytes": p.stat().st_size} for p in files}}
    manifest_path = ROOT/"release-manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True)+"\n")
    archive = ROOT.parent/(ROOT.name+".zip")
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(files+[manifest_path]):
            info = zipfile.ZipInfo(f"{ROOT.name}/{p.relative_to(ROOT).as_posix()}",
                                  date_time=(2026, 11, 4, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    checksum = hashlib.sha256(archive.read_bytes()).hexdigest()
    archive.with_suffix(archive.suffix+".sha256").write_text(f"{checksum}  {archive.name}\n")
    print(json.dumps({"archive": str(archive), "bytes": archive.stat().st_size,
                      "members": len(files)+1, "sha256": checksum}, indent=2))
