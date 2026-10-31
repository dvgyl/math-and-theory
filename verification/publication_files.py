"""Validate the explicit list of files for publication."""
from pathlib import Path, PurePosixPath
import json

MANIFEST = "publication-files.json"
HASHES = "verification/records/source-hashes.json"
EXCLUDED_DIRS = {".claude", ".git", ".lake", ".venv", "__pycache__"}
BUILD_SUFFIXES = {".aux", ".bbl", ".blg", ".out", ".toc", ".pyc"}


def is_public_path(name):
    """Return whether the path can identify a publication file."""
    if not isinstance(name, str) or not name:
        return False
    path = PurePosixPath(name)
    return (
        not path.is_absolute() and path.as_posix() == name and "\\" not in name
        and not any(part in EXCLUDED_DIRS or part in {".", ".."} for part in path.parts)
        and path.suffix not in BUILD_SUFFIXES and path.name != ".DS_Store"
        # The shared research ledger and its registration notes are updated by concurrent
        # sessions; they are not publication files.
        and name != "ACTIVE_PROBLEMS.md" and path.parts[:2] != ("research", "active")
        and (path.suffix != ".log" or path.parts[0] in {"verification", "papers"})
    )


def load_publication_files(root):
    """Require complete file coverage, valid paths, and no symbolic links."""
    root = Path(root).resolve()
    record = json.loads((root / MANIFEST).read_text())
    names = record.get("files")
    if record.get("format_version") != 1 or not isinstance(names, list) or not names:
        raise ValueError("The publication manifest must contain a nonempty file list.")
    if any(not is_public_path(name) for name in names):
        raise ValueError("The publication manifest contains an invalid path.")
    if names != sorted(set(names)):
        raise ValueError("Publication paths must be sorted and unique.")
    if not {MANIFEST, HASHES}.issubset(names):
        raise ValueError("The publication manifest must include both integrity records.")
    for name in names:
        path = root / name
        if not path.is_file():
            raise ValueError(f"Publication file is missing: {name}")
        cursor = path
        while cursor != root:
            if cursor.is_symlink():
                raise ValueError(f"Publication path contains a symbolic link: {name}")
            cursor = cursor.parent
    actual = {
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_file() and is_public_path(path.relative_to(root).as_posix())
    }
    if actual != set(names):
        missing = sorted(actual - set(names))
        extra = sorted(set(names) - actual)
        raise ValueError(f"Publication coverage differs. Unlisted: {missing}; absent: {extra}")
    return names
