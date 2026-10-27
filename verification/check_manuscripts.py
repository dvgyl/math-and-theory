#!/usr/bin/env python3
"""Build the overview and every catalogue manuscript."""

from pathlib import Path
import re
import subprocess
import tempfile

from catalogue_paths import load_families, manuscript_source
from publication_files import load_publication_files


WARNINGS = re.compile(
    r"undefined references|undefined citations|Citation .* undefined|Reference .* undefined|Overfull|Missing character",
    re.I,
)


def check(root):
    root = Path(root).resolve()
    names = set(load_publication_files(root))
    families = load_families(root, names)
    sources = [("overview.tex", "overview.pdf")]
    sources.extend((manuscript_source(family["paper"]), family["paper"]) for family in families)
    if len(sources) != len(families) + 1:
        raise ValueError("The manuscript source count differs from the catalogue.")
    with tempfile.TemporaryDirectory() as folder:
        for index, (source, committed) in enumerate(sources):
            output = Path(folder) / str(index)
            output.mkdir()
            subprocess.run(["tectonic", "-X", "compile", source, "--outdir", str(output), "--keep-logs"],
                           cwd=root, check=True)
            logs = list(output.glob("*.log"))
            if len(logs) != 1 or WARNINGS.search(logs[0].read_text(errors="replace")):
                raise ValueError(f"Manuscript has a warning or no unique log: {source}")
            rebuilt = output / Path(source).with_suffix(".pdf").name
            text = subprocess.run(["pdftotext", "-layout", str(rebuilt), "-"],
                                  check=True, capture_output=True).stdout
            original = subprocess.run(["pdftotext", "-layout", str(root / committed), "-"],
                                      check=True, capture_output=True).stdout
            if not text or text != original:
                raise ValueError(f"Committed manuscript text differs from its source: {committed}")
    return len(sources)


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1]
    print(f"PASS: rebuilt the overview and {check(root) - 1} catalogue manuscripts.")
