#!/usr/bin/env python3
"""Build each manuscript and compare exact logical text and page coverage.

Position-based PDF extraction can reorder a fraction when glyph coordinates
change slightly between TeX engines. Raw extraction preserves content-stream
order. This is a text-consistency check; visual layout review remains separate.
"""

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


def pdf_content(path):
    text = subprocess.run(["pdftotext", "-raw", str(path), "-"],
                          check=True, capture_output=True).stdout
    info = subprocess.run(["pdfinfo", str(path)], check=True,
                          capture_output=True, text=True).stdout
    match = re.search(r"^Pages:\s+([0-9]+)\s*$", info, re.M)
    if match is None or int(match[1]) < 1:
        raise ValueError(f"PDF has no valid page count: {path}")
    pages = int(match[1])
    if not text.strip() or text.count(b"\f") != pages:
        raise ValueError(f"PDF text is empty or has incomplete page coverage: {path}")
    return text, pages


def check_pdf_text(rebuilt, committed):
    text, pages = pdf_content(rebuilt)
    original, original_pages = pdf_content(committed)
    if pages != original_pages or text != original:
        raise ValueError(f"Committed manuscript text or page count differs from its source: {committed}")


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
            check_pdf_text(rebuilt, root / committed)
    return len(sources)


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1]
    print(f"PASS: rebuilt the overview and {check(root) - 1} catalogue manuscripts.")
