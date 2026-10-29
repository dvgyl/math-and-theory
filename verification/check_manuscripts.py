#!/usr/bin/env python3
"""Build each manuscript and compare exact logical text and page coverage.

Position-based PDF extraction can reorder a fraction when glyph coordinates
change slightly between TeX engines. Raw extraction preserves content-stream
order. This is a text-consistency check; visual layout review remains separate.
"""

from pathlib import Path
import argparse
import json
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


def manuscript_engine(family):
    engine = family.get("manuscript_engine", "tectonic")
    if engine not in {"tectonic", "pdflatex"}:
        raise ValueError(f"Unsupported manuscript engine: {engine}")
    return engine


def check(root, engine_filter=None):
    root = Path(root).resolve()
    names = set(load_publication_files(root))
    families = load_families(root, names)
    catalogue = json.loads((root / "catalogue.json").read_text())
    overview_engine = manuscript_engine({"manuscript_engine": catalogue.get("overview_engine", "tectonic")})
    sources = [("overview.tex", "overview.pdf", overview_engine)]
    sources.extend((manuscript_source(family["paper"]), family["paper"], manuscript_engine(family))
                   for family in families)
    if len(sources) != len(families) + 1:
        raise ValueError("The manuscript source count differs from the catalogue.")
    if engine_filter is not None:
        if engine_filter not in {"tectonic", "pdflatex"}:
            raise ValueError("Unknown manuscript engine filter")
        sources = [item for item in sources if item[2] == engine_filter]
    with tempfile.TemporaryDirectory() as folder:
        for index, (source, committed, engine) in enumerate(sources):
            output = Path(folder) / str(index)
            output.mkdir()
            if engine == "tectonic":
                subprocess.run(["tectonic", "-X", "compile", source, "--outdir", str(output), "--keep-logs"],
                               cwd=root, check=True)
            else:
                subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
                                "-outdir=" + str(output), Path(source).name],
                               cwd=(root / source).parent, check=True)
            logs = list(output.glob("*.log"))
            if len(logs) != 1 or WARNINGS.search(logs[0].read_text(errors="replace")):
                raise ValueError(f"Manuscript has a warning or no unique log: {source}")
            rebuilt = output / Path(source).with_suffix(".pdf").name
            check_pdf_text(rebuilt, root / committed)
    return len(sources)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", choices=["tectonic", "pdflatex"],
                        help="Check only manuscripts using this engine; default checks the whole catalogue.")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    count = check(root, args.engine)
    print(f"PASS: rebuilt and compared {count} manuscripts ({args.engine or 'all catalogue entries and overview'}).")
