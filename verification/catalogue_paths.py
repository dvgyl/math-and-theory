"""Read manuscript paths and formalization kinds from one catalogue."""

import json
from pathlib import Path
import re

from publication_files import is_public_path


IDENTIFIER = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*\Z")


def manuscript_source(paper):
    """Return the TeX source for a catalogue PDF path."""
    if not isinstance(paper, str) or not paper.endswith(".pdf") or not is_public_path(paper):
        raise ValueError(f"Invalid manuscript path: {paper}")
    return paper[:-4] + ".tex"


def load_families(root, public_names=None):
    """Validate the catalogue routes and return its family records."""
    root = Path(root)
    record = json.loads((root / "catalogue.json").read_text())
    return validate_families(root, record, public_names)


def validate_families(root, record, public_names=None):
    """Validate family records from a supplied catalogue."""
    root = Path(root)
    families = record.get("families")
    if record.get("schema_version") != 1 or not isinstance(families, list) or not families:
        raise ValueError("The catalogue needs a nonempty version-one family list.")
    seen_ids = set()
    seen_papers = set()
    for family in families:
        if not isinstance(family, dict):
            raise ValueError("A catalogue family must be an object.")
        name = family.get("id")
        if not isinstance(name, str) or not IDENTIFIER.fullmatch(name) or name in seen_ids:
            raise ValueError(f"Invalid or repeated family identifier: {name}")
        seen_ids.add(name)
        paper = family.get("paper")
        source = manuscript_source(paper)
        if paper in seen_papers:
            raise ValueError(f"Repeated manuscript path: {paper}")
        seen_papers.add(paper)
        formalization = family.get("formalization")
        if not isinstance(formalization, dict):
            raise ValueError(f"Missing formalization kind: {name}")
        kind = formalization.get("kind")
        if kind == "comparator":
            if set(formalization) != {"kind"} or paper != f"preprints/{name}/paper.pdf":
                raise ValueError(f"Invalid Comparator route: {name}")
            if not all(key in family for key in ("module", "namespace", "comparator", "theorems")):
                raise ValueError(f"Missing Comparator fields: {name}")
            if family["comparator"] != f"lean/comparator/{name}.json":
                raise ValueError(f"Invalid Comparator path: {name}")
        elif kind == "standalone":
            package = f"verification/additional-proofs/{name}"
            if set(formalization) != {"kind", "root"} or formalization["root"] != package:
                raise ValueError(f"Invalid standalone route: {name}")
            if not paper.startswith(package + "/"):
                raise ValueError(f"Manuscript is outside its package: {name}")
            if any(key in family for key in ("module", "namespace", "comparator", "theorems")):
                raise ValueError(f"Standalone family has Comparator fields: {name}")
        else:
            raise ValueError(f"Unknown formalization kind: {name}")
        for path in (paper, source):
            if not (root / path).is_file():
                raise ValueError(f"Missing manuscript file: {path}")
            if public_names is not None and path not in public_names:
                raise ValueError(f"Manuscript file is absent from the publication list: {path}")
    return families
