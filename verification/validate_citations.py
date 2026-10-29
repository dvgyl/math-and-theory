"""Validate citation files against the pinned Citation File Format schema."""
from datetime import date
from pathlib import Path
from urllib.request import urlopen
import hashlib
import json
import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
URL = "https://raw.githubusercontent.com/citation-file-format/citation-file-format/1.2.0/schema.json"
EXPECTED = "0b8d22140da702d766df318dcff3a91af2f39521298dcf36d76315fd99cc169b"


def json_values(value):
    if isinstance(value, date):
        return value.isoformat()
    if isinstance(value, dict):
        return {key: json_values(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_values(item) for item in value]
    return value


def main():
    raw = urlopen(URL, timeout=60).read()
    if hashlib.sha256(raw).hexdigest() != EXPECTED:
        raise ValueError("The citation schema hash differs.")
    schema = json.loads(raw)
    files = [ROOT / "CITATION.cff"] + sorted((ROOT / "papers").rglob("CITATION.cff"))
    for path in files:
        document = json_values(yaml.safe_load(path.read_text()))
        jsonschema.validate(document, schema)
        if document.get("license") != "Apache-2.0":
            raise ValueError("The citation license differs from the package license.")
        if not path.with_suffix(".bib").is_file():
            raise ValueError("A BibTeX citation is missing.")
    print(json.dumps({"status": "PASS", "citation_files": len(files), "schema_sha256": EXPECTED}))


if __name__ == "__main__":
    main()
