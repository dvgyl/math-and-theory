#!/usr/bin/env python3
"""Validate metadata against the pinned formalization.yaml v0.4 schema."""
from pathlib import Path
from urllib.request import urlopen
import hashlib,json
import jsonschema,yaml
ROOT=Path(__file__).resolve().parents[1]
URL="https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json"
EXPECTED="25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce"
data=urlopen(URL,timeout=60).read()
assert hashlib.sha256(data).hexdigest()==EXPECTED,"Schema hash mismatch"
schema=json.loads(data)
validator=jsonschema.validators.validator_for(schema)
validator.check_schema(schema)
document=yaml.safe_load((ROOT/'lean/formalization.yaml').read_text())
validator(schema).validate(document)
print(json.dumps({"status":"PASS","schema_revision":"99c678e569c7c4c0772db297c5ddd5e4c9b6322e","schema_sha256":EXPECTED,"metadata":"lean/formalization.yaml"},indent=2))
