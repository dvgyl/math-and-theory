"""Check six exact reports with the frozen package's already-tested fail-closed parser."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

AUDIT = Path(__file__).resolve().parent
PACKAGE = AUDIT.parent / 'rank-two'
EXPECTED_PARSER_SHA256 = '88ec257c2f37d74a17aa10e2da14e2c18b6885d7cca40809e45676ebf72e884b'

EXPECTED_REPORTS_SHA256 = '027bf5a8f3535ebc0a4046ed56c8804e9fa4d64be10a05e6b4af0055127730d0'

if len(sys.argv) != 2:
    raise SystemExit('Usage: python3 -B check_audit.py AUDIT_LOG')
parser_path = PACKAGE / 'check_package.py'
if hashlib.sha256(parser_path.read_bytes()).hexdigest() != EXPECTED_PARSER_SHA256:
    raise SystemExit('The frozen parser hash differs.')
spec = importlib.util.spec_from_file_location('frozen_rank_two_parser', parser_path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
try:
    expected_path = AUDIT / 'expected-axioms.json'
    if hashlib.sha256(expected_path.read_bytes()).hexdigest() != EXPECTED_REPORTS_SHA256:
        raise ValueError('The six expected report names changed.')
    expected = json.loads(expected_path.read_text())
    module.check_axioms(Path(sys.argv[1]), expected)
except (OSError, ValueError, KeyError, TypeError) as error:
    raise SystemExit(str(error))
print('Six exact scoped audit reports passed.')
