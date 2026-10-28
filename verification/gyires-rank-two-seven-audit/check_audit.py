"""Check six exact reports with the frozen package's already-tested fail-closed parser."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

AUDIT = Path(__file__).resolve().parent
PACKAGE = AUDIT.parent / 'gyires-rank-two'
EXPECTED_PARSER_SHA256 = '9427133fee3a3299cc004369f6216407fc43e5d38205df4186a170644fbfe64f'

EXPECTED_REPORTS_SHA256 = '68c1ff1e4261b1835e1f86e16949c9a57dc16ed166f4693ab4e50773552d9561'

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
