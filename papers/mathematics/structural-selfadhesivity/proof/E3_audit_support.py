"""Strict parser for Lean's two legitimate #print axioms output forms."""
import re

ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def audit_endpoints(source, output):
    expected = re.findall(r'^#print axioms\s+(\S+)\s*$', source, re.M)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError('Empty or duplicated endpoint inventory')
    if 'sorryAx' in output or 'error:' in output:
        raise ValueError('Axiom audit contains an error or admission')
    found = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
        output, re.S)
    if [name for name, _ in found] != expected:
        raise ValueError('Axiom audit endpoint names or order do not match the complete inventory')
    result = []
    for name, raw in found:
        axioms = {x.strip() for x in raw.split(',') if x.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(f'Unexpected axioms at {name}: {axioms - ALLOWED_AXIOMS}')
        result.append({'endpoint': name, 'axioms': sorted(axioms)})
    return result
