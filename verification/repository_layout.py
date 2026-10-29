"""Canonical subject/family routes derived from the manuscript catalogue.

A new result supplies its discipline and identifier in catalogue.json. The only
aliases group multiple manuscripts within one scientific family.
"""
import json
from pathlib import Path
import re

SUBJECTS = {
    'Mathematics': 'mathematics',
    'Theoretical computer science': 'theoretical-computer-science',
    'Mathematical physics': 'physics',
}
GROUPS = {
    'gyires-circulant-five': 'gyires',
    'alternating-motzkin': 'motzkin',
    'motzkin-bounded-forcing': 'motzkin/bounded-forcing',
}
CATALOGUE = json.loads((Path(__file__).resolve().parents[1] / 'catalogue.json').read_text())
DISCIPLINES = {f['id']: f['discipline'] for f in CATALOGUE['families']}


def family_root(name, discipline=None):
    if not isinstance(name, str) or not re.fullmatch(r'[a-z0-9]+(?:-[a-z0-9]+)*', name):
        raise ValueError('Invalid family identifier')
    if discipline is None and name not in DISCIPLINES:
        raise ValueError('Unregistered family identifier')
    discipline = discipline or DISCIPLINES[name]
    if discipline not in SUBJECTS:
        raise ValueError('Unknown discipline')
    return 'papers/' + SUBJECTS[discipline] + '/' + GROUPS.get(name, name)


FAMILY_ROOTS = {name: family_root(name) for name in DISCIPLINES}
