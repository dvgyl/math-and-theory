"""Independent exact audit of supplied HS SOS against direct density determinants.
Does not import the generating code. Every coefficient is an arbitrary-precision int.
A key is a pair of sorted triples of holomorphic and antiholomorphic indices.
"""

from pathlib import Path
import os
import tempfile

root = Path(__file__).resolve().parents[1]
report_path = root / "certificates/independent_audit.json"
report_path.unlink(missing_ok=True)

if not __debug__:
    raise SystemExit("Run this verifier without Python optimization.")
import json
import itertools as it
from collections import Counter


def reject_number(value):
    raise ValueError('Certificate numbers must be JSON integers.')


def unique_object(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError('Duplicate JSON field: ' + key)
        result[key] = value
    return result


data=json.loads((root/'certificates/sos_integer.json').read_text(),
                parse_float=reject_number, parse_constant=reject_number,
                object_pairs_hook=unique_object)
assert type(data) is dict and set(data) == {'statement', 'variables', 'cubic_convention', 'sos', 'minors', 'check'}
assert data['statement'] == '6400*norm^6-46080*sum_abs_squared_3x3_minors=sum_weighted_abs_squared_cubics'
assert type(data['variables']) is int and data['variables'] == 16
assert data['cubic_convention'] == 'each key i,j,k means z_i*z_j*conj(z_k)'
assert type(data['minors']) is list and len(data['minors']) == 48
assert type(data['sos']) is list and len(data['sos']) == 272


def check_terms(terms, minor=False):
    assert type(terms) is list and terms
    keys = set()
    for term in terms:
        assert type(term) is list and len(term) == 4
        assert all(type(v) is int for v in term)
        i, j, k, coefficient = term
        assert 0 <= i < 16 and 0 <= j < 16 and 0 <= k < 16
        assert coefficient != 0
        if minor:
            assert i < j < k and coefficient in {-1, 1}
        else:
            assert i <= j
        key = (i, j, k)
        assert key not in keys
        keys.add(key)


for minor in data['minors']:
    assert len(minor) == 6
    check_terms(minor, minor=True)
for form in data['sos']:
    assert type(form) is dict and set(form) == {'weight', 'terms'}
    assert type(form['weight']) is int and form['weight'] > 0
    check_terms(form['terms'])
expected_check = {'identity_verified_exactly': True, 'integer_coefficients': True,
                  'sos_forms': 272, 'minor_forms': 48, 'target_nonzero_terms': 1968,
                  'rhs_nonzero_terms': 1968, 'difference_terms': 0, 'maximum_cubic_terms': 41}
assert type(data['check']) is dict and set(data['check']) == set(expected_check)
assert all(type(data['check'][key]) is type(value) and data['check'][key] == value
           for key, value in expected_check.items())
assert max(map(lambda form: len(form['terms']), data['sos'])) == 41

# Direct determinant expansion of 3x3 principal submatrices of M M*,
# without passing through the supplied 3x3 minor representation.
def state_index(row,col,paired):
    result=0
    remaining=tuple(i for i in range(4) if i not in paired)
    for site,bit in zip(paired, (row//2,row%2)):
        result += bit * 2**(3-site)
    for site,bit in zip(remaining, (col//2,col%2)):
        result += bit * 2**(3-site)
    return result

principal_e3=Counter()
for paired in [(0,1),(0,2),(0,3)]:
    for selected in it.combinations(range(4),3):
        for perm in it.permutations(range(3)):
            sign=1 if sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))%2==0 else -1
            for columns in it.product(range(4),repeat=3):
                holo=tuple(sorted(state_index(selected[i],columns[i],paired) for i in range(3)))
                anti=tuple(sorted(state_index(selected[perm[i]],columns[i],paired) for i in range(3)))
                principal_e3[holo,anti]+=sign
principal_e3={k:v for k,v in principal_e3.items() if v}

cofactor_e3=Counter()
for minor in data['minors']:
    for i,j,k,a in minor:
        for p,q,r,b in minor:
            cofactor_e3[tuple(sorted((i,j,k))),tuple(sorted((p,q,r)))]+=a*b
cofactor_e3={k:v for k,v in cofactor_e3.items() if v}
assert cofactor_e3==principal_e3,'The minor and direct density definitions differ'

lhs=Counter({k:-46080*v for k,v in principal_e3.items()})
for i,j,k in it.product(range(16),repeat=3):
    triple=tuple(sorted((i,j,k)))
    lhs[triple,triple]+=6400
lhs={k:v for k,v in lhs.items() if v}

rhs=Counter()
for form in data['sos']:
    assert isinstance(form['weight'],int) and form['weight']>0
    assert all(isinstance(v,int) for term in form['terms'] for v in term)
    for i,j,k,a in form['terms']:
        for p,q,r,b in form['terms']:
            rhs[tuple(sorted((i,j,r))),tuple(sorted((k,p,q)))]+=form['weight']*a*b
rhs={k:v for k,v in rhs.items() if v}
assert lhs==rhs,'The direct density LHS and supplied SOS differ'
result={
 'direct_density_e3_matches_minor_sum':True,
 'direct_density_target_matches_sos':True,
 'arithmetic':'exact Python arbitrary precision integers',
 'number_of_amplitudes':16,
 'independent_formal_variables':32,
 'subspace_assumptions':None,
 'normalization_assumption_for_identity':None,
 'partitions':['AB|CD','AC|BD','AD|BC'],
 'e3_nonzero_terms':len(principal_e3),
 'identity_nonzero_terms':len(lhs),
 'positive_weighted_squares':len(data['sos']),
 'formal_proof_status':'No Lean verification performed by this script'
}
encoded = json.dumps(result, indent=2) + '\n'
temporary_path = None
try:
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8',
                                     dir=report_path.parent, prefix='.audit-',
                                     delete=False) as stream:
        temporary_path = Path(stream.name)
        stream.write(encoded)
    os.replace(temporary_path, report_path)
finally:
    if temporary_path is not None:
        temporary_path.unlink(missing_ok=True)
print(encoded, end='')
