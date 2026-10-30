#!/usr/bin/env python3
"""Independent exact check of the separating identity in ordinary h-coordinates.

No optimization, floating point, search model, or standardized m-coordinates.
Every variable is a formal real-valued polymatroid coordinate, with only
normalization and the two numerically identical copy restrictions substituted.
"""
from pathlib import Path
from collections import defaultdict
import itertools,json,hashlib

ROOT=Path(__file__).resolve().parent
PATTERN='01111101110000011101001111010011011111010111111101111110111101011111010101100101'
CERT=ROOT/'E3_dual_certificate.json'
c=json.loads(CERT.read_text())
assert c['pattern']==PATTERN and c['target_ci_index']==47

def cis(n):
    for i,j in itertools.combinations(range(n),2):
        rest=[x for x in range(n) if x not in(i,j)]
        for k in range(n-1):
            for t in itertools.combinations(rest,k):yield i,j,sum(1<<x for x in t)

base_cis=list(cis(5))

def copy_map(L):
    nxt=5;out=[]
    for i in range(5):
        if L>>i&1:out.append(i)
        else:out.append(nxt);nxt+=1
    return out

def coord(L,S):
    if S==0:return None
    if L is None or S&31==S:return ('base',S)
    cp=copy_map(L);C=sum(1<<i for i in cp)
    if S&C==S:return ('base',sum(1<<i for i,x in enumerate(cp) if S>>x&1))
    return ('copy'+str(L),S)

total=defaultdict(int)
def add_values(L,values,coefficient):
    for S,v in values:
        key=coord(L,S)
        if key is not None:total[key]+=coefficient*v

def add_ci(L,ci,coefficient):
    i,j,K=ci
    assert i!=j and not K&(1<<i|1<<j)
    if L is not None:
        assert 0<=i<10-L.bit_count() and 0<=j<10-L.bit_count()
        assert 0<=K<1<<(10-L.bit_count())
    add_values(L,[(K|1<<i,1),(K|1<<j,1),(K,-1),(K|1<<i|1<<j,-1)],coefficient)

add_ci(None,base_cis[47],c['target_multiplier'])
assert c['target_multiplier']>0 and PATTERN[47]=='1'
for row in c['inequalities']:
    assert isinstance(row['coefficient'],int) and row['coefficient']>=0
    add_ci(row['overlap'],row['ci_local'],row['coefficient'])
for row in c['equalities']:
    q=row['coefficient']
    assert isinstance(q,int)
    if row['kind']=='base_CI':
        i=row['base_ci_index'];assert PATTERN[i]=='0'
        add_ci(None,base_cis[i],q)
    else:
        assert row['kind']=='group'
        L=row['overlap'];C=sum(1<<i for i in copy_map(L))
        assert C&31==L
        add_values(L,[(31,1),(C,1),(L,-1),(C|31,-1)],q)

residual={str(k):v for k,v in total.items() if v}
assert not residual,residual
result={'exact_identity_passed':True,'coordinate_system':'ordinary polymatroid h',
        'normalization_only':True,'shared_copy_restrictions_used':True,
        'target':'I(2;4|1,3,5)','positive_target_multiplier':c['target_multiplier'],
        'elementary_nonnegative_terms':len(c['inequalities']),
        'source_zero_CIs':sum(r['kind']=='base_CI' for r in c['equalities']),
        'adhesion_equalities':[r['overlap'] for r in c['equalities'] if r['kind']=='group'],
        'residual_coordinate_count':0,'lean_verified':False,
        'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest()}
(ROOT/'E3_negative_check_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
