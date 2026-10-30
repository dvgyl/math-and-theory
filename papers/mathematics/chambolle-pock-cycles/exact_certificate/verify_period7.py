#!/usr/bin/env python3
"""Independent exact arithmetic audit; Python standard library only."""
import json
from fractions import Fraction as Q
from pathlib import Path

path=Path(__file__).with_name('period7_rational_certificate.json')
data=json.loads(path.read_text())
X=[[Q(v) for v in row] for row in data['X']]
Y=[[Q(v) for v in row] for row in data['Y']]
n=data['period'];dim=data['dimension']
assert len(X)==len(Y)==n
assert all(len(row)==dim for row in X+Y)
assert all(sum(row[j] for row in X)==0 for j in range(dim))
assert all(sum(row[j] for row in Y)==0 for j in range(dim))
assert X[0]!=X[1]
if 'common_denominator' in data:
    scale=data['common_denominator']
    assert [[scale*v for v in row] for row in X]==data['X_integer_scaled']
    assert [[scale*v for v in row] for row in Y]==data['Y_integer_scaled']

def sub(a,b):return [aa-bb for aa,bb in zip(a,b)]
def dot(a,b):return sum((aa*bb for aa,bb in zip(a,b)),Q(0))

primal=[]
for i in range(n):
    p=(i-1)%n
    normal=sub(sub(X[p],Y[p]),X[i])
    primal.extend(dot(normal,sub(X[j],X[i])) for j in range(n) if j!=i)
assert max(primal)<0

corners=[]
for kappa in (Q(2499,1000),Q(2501,1000)):
    for theta in (Q(0),Q(1,400)):
        dual=[]
        for i in range(n):
            p=(i-1)%n
            normal=[yp+kappa*((1+theta)*xx-theta*xp)-yy
                    for yp,xx,xp,yy in zip(Y[p],X[i],X[p],Y[i])]
            dual.extend(dot(normal,sub(Y[j],Y[i])) for j in range(n) if j!=i)
        assert max(dual)<0
        corners.append({'kappa':str(kappa),'theta':str(theta),'dual_count':len(dual),
                        'max_dual':str(max(dual))})
print(json.dumps({'verified':True,'period':n,'dimension':dim,
                  'primal_count':len(primal),'max_primal':str(max(primal)),
                  'corners':corners,'centers_exactly_zero':True,'nonconstant':True},indent=2))
