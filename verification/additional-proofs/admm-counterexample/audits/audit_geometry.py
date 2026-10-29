"""Exact rational audit of the ADMM five-cycle.

This script uses only Python's exact Fraction arithmetic. The accompanying Lean
files, not this script, supply kernel-checked proofs of the formal statement.
Pass the exact JSON path explicitly to check another input.
"""

# Assertions are part of this certificate.
import os as _assertion_guard_os
if not __debug__ or "PYTHONOPTIMIZE" in _assertion_guard_os.environ:
    raise SystemExit("Verification requires assertions; remove -O/-OO and unset PYTHONOPTIMIZE.")
import json
import sys
from fractions import Fraction as Q
from pathlib import Path


def add(a, b):
    return [x+y for x,y in zip(a,b)]


def sub(a, b):
    return [x-y for x,y in zip(a,b)]


def scale(t, a):
    return [t*x for x in a]


def dot(a, b):
    return sum(x*y for x,y in zip(a,b))


def determinant(matrix):
    a = [[Q(x) for x in row] for row in matrix]
    result = Q(1)
    for i in range(len(a)):
        pivot = next(j for j in range(i,len(a)) if a[j][i])
        if pivot != i:
            a[i],a[pivot] = a[pivot],a[i]
            result = -result
        result *= a[i][i]
        for j in range(i+1,len(a)):
            factor = a[j][i]/a[i][i]
            a[j] = sub(a[j],scale(factor,a[i]))
    return result


def main(path):
    data = json.loads(Path(path).read_text())
    tau = Q(data["tau"])
    assert tau == Q(199,100) and Q(0) < tau < Q(2)
    z,v,x,u = [[[Q(t) for t in row] for row in data[name]]
               for name in ("Z","V","X","U")]
    K = len(z)
    assert K == 5 and all(len(row)==4 for row in z+v+x+u)
    for i in range(K):
        prev=(i-1)%K
        assert u[i] == scale(tau,v[i])
        assert x[i] == add(z[i],sub(v[i],v[prev]))
        assert u[i] == add(u[prev],scale(tau,sub(x[i],z[i])))
    margins=[]
    lower=[]
    upper=[]
    for i in range(K):
        prev=(i-1)%K
        for name,vertices,normal0,normal1 in [
            ("C",x,sub(z[prev],x[i]),scale(-1,v[prev])),
            ("D",z,sub(x[i],z[i]),v[prev])]:
            normal=add(normal0,scale(tau,normal1))
            for j in range(K):
                difference=sub(vertices[j],vertices[i])
                margin=-dot(normal,difference)
                assert margin == 0 if i==j else margin > 0
                if i==j:
                    continue
                margins.append((margin,name,i,j))
                alpha=dot(normal0,difference)
                beta=dot(normal1,difference)
                if beta < 0:
                    lower.append((-alpha/beta,name,i,j))
                elif beta > 0:
                    upper.append((-alpha/beta,name,i,j))
                else:
                    assert alpha <= 0
    centroids={name:[sum(row[j] for row in points) for j in range(4)]
               for name,points in [("X",x),("Z",z),("U",u)]}
    assert all(all(t==0 for t in row) for row in centroids.values())
    dets={name:determinant([sub(points[i],points[0]) for i in range(1,5)])
          for name,points in [("X",x),("Z",z)]}
    assert all(t != 0 for t in dets.values())
    residuals=[dot(sub(x[i],z[i]),sub(x[i],z[i])) for i in range(K)]
    assert all(t>0 for t in residuals)
    assert len(margins)==40
    assert min(margins)[0] == Q(136989,100)
    assert max(lower)[0] == Q(140111,70637)
    assert not upper
    out={"tau":str(tau),"normal_checks":len(margins),
         "minimum_margin":str(min(margins)[0]),
         "valid_tau_lower_endpoint":str(max(lower)[0]),
         "binding_constraint":max(lower)[1:],
         "valid_tau_upper_endpoint":None,
         "determinants":{k:str(t) for k,t in dets.items()},
         "residual_squared":[str(t) for t in residuals],
         "centroids_zero":True,"exact_recurrence":True}
    print(json.dumps(out,indent=2))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv)>1 else
         str(Path(__file__).resolve().parent.parent / "data/admm_exact_K5_tau199over100.json"))
