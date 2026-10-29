
if not __debug__:
    raise RuntimeError("Run this checker without Python optimization so that all mathematical checks execute.")

from itertools import combinations
from fractions import Fraction
import json
import sys
import sympy as S
import mpmath as mp

mp.mp.dps = 80
edges = set()
for group in ([1, 2], [3, 4, 5], [6, 7, 8]):
    edges.update(combinations(group, 2))
for i in [0, 1, 2]:
    edges.update((i, j) for j in range(3, 10))
edges.update((9, j) for j in range(10, 14))
A = S.zeros(14)
for i, j in edges:
    A[i, j] = A[j, i] = 1
assert len(edges) == 32
seen = {0}
while True:
    extended = seen | {j for i in seen for j in range(14) if A[i,j]}
    if extended == seen:
        break
    seen = extended
assert len(seen) == 14
d = A * S.ones(14, 1)
assert list(d) == [7, 8, 8, 5, 5, 5, 5, 5, 5, 7, 1, 1, 1, 1]
M = 15*S.eye(14)+4*A
L, D = M.LDLdecomposition(hermitian=False)
assert L*D*L.T == M
assert all(D[i,i]>0 for i in range(14))
s = S.symbols('s')
classes = [[0], [1,2], list(range(3,9)), [9], list(range(10,14))]
B = S.Matrix([[sum(A[g[0],j] for j in h) for h in classes] for g in classes])
u = (S.eye(5)+s*B).inv()*S.Matrix([d[g[0]] for g in classes])
u = u.applyfunc(S.factor)
full_u = S.Matrix([u[next(k for k,g in enumerate(classes) if i in g)] for i in range(14)])
assert (S.eye(14)+s*A)*full_u-S.Matrix(d) == S.zeros(14,1) or all(S.simplify(x)==0 for x in (S.eye(14)+s*A)*full_u-d)
for f in u:
    num, den = S.fraction(f)
    assert S.Poly(num,s).count_roots(S.Rational(251,1000),S.Rational(63,250)) == 0
    assert S.Poly(den,s).count_roots(S.Rational(251,1000),S.Rational(63,250)) == 0
    assert f.subs(s,S.Rational(251,1000)) > 0

K = S.diag(*map(len,classes))*(15*S.eye(5)+4*B)
minors = [K[:i,:i].det() for i in range(1,6)]
assert minors == [15,570,22212,116796,1321488]

def real(q):
    return mp.mpf(str(S.numer(q))) / mp.mpf(str(S.denom(q)))

probabilities=[]
entropies=[]
for parameter in [S.Rational(251,1000),S.Rational(63,250)]:
    gamma=(S.eye(14)+parameter*A).inv()*(parameter*d)
    assert all(v>0 for v in gamma)
    p=gamma/sum(gamma)
    assert sum(p)==1
    probabilities.append([str(v) for v in p])
    entropies.append(-sum(real(v)*mp.log(real(v)) for v in p))
assert entropies[1]-entropies[0] > mp.mpf('0.0001')
def log_bounds(q, terms):
    t=(q-1)/(q+1)
    assert 0 <= t < 1
    lo=2*sum((t**(2*j+1)/Fraction(2*j+1) for j in range(terms)),Fraction(0))
    return lo,lo+2*t**(2*terms+1)/(1-t*t)

lo2,hi2=log_bounds(Fraction(2),12)
assert Fraction(69314718055,10**11) <= lo2 <= hi2 <= Fraction(69314718057,10**11)
expected_bounds=[
 [(-178229885,-178229884),(-178436459,-178436458),(-290218503,-290218501),(-179635882,-179635881),(-877041770,-877041769)],
 [(-177207058,-177207057),(-177634555,-177634554),(-291532324,-291532323),(-180180147,-180180146),(-796635274,-796635273)]]
entropy_bounds=[]
for side in range(2):
    lower=upper=Fraction(0)
    for j,g in enumerate(classes):
        p=Fraction(probabilities[side][g[0]])
        scaled=p; power=0
        while scaled<1:
            scaled*=2;power+=1
        lo,hi=log_bounds(scaled,7)
        lo-=power*hi2;hi-=power*lo2
        e0,e1=expected_bounds[side][j]
        assert Fraction(e0,10**8)<=lo<=hi<=Fraction(e1,10**8)
        lower-=len(g)*p*hi;upper-=len(g)*p*lo
    entropy_bounds.append((lower,upper))
assert entropy_bounds[0][1]<Fraction(2158577,10**6)
assert entropy_bounds[1][0]>Fraction(2158712,10**6)
assert entropy_bounds[1][0]-entropy_bounds[0][1]>Fraction(1,10000)
oriented=[(i,j) for i in range(14) for j in range(14) if A[i,j]]
mean_degree=sum(d[i] for i,j in oriented)/len(oriented)
mean_log=sum(S.log(d[j]) for i,j in oriented)/len(oriented)
cov=sum(d[i]*S.log(d[j]) for i,j in oriented)/len(oriented)-mean_degree*mean_log
expected=(159*S.log(5)-153*S.log(7)-120*S.log(2))/512
assert S.expand_log(cov-expected,force=True).expand()==0
assert cov.evalf(80)<0
print(json.dumps({'python':sys.version,'sympy':S.__version__,'mpmath':mp.__version__,'edges':len(edges),'connected_vertices':len(seen),'ldl_diagonal':[str(D[i,i]) for i in range(14)],'quotient_matrix':str(B),'class_gram_minors':[str(v) for v in minors],'exact_entropy_bounds':[[str(v) for v in bounds] for bounds in entropy_bounds],'resolvent_formulas':[str(f) for f in u],'interval_test':'Exact rational root isolation. No numerator or denominator roots on the interval. Positive left values.','probabilities':probabilities,'entropy_nats':[str(x) for x in entropies],'entropy_gap_nats':str(entropies[1]-entropies[0]),'covariance_nats':str(cov.evalf(70)),'status':'PASS'},indent=2))
