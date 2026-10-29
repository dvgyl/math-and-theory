"""Exact, dependency-free certificate for a five-cycle of two-block ADMM.

Every arithmetic assertion uses Python integers or fractions.Fraction.
This verifies finite algebra and inequalities. It is not a Lean certificate.
The accompanying proof explains why these inequalities imply the full orbit.
"""

# Assertions are part of this certificate.
import os as _assertion_guard_os
if not __debug__ or "PYTHONOPTIMIZE" in _assertion_guard_os.environ:
    raise SystemExit("Verification requires assertions; remove -O/-OO and unset PYTHONOPTIMIZE.")
from fractions import Fraction as Q
import json
from pathlib import Path
from itertools import permutations

TAU=Q(199,100)
Z=[(20,-62,-161,80),(-52,-38,177,31),(-53,38,-126,-129),
   (20,62,26,178),(65,0,84,-160)]
V=[(57,-289,314,-85),(-257,-143,-304,-116),(-216,200,178,273),
   (124,267,16,-325),(292,-35,-204,253)]
K=5

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def mul(t,a):return tuple(t*x for x in a)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sq(a):return dot(a,a)
def rowsum(a):return tuple(sum(row[j] for row in a) for j in range(4))

X=[add(Z[i],sub(V[i],V[(i-1)%K])) for i in range(K)]
U=[mul(TAU,v) for v in V]
A=[sub(sub(Z[(i-1)%K],U[(i-1)%K]),X[i]) for i in range(K)]
B=[sub(add(X[i],U[(i-1)%K]),Z[i]) for i in range(K)]
AN=[mul(100,a) for a in A]
BN=[mul(100,b) for b in B]
assert all(v.denominator==1 for a in AN+BN for v in a)
AN=[tuple(int(v) for v in a) for a in AN]
BN=[tuple(int(v) for v in b) for b in BN]
assert rowsum(X)==rowsum(Z)==rowsum(V)==(0,0,0,0)

MC=[[dot(AN[i],sub(X[i],X[j])) for j in range(K)] for i in range(K)]
MD=[[dot(BN[i],sub(Z[i],Z[j])) for j in range(K)] for i in range(K)]
assert all(M[i][j]>0 for M in [MC,MD] for i in range(K) for j in range(K) if i!=j)
assert min(M[i][j] for M in [MC,MD] for i in range(K) for j in range(K) if i!=j)==136989
assert all(dot(a,x)>0 for a,x in zip(AN,X))
assert all(dot(b,z)>0 for b,z in zip(BN,Z))

# The same orbit for everywhere finite 1/1000-strongly convex objectives.
# f(w) = (||w||^2 + 2 max(0, max_i P_i . (w-X_i)))/2000, and g analogously.
P=[sub(mul(10,AN[i]),X[i]) for i in range(K)]
R=[sub(mul(10,BN[i]),Z[i]) for i in range(K)]
MCstrong=[[dot(P[i],sub(X[i],X[j])) for j in range(K)] for i in range(K)]
MDstrong=[[dot(R[i],sub(Z[i],Z[j])) for j in range(K)] for i in range(K)]
assert all(M[i][j]>0 for M in [MCstrong,MDstrong] for i in range(K) for j in range(K) if i!=j)
assert min(M[i][j] for M in [MCstrong,MDstrong] for i in range(K) for j in range(K) if i!=j)==971440
assert all(dot(p,x)>0 for p,x in zip(P,X))
assert all(dot(r,z)>0 for r,z in zip(R,Z))
strong_origin_margins=[dot(p,x) for p,x in zip(P,X)]+[dot(r,z) for r,z in zip(R,Z)]
assert min(strong_origin_margins)==21708952

def objective(w,pts,normals):
    h=max([Q(0)]+[dot(normals[i],sub(w,pts[i])) for i in range(K)])
    return Q(1,2000)*(sq(w)+2*h)

assert objective((0,0,0,0),X,P)==objective((0,0,0,0),Z,R)==0
for i in range(K):
    assert objective(X[i],X,P)==Q(sq(X[i]),2000)
    assert objective(Z[i],Z,R)==Q(sq(Z[i]),2000)
    assert mul(Q(1,1000),add(X[i],P[i]))==A[i]
    assert mul(Q(1,1000),add(Z[i],R[i]))==B[i]

# Exact identities that hold at every step, with subscripts modulo five.
for i in range(K):
    prev=(i-1)%K
    assert add(X[i],A[i])==sub(Z[prev],U[prev])
    assert add(Z[i],B[i])==add(X[i],U[prev])
    assert U[i]==add(U[prev],mul(TAU,sub(X[i],Z[i])))
assert sq(sub(X[0],Z[0]))==502309
assert all(sq(sub(X[i],Z[i]))>0 for i in range(K))

def det4(M):
    total=0
    for p in permutations(range(4)):
        term=(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        for i in range(4):term*=M[i][p[i]]
        total+=term
    return total

detX=det4([sub(X[i],X[4]) for i in range(4)])
detZ=det4([sub(Z[i],Z[4]) for i in range(4)])
assert detX==395537260080 and detZ==1913707790

# Exact parameter interval for the same two indicator polytopes and state
# vectors z_i=Z_i, u_i=tau*V_i. This is supplementary to tau=199/100.
lower=Q(0);upper=None
for points,sign in [(X,-1),(Z,1)]:
    for i in range(K):
        prev=(i-1)%K
        n0=sub(Z[prev],X[i]) if sign==-1 else sub(X[i],Z[i])
        n1=mul(sign,V[prev])
        for j in range(K):
            if i==j:continue
            delta=sub(points[i],points[j]);c=dot(n0,delta);d=dot(n1,delta)
            if d>0:lower=max(lower,-Q(c,d))
            elif d<0:
                candidate=-Q(c,d)
                upper=candidate if upper is None else min(upper,candidate)
            else:assert c>=0
assert lower<TAU<2 and (upper is None or 2<upper)

data={
    'tau':str(TAU),'dimension':4,'period':5,
    'Z':Z,'V':V,'X':X,'100A':AN,'100B':BN,
    'normal_margin_matrix_times_100_C':MC,
    'normal_margin_matrix_times_100_D':MD,
    'strongly_convex_mu':'1/1000','P':P,'R':R,
    'strong_margin_matrix_times_1000_C':MCstrong,
    'strong_margin_matrix_times_1000_D':MDstrong,
    'strong_origin_margins_times_1000':strong_origin_margins,
    'residual_squared':[sq(sub(X[i],Z[i])) for i in range(K)],
    'affine_determinant_X':detX,'affine_determinant_Z':detZ,
    'same_indicator_polytopes_tau_interval':[str(lower),str(upper) if upper is not None else 'infinity'],
    'status':'Exact rational algebra checked; formal Lean verification tracked separately.'
}
if __name__=='__main__':
    path=Path(__file__).with_name('admm_five_cycle_exact_certificate.json')
    path.write_text(json.dumps(data,indent=2))
    print('PASS: all recurrence identities and all projection certificates checked exactly.')
    print('PASS: everywhere-finite 1/1000-strongly-convex variant checked exactly.')
    print('Minimum indicator normal margin = 136989/100.')
    print('Minimum strongly convex normal margin = 971440/1000.')
    print('First squared primal residual = 502309.')
    print('Same indicator polytopes work for tau >=',lower,'(no upper restriction)' if upper is None else f'and <= {upper}')
    print('Wrote',path)
