"""Exact certificate for the conjecture-free two-sided-only activation example.

The single-side optimum uses the proved rank-two formula. The state,
bilateral filter, success, and output CHSH value are checked directly.
"""
from pathlib import Path
import json
import sympy as s

R=s.Rational
psi=s.Matrix([0,1,-1,0])/s.sqrt(2)
zero=s.Matrix([1,0,0,0])
def rho(p): return p*psi*psi.T+(1-p)*zero*zero.T
p,e=s.symbols('p e',positive=True)
F=s.diag(e,1)
FF=s.kronecker_product(F,F)
unnormalized=FF*rho(p)*FF
prob=s.trace(unnormalized)
q=p/(p+(1-p)*e**2)
assert s.factor(prob-(p*e**2+(1-p)*e**4))==0
assert (unnormalized/prob-rho(q)).applyfunc(s.factor)==s.zeros(4)
pauli=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
T=s.Matrix(3,3,lambda i,j:s.trace(rho(p)*s.kronecker_product(pauli[i],pauli[j])))
assert T==s.diag(-p,-p,1-2*p)
initial=rho(R(3,5));output=(unnormalized/prob).subs({p:R(3,5),e:R(1,2)})
assert all(x>=0 for x in initial.eigenvals())
assert output==rho(R(6,7))
assert prob.subs({p:R(3,5),e:R(1,2)})==R(7,40)
initial_spectrum=list((T.T*T).subs(p,R(3,5)).eigenvals(multiple=True))
output_spectrum=list((T.T*T).subs(p,R(6,7)).eigenvals(multiple=True))
assert sum(sorted(initial_spectrum)[-2:])==R(18,25)
assert sum(sorted(output_spectrum)[-2:])==R(72,49)>1
guard=2*R(3,5)*(3*R(3,5)-2)
assert guard==R(-6,25)<0
assert max(s.Integer(1),2*R(3,5)/(2-R(3,5)))==1
result={'status':'PASS','arithmetic':'exact rational and symbolic',
        'generic_filtered_parameter':str(q),'generic_success':str(s.factor(prob)),
        'p':'3/5','epsilon':'1/2','initial_chsh_squared':'18/25',
        'unilateral_squared_via_rank_two_theorem':'1',
        'bilateral_chsh_squared':'72/49','success_probability':'7/40',
        'purity_guard':'-6/25'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
