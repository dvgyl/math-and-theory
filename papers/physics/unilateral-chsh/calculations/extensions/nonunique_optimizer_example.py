#!/usr/bin/env python3
"""Exact SymPy certificate for a circle of optimal unilateral CHSH effects."""
import json
from pathlib import Path
import sympy as sp

R = sp.Rational
I = sp.I
pauli = [sp.Matrix([[0,1],[1,0]]), sp.Matrix([[0,-I],[I,0]]), sp.diag(1,-1)]
rho = sp.Matrix([
    [R(7,16), R(9,80), 0, R(3,10)],
    [R(9,80), R(1,16), -R(1,30), 0],
    [0, -R(1,30), R(1,16), R(9,80)],
    [R(3,10), 0, R(9,80), R(7,16)],
])
U = sp.Matrix([[1,0,1,0],[0,1,0,1],[0,1,0,-1],[1,0,-1,0]])/sp.sqrt(2)
block = sp.simplify(U.T*rho*U)
expected = sp.diag(
    sp.Matrix([[R(59,80),R(9,80)],[R(9,80),R(7,240)]]),
    sp.Matrix([[R(11,80),R(9,80)],[R(9,80),R(23,240)]]),
)
assert U.T*U == sp.eye(4)
assert block == expected
assert rho == rho.H and sp.trace(rho) == 1
block_determinants = [block[:2,:2].det(), block[2:,2:].det()]
assert block_determinants == [R(17,1920),R(1,1920)]
assert block[0,0] > 0 and block[2,2] > 0
c = sp.Matrix([(rho*sp.kronecker_product(sp.eye(2),p)).trace() for p in pauli])
a = sp.Matrix([(rho*sp.kronecker_product(p,sp.eye(2))).trace() for p in pauli])
D = sp.Matrix(3,3,lambda i,j:(rho*sp.kronecker_product(pauli[i],pauli[j])).trace())
assert a == sp.zeros(3,1)
assert c == sp.Matrix([R(9,20),0,0])
assert D == sp.diag(R(8,15),-R(2,3),R(3,4))
A = D*D.T
s = (c.T*c)[0]
alpha = sp.trace(A)-s
K = A-s*sp.eye(3)
d = D*c
C = sp.Matrix([[0,-d[2],d[1]],[d[2],0,-d[0]],[-d[1],d[0],0]])
L = K+C*K.inv()*C
r = R(59,720)
assert K == sp.diag(r,R(871,3600),R(9,25))
assert L == sp.diag(r,r,R(531,4355))
assert L[2,2] > r > 0
assert alpha == R(49,45)
assert alpha-r == R(145,144)
x,y = sp.symbols('x y',real=True)
n = sp.Matrix([x,y,0])
v = -K.inv()*C*n
u = -n.cross(v)
assert v == sp.Matrix([0,0,-R(2,3)*y])
assert u == sp.Matrix([R(2,3)*y*y,-R(2,3)*x*y,0])
assert L*n == r*n
assert (n.T*v)[0] == 0
energy = alpha-(n.T*K*n)[0]-(v.T*K*v)[0]-2*(v.T*C*n)[0]
constraint = x*x+y*y-1
assert sp.expand(energy-(alpha-r)+r*constraint) == 0
circle = (u[0]-R(1,3))**2+u[1]**2-R(1,9)
assert sp.expand(circle-R(4,9)*y*y*constraint) == 0
report = {
    'status':'PASS',
    'arithmetic':'Exact rational and symbolic arithmetic; no floating point',
    'density_matrix_trace':str(sp.trace(rho)),
    'positive_block_determinants':list(map(str,block_determinants)),
    'alpha':str(alpha),
    'K_diagonal':[str(K[i,i]) for i in range(3)],
    'schur_diagonal':[str(L[i,i]) for i in range(3)],
    'optimal_normalized_chsh_squared':str(alpha-r),
    'optimal_effect_circle':'(u_1-1/3)^2+u_2^2=1/9, u_3=0',
    'family':'u=(2*y^2/3,-2*x*y/3,0), x^2+y^2=1',
    'max_effect_norm':'2/3',
}
print(json.dumps(report,indent=2))
if __name__ == '__main__':
    Path(__file__).with_name('nonunique_optimizer_example.json').write_text(json.dumps(report,indent=2)+'\n')
