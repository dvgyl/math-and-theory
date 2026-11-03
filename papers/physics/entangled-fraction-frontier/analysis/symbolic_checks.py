"""Exact SymPy certificates for the equality representative.

Run: python3 equality/symbolic_checks.py
No floating point is used. The rho_c centre expression is valid for c<1;
the singular endpoint is checked separately under its stated convention.
"""
import json
import sympy as s

c = s.symbols('c', real=True)
t = 1-c
d = 2-c
rho = s.Matrix([[1,0,0,t],[0,c*t,0,0],[0,0,0,0],[t,0,0,t*t]])/d
I = s.eye(2)
pauli = [s.Matrix([[0,1],[1,0]]),
         s.Matrix([[0,-s.I],[s.I,0]]), s.diag(1,-1)]

def reduced_a(m):
    return s.Matrix(2,2,lambda i,j:sum(m[2*i+k,2*j+k] for k in range(2)))

def reduced_b(m):
    return s.Matrix(2,2,lambda i,j:sum(m[2*k+i,2*k+j] for k in range(2)))

def exact_zero(expr):
    if isinstance(expr,s.MatrixBase):
        return all(s.simplify(x)==0 for x in expr)
    return s.simplify(expr)==0

a = s.Matrix([s.trace(rho*s.kronecker_product(p,I)) for p in pauli])
b = s.Matrix([s.trace(rho*s.kronecker_product(I,p)) for p in pauli])
T = s.Matrix(3,3,lambda i,j:s.trace(rho*s.kronecker_product(pauli[i],pauli[j])))
centre = (a-T*b)/(1-(b.T*b)[0])
bell = s.Matrix([1,0,0,1])/s.sqrt(2)
eig1 = (1+t*t)/d
eig2 = c*t/d
z = s.symbols('z')
checks = {
    'trace_one': exact_zero(s.trace(rho)-1),
    'Hermitian': exact_zero(rho-rho.H),
    'a_formula': exact_zero(a-s.Matrix([0,0,c*(3-2*c)/d])),
    'b_formula': exact_zero(b-s.Matrix([0,0,c/d])),
    'T_formula': exact_zero(T-s.diag(2*t/d,-2*t/d,(2-3*c+2*c*c)/d)),
    'centre_formula': exact_zero(centre-s.Matrix([0,0,c])),
    'Bell_overlap': exact_zero((bell.H*rho*bell)[0]-(1-c/2)),
    'characteristic_polynomial': exact_zero(rho.charpoly(z).as_expr()-z*z*(z-eig1)*(z-eig2)),
    'c0_Bell': exact_zero(rho.subs(c,0)-bell*bell.H),
    'c1_product': exact_zero(rho.subs(c,1)-s.diag(1,0,0,0)),
}

# Reparameterize sqrt(1-c) by u to avoid symbolic branch assumptions.
u = s.symbols('u', real=True, nonnegative=True)
cu = 1-u*u
sig = s.Matrix([[1,0,0,u],[0,cu,0,0],[0,0,0,0],[u,0,0,u*u]])/2
Du = s.diag(s.sqrt(2/(1+u*u)),u*s.sqrt(2/(1+u*u)))
psi = s.Matrix([1,0,0,u])/s.sqrt(1+u*u)
filt = s.kronecker_product(I,Du)
checks.update({
    'canonical_B_marginal':exact_zero(reduced_b(sig)-I/2),
    'canonical_A_marginal':exact_zero(reduced_a(sig)-s.diag(1+cu,1-cu)/2),
    'canonical_top_eigenvector':exact_zero(sig*psi-(1-cu/2)*psi),
    'filter_gram':exact_zero(Du.H*Du-2*reduced_b(psi*psi.H)),
    'filter_reconstructs_rho':exact_zero(filt*sig*filt.H-rho.subs(c,cu)),
    'filter_maps_Bell_to_top_eigenvector':exact_zero(filt*bell-psi),
    'canonical_Q':exact_zero(s.diag(u,-u,u*u)**2-s.diag(1-cu,1-cu,(1-cu)**2)),
})

# Joint-envelope family, using b=(1-v^2)/(1+v^2) for 0<=v<=1 to make
# all square-root choices unambiguous algebraic expressions.
v = s.symbols('v', real=True, nonnegative=True)
bv = (1-v*v)/(1+v*v)
Db = s.diag(s.sqrt(2/(1+v*v)),v*s.sqrt(2/(1+v*v)))
Fb = s.kronecker_product(I,Db)
rjoint = Fb*sig*Fb.H
aj = s.Matrix([s.trace(rjoint*s.kronecker_product(p,I)) for p in pauli])
bj = s.Matrix([s.trace(rjoint*s.kronecker_product(I,p)) for p in pauli])
Tj = s.Matrix(3,3,lambda i,j:s.trace(rjoint*s.kronecker_product(pauli[i],pauli[j])))
expected_F = (1+u*v)**2/(2*(1+v*v))
checks.update({
    'joint_trace_one':exact_zero(s.trace(rjoint)-1),
    'joint_a':exact_zero(aj-s.Matrix([0,0,cu+(1-cu)*bv])),
    'joint_b':exact_zero(bj-s.Matrix([0,0,bv])),
    'joint_T':exact_zero(Tj-s.diag(2*u*v/(1+v*v),-2*u*v/(1+v*v),1-cu+cu*bv)),
    'joint_centre':exact_zero((aj-Tj*bj)/(1-(bj.T*bj)[0])-s.Matrix([0,0,cu])),
    'joint_Bell_overlap':exact_zero((bell.H*rjoint*bell)[0]-expected_F),
    'joint_deficit_square':exact_zero(1-cu/2-expected_F-(v-u)**2/(2*(1+v*v))),
    'joint_singular_limit_pure_product':exact_zero(rjoint.subs(v,0)-s.diag(1,0,0,0)),
})

print(json.dumps({'checks':checks,'passed':sum(checks.values()),'total':len(checks)},indent=2))
assert all(checks.values())
