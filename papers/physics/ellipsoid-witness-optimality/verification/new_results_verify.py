#!/usr/bin/env python3
"""Exact symbolic checks for the expanded ellipsoid-witness dossier.

This verifies identities and rational certificates. It is not a numerical
surrogate for universal analytic theorems or a substitute for Lean.
Requires SymPy 1.14 (no SDP solver).
"""
from pathlib import Path
import json
import sympy as s

I2 = s.eye(2)
I4 = s.eye(4)
X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -s.I], [s.I, 0]])
Z = s.diag(1, -1)
sig = [I2, X, Y, Z]
XX, YY, ZZ = [s.kronecker_product(t, t) for t in [X, Y, Z]]
BX = s.kronecker_product(I2, X)
q = s.Rational
checks = []


def check(name, truth):
    ok = bool(truth)
    checks.append({"name": name, "passed": ok})
    if not ok:
        raise AssertionError(name)


def equal(A, B):
    if isinstance(A, s.MatrixBase) or isinstance(B, s.MatrixBase):
        return all(s.simplify(x) == 0 for x in A-B)
    return s.simplify(A-B) == 0


def pt(A):
    return s.Matrix(4, 4, lambda i, j: A[2*(i//2)+j % 2, 2*(j//2)+i % 2])


def J(A):
    return BX * pt(A) * BX


def bell(a, b, c):
    return (I4+a*XX+b*YY+c*ZZ)/4


def proj(v):
    return v*v.conjugate().T / (v.conjugate().T*v)[0]


PhiP = proj(s.Matrix([1, 0, 0, 1]))
PhiM = proj(s.Matrix([1, 0, 0, -1]))
PsiP = proj(s.Matrix([0, 1, 1, 0]))
PsiM = proj(s.Matrix([0, 1, -1, 0]))
bp = [PhiP, PhiM, PsiP, PsiM]


def spectrum_in_bell(A):
    return [s.simplify(s.trace(A*P)) for P in bp]


a, b, c, al = s.symbols("a b c alpha", real=True)
dm = a+b-1
tm = 1-a+b
Wm = bell(a, b, -c)
Wp = bell(a, b, c)
alpha_lo = (dm-c)/(dm+c)
alpha_hi = (tm-c)/(tm+c)

check("bell_basis_resolution", equal(sum(bp, s.zeros(4)), I4))
check("mirror_map_pair", equal(J(Wm), Wp))
check("left_spectrum", spectrum_in_bell(Wm) ==
      [(1+a-b-c)/4, (1-a+b-c)/4, (1+a+b+c)/4, (1-a-b+c)/4])
check("right_spectrum", spectrum_in_bell(Wp) ==
      [(1+a-b+c)/4, (1-a+b+c)/4, (1+a+b-c)/4, (1-a-b-c)/4])
res = Wm-al*Wp
ev = spectrum_in_bell(res)
check("sharp_interval_lower_eigenvalue", equal(ev[3], ((dm+c)*al-(dm-c))/4))
check("sharp_interval_upper_eigenvalue", equal(ev[1], ((tm-c)-(tm+c)*al)/4))
check("sharp_interval_other_phi", equal(ev[0]-ev[1], (a-b)*(1-al)/2))
check("sharp_interval_other_psi", equal(ev[2], ((1+a+b)*(1-al)+c*(1+al))/4))
check("interval_width", equal(alpha_hi-alpha_lo,
      4*c*(1-a)/((tm+c)*(dm+c))))
lower_residual = s.simplify(Wm-alpha_lo*Wp)
lower_expected = (1-alpha_lo)*bell(a, b, -dm)
check("lower_endpoint_remainder", equal(lower_residual, lower_expected))
mix = (1+a+b)/(2*(a+b))
rho = s.simplify(mix*PsiM+(1-mix)*PsiP)
check("universal_separator_trace", equal(s.trace(rho), 1))
check("universal_separator_left", equal(s.trace(Wm*rho), c/4))
check("universal_separator_right", equal(s.trace(Wp*rho), -c/4))

Hm = Wm.subs({a:q(3,4), b:q(3,4), c:q(1,4)})
Hp = Wp.subs({a:q(3,4), b:q(3,4), c:q(1,4)})
P = Hm-Hp/2
check("robust_pair_exact_mirror", equal(J(Hm), Hp))
check("robust_remainder_spectrum", spectrum_in_bell(P) ==
      [q(1,32), q(1,32), q(13,32), q(1,32)])
check("robust_left_negative_eigenvalue", min(Hm.eigenvals()) == -q(1,16))
check("robust_right_negative_eigenvalue", min(Hp.eigenvals()) == -q(3,16))
check("robust_radius_remainder", equal(q(3,2)*q(1,48), q(1,32)))
check("robust_radius_witness_margin", q(1,48) < q(1,16))
check("robust_uniform_BP_margin", equal((1-q(3,4))/4, q(1,16)))

# Every matrix unit is permuted by J, proving Frobenius isometry and involution.
unit_positions = set()
for i in range(4):
    for j in range(4):
        E = s.zeros(4); E[i,j] = 1
        JE = J(E)
        check(f"mirror_involution_{i}_{j}", equal(J(JE), E))
        where = [(u,v) for u in range(4) for v in range(4) if JE[u,v] != 0]
        check(f"mirror_unit_{i}_{j}", len(where) == 1 and JE[where[0]] == 1)
        unit_positions.add(where[0])
check("mirror_matrix_unit_permutation", len(unit_positions) == 16)

# Exact primal/dual certificate for the diagonal mirror family.
# M(Q)=(L tensor id)(Q^Gamma), L is unital diagonal with (a,b,c).
def M(Q):
    A = pt(Q)
    ans = s.zeros(4)
    for i in range(4):
        for j in range(4):
            Sij = s.kronecker_product(sig[i], sig[j])
            coef = s.trace(Sij*A)/4
            ans += coef * [1,a,b,c][i] * Sij
    return s.simplify(ans)

check("map_source_outer", equal(M(PhiP), Wp))
Xdual = 4*PsiM/(dm+c)
dual_slack = s.simplify(I4+M(Xdual))  # Here M is self-adjoint.
check("dual_objective", equal(-s.trace(Xdual*Wm), alpha_lo))
check("dual_slack_phi_plus_kernel", equal(dual_slack*PhiP, s.zeros(4)))
check("dual_slack_spectrum", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(dual_slack),
    [0, 2*(a+b)/(dm+c), 2*(b+c)/(dm+c), 2*(a+c)/(dm+c)])))
check("primal_dual_complementarity", equal(Xdual*lower_residual, s.zeros(4)))

p, qtarget = s.symbols("p q", real=True)
Wpf = bell(1,1,2*p-1)
Wqf = bell(1,1,2*qtarget-1)
Qf = p/qtarget*PhiP
Xf = 2/qtarget*PsiM
MfQ = M(Qf).subs({a:1,b:1,c:2*qtarget-1})
MfX = M(Xf).subs({a:1,b:1,c:2*qtarget-1})
check("Wp_target_primal_image", equal(MfQ,p/qtarget*Wqf))
check("Wp_target_primal_residual", equal(Wpf-MfQ,(1-p/qtarget)*PsiP))
check("Wp_target_dual_objective", equal(-s.trace(Xf*Wpf),p/qtarget))
check("Wp_target_dual_slack", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(I4+MfX),[0,2/qtarget,2,2])))

# Class C spherical witnesses and a positive-chirality geometry counterexample.
r = s.symbols("r", real=True)
Sr = bell(r,r,r)
check("sphere_eigenvalues", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(Sr), [(1+r)/4]*3+[(1-3*r)/4])))
check("sphere_partial_transpose_spectrum", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(pt(Sr)), [(1+3*r)/4]+[(1-r)/4]*3)))
V = Sr.subs(r,q(1,2))
P00 = s.diag(1,0,0,0)
W = (V+P00)/2
check("classC_positive_subtraction", equal(W-V/2,P00/2))
check("classC_V_spectrum", V.eigenvals() == {q(3,8):3,-q(1,8):1})
check("classC_W_spectrum", W.eigenvals() == {q(11,16):1,q(3,16):2,-q(1,16):1})
check("classC_V_PT_PSD", all(x>0 for x in pt(V).eigenvals()))
check("classC_W_PT_PSD", all(x>0 for x in pt(W).eigenvals()))
A = s.Matrix([s.trace(W*s.kronecker_product(t,I2)) for t in [X,Y,Z]])
B = s.Matrix([s.trace(W*s.kronecker_product(I2,t)) for t in [X,Y,Z]])
T = s.Matrix(3,3,lambda i,j:s.trace(W*s.kronecker_product(sig[i+1],sig[j+1])))
delta = 1-(B.T*B)[0]
K = T-A*B.T
centre = s.simplify((A-T*B)/delta)
shape = s.simplify(K*(delta*s.eye(3)+B*B.T)*K.T/delta**2)
check("classC_W_Bloch_A", equal(A,s.Matrix([0,0,q(1,2)])))
check("classC_W_Bloch_B", equal(B,s.Matrix([0,0,q(1,2)])))
check("classC_W_T", equal(T,s.diag(q(1,4),q(1,4),q(3,4))))
check("classC_W_centre", equal(centre,s.Matrix([0,0,q(1,6)])))
check("classC_W_shape", equal(shape,s.diag(q(1,12),q(1,12),q(4,9))))
check("classC_W_chirality_positive", K.det()>0)
north = s.Matrix([0,0,q(5,6)])
check("classC_W_north_on_ellipsoid", equal(((north-centre).T*shape.inv()*(north-centre))[0],1))
check("classC_W_north_outside_V", (north.T*north)[0]>q(1,4))
equator = s.Matrix([q(1,2),0,0])
check("classC_V_equator_outside_W", ((equator-centre).T*shape.inv()*(equator-centre))[0]>1)
sep = q(4,5)*PsiM+q(1,5)*P00
check("classC_separating_state_PSD", all(x>=0 for x in sep.eigenvals()))
check("classC_separating_state_trace", s.trace(sep)==1)
check("classC_separator_V", equal(s.trace(V*sep),-q(1,40)))
check("classC_separator_W", equal(s.trace(W*sep),q(7,80)))

# A strictly interior planar target, rank two but nevertheless witness-admissible.
disk = bell(q(3,4),q(3,4),0)
check("planar_spectrum", disk.eigenvals()=={q(1,4):2,q(5,8):1,-q(1,8):1})
check("planar_PT_spectrum", pt(disk).eigenvals()==disk.eigenvals())
check("planar_shape", equal(s.diag(q(3,4),q(3,4),0)**2,s.diag(q(9,16),q(9,16),0)))

# Algebraic interpolation identity for arbitrarily close finer witnesses.
t, alpha = s.symbols("t alpha", real=True)
k = alpha+(1-alpha)*t
beta = alpha/k
check("path_U_coefficient", equal(beta*((1-t)*alpha+t),alpha))
check("path_P_remainder_coefficient", equal(1-beta*(1-t),t/k))

# Volume reversal is unbounded even for canonical right-handed Class C pairs.
delt = s.symbols("delta", real=True)
Vd = bell(1-delt,delt,delt)
Wd = q(3,4)*Vd+q(1,4)*PhiM
check("volume_family_Bloch", equal(Wd,bell((2-3*delt)/4,(1+3*delt)/4,(1+3*delt)/4)))
check("volume_family_V_eigenvalues", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(Vd),[(2-delt)/4,3*delt/4,(2-delt)/4,-delt/4])))
check("volume_family_W_eigenvalues", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(Wd),[3*(2-delt)/16,(4+9*delt)/16,3*(2-delt)/16,-3*delt/16])))
check("volume_family_V_PT_eigenvalues", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(pt(Vd)),[(2+delt)/4,delt/4,(2-3*delt)/4,delt/4])))
check("volume_family_W_PT_eigenvalues", all(equal(x,y) for x,y in zip(
    spectrum_in_bell(pt(Wd)),[(8+3*delt)/16,(2+3*delt)/16,(4-9*delt)/16,(2+3*delt)/16])))
rd = q(7,8)*PsiM+q(1,8)*PhiM
check("volume_family_separator_V",equal(s.trace(Vd*rd),-delt/8))
check("volume_family_separator_W",equal(s.trace(Wd*rd),(1-3*delt)/32))
volV = (1-delt)*delt**2
volW = (2-3*delt)*(1+3*delt)**2/64
check("volume_family_finite_limit_W",s.limit(volW,delt,0,dir="+")==q(1,32))
check("volume_family_zero_limit_V",s.limit(volV,delt,0,dir="+")==0)
check("volume_family_unbounded_ratio",s.limit(volW/volV,delt,0,dir="+")==s.oo)

# Ordinary partial transpose is not necessarily the finer chirality change.
Ap = bell(q(3,4),-q(3,4),q(1,4))
Bp = pt(Ap)
check("PT_incomparable_exact_pair",equal(Bp,bell(q(3,4),q(3,4),q(1,4))))
check("PT_incomparable_A_Phi_minus",equal(s.trace(Ap*PhiM),-q(1,16)))
check("PT_incomparable_B_Phi_minus",equal(s.trace(Bp*PhiM),q(5,16)))
check("PT_incomparable_A_Psi_minus",equal(s.trace(Ap*PsiM),q(3,16)))
check("PT_incomparable_B_Psi_minus",equal(s.trace(Bp*PsiM),-q(3,16)))
check("PT_incomparable_chiralities",s.diag(q(3,4),-q(3,4),q(1,4)).det()<0 and
      s.diag(q(3,4),q(3,4),q(1,4)).det()>0)
check("PT_incomparable_same_shape",equal(s.diag(q(3,4),-q(3,4),q(1,4))**2,
      s.diag(q(3,4),q(3,4),q(1,4))**2))

result={"engine":"SymPy", "sympy_version":s.__version__,
        "scope":"Exact identities/rational spectra, not general theorem formalization",
        "checks":checks, "total":len(checks),
        "passed":sum(x["passed"] for x in checks),
        "failed":sum(not x["passed"] for x in checks)}
out=Path(__file__).with_name("new_results_verify_output.json")
out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:result[k] for k in ["engine","sympy_version","total","passed","failed"]},indent=2))
