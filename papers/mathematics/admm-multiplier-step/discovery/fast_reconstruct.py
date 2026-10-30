"""Exact rational reconstruction of the robust finite-window ADMM certificate.

The input SDP data are only a locator. Acceptance requires exact affine
identities, nonnegative interpolation multipliers, and positive rational LDL
pivots for both dissipation and coercivity. No tolerance accepts a certificate.
"""
import argparse
from pathlib import Path
import json
import sys
import sympy as sp


def symouter(a, b):
    return (a.T * b + b.T * a) / 2


def exact_matrices(tau, m):
    dim = 2 * (m + 1)
    E = sp.eye(dim)
    Z = [E[2*j, :] for j in range(m+1)]
    V = [E[2*j+1, :] for j in range(m+1)]
    zero = sp.zeros(1, dim)
    X = [zero] + [Z[j]+V[j]-V[j-1] for j in range(1,m+1)]
    A = [zero] + [Z[j-1]-tau*V[j-1]-X[j] for j in range(1,m+1)]
    B = [zero] + [X[j]+tau*V[j-1]-Z[j] for j in range(1,m+1)]
    fv = sp.eye(2*m)
    fzero = sp.zeros(1,2*m)
    data = []
    for name, points, grads, values in (
        ('f',X,A,[fzero]+[fv[j,:] for j in range(m)]),
        ('g',[zero]+Z[1:],B,[fzero]+[fv[m+j,:] for j in range(m)])):
        for i in range(m+1):
            for j in range(m+1):
                if i != j:
                    data.append(dict(name=name,i=i,j=j,
                        Q=-symouter(grads[i],points[j]-points[i]),
                        F=values[j]-values[i]))
    S0, S1 = E[:2*m,:], E[2:,:]
    D = E[2:,:]-E[:-2,:]
    diss = symouter(Z[m]-Z[m-1], Z[m]-Z[m-1]) + symouter(V[m]-V[m-1], V[m]-V[m-1])
    coerc = symouter(Z[m-1],Z[m-1])+symouter(V[m-1],V[m-1])
    return data,S0,S1,D,diss,coerc


def symmetric_unknowns(n, name):
    upper = [(i,j) for i in range(n) for j in range(i,n)]
    variables = sp.symbols(f'{name}0:{len(upper)}')
    M = sp.zeros(n)
    for (i,j),var in zip(upper, variables):
        M[i,j] = M[j,i] = var
    return M,list(variables),upper


def rational_ldl(M):
    assert M == M.T
    n = M.rows
    L = sp.eye(n)
    d = []
    for j in range(n):
        pivot = sp.cancel(M[j,j]-sum(L[j,k]**2*d[k] for k in range(j)))
        if not pivot > 0:
            raise ValueError(f'nonpositive LDL pivot at {j}: {pivot}')
        d.append(pivot)
        for i in range(j+1,n):
            L[i,j] = sp.cancel((M[i,j]-sum(L[i,k]*L[j,k]*d[k] for k in range(j)))/pivot)
    assert M == L*sp.diag(*d)*L.T
    return L,d


def encode_matrix(M):
    return [[str(M[i,j]) for j in range(M.cols)] for i in range(M.rows)]


def reconstruct(input_path, output_path, denominator, zero_threshold):
    raw = json.loads(Path(input_path).read_text())
    m = raw['memory']
    endpoints = [sp.Rational(str(x)) for x in raw['interval']]
    if endpoints[0] == endpoints[1]:
        endpoints = endpoints[:1]
    data0,*_ = exact_matrices(endpoints[0],m)
    lam = list(sp.symbols(f'lam0:{len(data0)}'))
    variables = []
    approximate = []
    Ps,Ts = [],[]
    equations = []
    for e,tau in enumerate(endpoints):
        P,pvars,upper = symmetric_unknowns(2*m,f'p{e}_')
        T,tvars,_ = symmetric_unknowns(2*m,f't{e}_')
        Ps.append(P);Ts.append(T)
        variables.extend(pvars+tvars)
        approximate.extend([raw['P'][e][i][j] for i,j in upper])
        approximate.extend([raw['T'][e][i][j] for i,j in upper])
        data,S0,S1,D,diss,coerc = exact_matrices(tau,m)
        Q = sum((lam[i]*r['Q'] for i,r in enumerate(data)),sp.zeros(2*(m+1)))
        diff = S0.T*P*S0-S1.T*P*S1-diss-Q-D.T*T*D
        equations.extend(diff[i,j] for i in range(diff.rows) for j in range(i,diff.cols))
    variables.extend(lam)
    approximate.extend(raw['multipliers'])
    flow = sum((lam[i]*r['F'] for i,r in enumerate(data0)),sp.zeros(1,2*m))
    equations.extend(flow)
    zero_indices = [i for i,x in enumerate(raw['multipliers']) if abs(x)<zero_threshold]
    equations.extend(lam[i] for i in zero_indices)
    mat,rhs = sp.linear_eq_to_matrix(equations,variables)
    print(f'Exact elimination: {mat.rows} equations, {mat.cols} variables', flush=True)
    reduced,pivots = mat.row_join(rhs).rref()
    print(f'Exact affine rank: {len(pivots)}', flush=True)
    if len(variables) in pivots:
        raise ValueError('exact affine constraints inconsistent after zero selection')
    free = [i for i in range(len(variables)) if i not in pivots]
    x = [sp.Rational(0)]*len(variables)
    for j in free:
        x[j] = sp.Rational(round(approximate[j]*denominator),denominator)
    for row,j in enumerate(pivots):
        x[j] = reduced[row,-1]-sum(reduced[row,k]*x[k] for k in free)
    assert mat*sp.Matrix(x) == rhs
    substitution = dict(zip(variables,x))
    exact_lam = [substitution[v] for v in lam]
    if min(exact_lam)<0:
        raise ValueError('negative exact multiplier: '+str(min(exact_lam)))
    result = dict(source=str(input_path),memory=m,
        interval=[str(x) for x in endpoints],rounding_denominator=denominator,
        zero_selection_threshold=zero_threshold,
        exact_affine_rank=len(pivots),number_variables=len(variables),
        multipliers=[str(x) for x in exact_lam],
        interpolation_indices=[{k:r[k] for k in ('name','i','j')} for r in data0],
        endpoints=[],pure_quadratic=True)
    for e,tau in enumerate(endpoints):
        P = Ps[e].xreplace(substitution)
        T = Ts[e].xreplace(substitution)
        data,S0,S1,D,diss,coerc = exact_matrices(tau,m)
        Q = sum((exact_lam[i]*r['Q'] for i,r in enumerate(data)),sp.zeros(2*(m+1)))
        assert S0.T*P*S0-S1.T*P*S1-diss-Q == D.T*T*D
        lower = P-coerc[:2*m,:2*m]
        print(f'Checking exact endpoint {tau}', flush=True)
        TL,Td = rational_ldl(T)
        PL,Pd = rational_ldl(lower)
        result['endpoints'].append(dict(tau=str(tau),P=encode_matrix(P),T=encode_matrix(T),
            lower=encode_matrix(lower),T_LDL_L=encode_matrix(TL),T_LDL_D=list(map(str,Td)),
            lower_LDL_L=encode_matrix(PL),lower_LDL_D=list(map(str,Pd)),
            minimum_T_pivot_float=min(map(float,Td)),
            minimum_lower_pivot_float=min(map(float,Pd))))
    Path(output_path).write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ('multipliers','interpolation_indices','endpoints')},indent=2))
    print('EXACT CERTIFICATE ACCEPTED: affine identities, nonnegative multipliers, positive LDL pivots')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('input');p.add_argument('output')
    p.add_argument('--denominator',type=int,default=10000)
    p.add_argument('--zero-threshold',type=float,default=.0001)
    a=p.parse_args()
    reconstruct(a.input,a.output,a.denominator,a.zero_threshold)
