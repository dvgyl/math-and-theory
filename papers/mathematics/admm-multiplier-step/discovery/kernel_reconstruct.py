"""Exact reconstruction using the two-dimensional constant-history kernel.

Only interpolation multipliers require a linear solve.  P is projected onto
the exact required column sums, and T is reconstructed through a right inverse
of the consecutive-difference matrix.  This avoids eliminating thousands of
irrelevant matrix variables.  Acceptance remains exact, including LDL pivots.
"""
import argparse
import json
from pathlib import Path
import sys
import sympy as sp
from fast_reconstruct import exact_matrices, rational_ldl, encode_matrix


def constant_columns(snapshots):
    return sp.Matrix(2*snapshots,2,lambda i,j: int(i%2==j))


def prefix_rows(W,m):
    return sp.Matrix(2*m,2,lambda i,j:sum(W[2*k+i%2,j] for k in range(i//2+1)))


def reconstruct(source,output,denominator,zero_threshold):
    raw=json.loads(Path(source).read_text());m=raw['memory'];n=2*(m+1)
    taus=list(dict.fromkeys(sp.Rational(str(t)) for t in raw['interval']))
    datasets=[exact_matrices(t,m) for t in taus]
    data=datasets[0][0]
    J=constant_columns(m+1);C=constant_columns(m)
    B=sp.Matrix(n,2*m,lambda i,j:int(bool(j%2==i%2 and j//2<i//2)))
    # Exact homogeneous constraints ensuring flow cancellation, M J=0,
    # and compatibility of the symmetric potential's prescribed column sums.
    columns=[]
    for k,r in enumerate(data):
        col=list(r['F'])
        for dataset in datasets:
            W=dataset[0][k]['Q']*J
            H=J.T*W;R=prefix_rows(W,m);G=C.T*R
            col.extend([H[0,0],H[0,1],H[1,1],G[0,1]-G[1,0]])
        columns.append(col)
    active=sorted((i for i,x in enumerate(raw['multipliers']) if x>zero_threshold),
                  key=lambda i:-raw['multipliers'][i])
    A=sp.Matrix.hstack(*(sp.Matrix(columns[i]) for i in active))
    red,pivots=A.rref()
    free=[j for j in range(len(active)) if j not in pivots]
    values=[sp.Rational(0)]*len(active)
    for j in free:
        values[j]=sp.Rational(round(raw['multipliers'][active[j]]*denominator),denominator)
    for row,j in enumerate(pivots):
        values[j]=-sum(red[row,k]*values[k] for k in free)
    assert A*sp.Matrix(values)==sp.zeros(A.rows,1)
    if min(values)<0:
        raise ValueError('negative reconstructed multiplier '+str(min(values)))
    lam=[sp.Rational(0)]*len(data)
    for i,v in zip(active,values):lam[i]=v
    result=dict(source=str(source),memory=m,interval=list(map(str,taus)),
        reconstruction='constant-history-kernel projection',
        rounding_denominator=denominator,zero_selection_threshold=zero_threshold,
        multiplier_affine_rank=len(pivots),active_multiplier_count=len(active),
        multipliers=list(map(str,lam)),
        interpolation_indices=[{k:r[k] for k in ('name','i','j')} for r in data],
        endpoints=[],pure_quadratic=True)
    print(f'Exact multiplier reconstruction: {len(active)} active, rank {len(pivots)}',flush=True)
    for e,(tau,dataset) in enumerate(zip(taus,datasets)):
        data,S0,S1,D,diss,coerc=dataset
        Q=sum((lam[i]*r['Q'] for i,r in enumerate(data) if lam[i]),sp.zeros(n))
        W=Q*J;R=prefix_rows(W,m)
        assert J.T*W==sp.zeros(2)
        assert C.T*R==R.T*C
        floating_P=raw['P'][e]
        P0=sp.Matrix(2*m,2*m,lambda i,j:sp.Rational(
            round((floating_P[int(i)][int(j)]+floating_P[int(j)][int(i)])*denominator/2),
            denominator))
        assert P0==P0.T
        delta=R-P0*C
        P=P0+(delta*C.T+C*delta.T)/m-C*(C.T*delta)*C.T/(m*m)
        assert P*C==R
        M=S0.T*P*S0-S1.T*P*S1-diss-Q
        assert M*J==sp.zeros(n,2)
        assert D*B==sp.eye(2*m)
        T=B.T*M*B
        assert M==D.T*T*D
        lower=P-coerc[:2*m,:2*m]
        print(f'Checking exact endpoint {tau}',flush=True)
        TL,Td=rational_ldl(T);PL,Pd=rational_ldl(lower)
        result['endpoints'].append(dict(tau=str(tau),P=encode_matrix(P),T=encode_matrix(T),
            lower=encode_matrix(lower),T_LDL_L=encode_matrix(TL),T_LDL_D=list(map(str,Td)),
            lower_LDL_L=encode_matrix(PL),lower_LDL_D=list(map(str,Pd)),
            minimum_T_pivot_float=min(map(float,Td)),
            minimum_lower_pivot_float=min(map(float,Pd))))
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print('EXACT CERTIFICATE ACCEPTED: affine identities, nonnegative multipliers, positive LDL pivots',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output')
    p.add_argument('--denominator',type=int,default=10000)
    p.add_argument('--zero-threshold',type=float,default=.001)
    a=p.parse_args();reconstruct(a.input,a.output,a.denominator,a.zero_threshold)
