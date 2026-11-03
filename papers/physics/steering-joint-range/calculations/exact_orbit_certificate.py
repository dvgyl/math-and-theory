#!/usr/bin/env python3
"""Exact rational certificates for the complete filtering-orbit maximum.

Input fields: c (3 entries), S (3x3), x (3 entries), lambda. Entries must be
integers or rational strings; floating-point inputs are rejected. The
certificate is checked by all physical principal minors and the complete
PSD-shift/stationarity/ball/complementarity conditions. It works for singular
and indefinite K. No numerical optimizer or inverse is used.
"""
import argparse,itertools,json
from pathlib import Path
import sympy as s

def rational(x):
    if isinstance(x,bool) or isinstance(x,float): raise ValueError('Use exact integers or rational strings')
    q=s.Rational(x)
    if not q.is_Rational: raise ValueError('Rational data required')
    return q

def principal_minors(A):
    vals=[]
    for size in range(1,A.rows+1):
        for inds in itertools.combinations(range(A.rows),size):
            q=s.simplify(A.extract(inds,inds).det())
            if q.is_real is not True or q<0: raise ValueError(f'Negative/nonreal principal minor {inds}: {q}')
            vals.append({'indices':list(inds),'determinant':str(q)})
    return vals

def check(data):
    c=s.Matrix([rational(v) for v in data['c']]); S=s.Matrix([[rational(v) for v in row] for row in data['S']])
    x=s.Matrix([rational(v) for v in data['x']]); lam=rational(data['lambda'])
    if c.shape!=(3,1) or S.shape!=(3,3) or x.shape!=(3,1): raise ValueError('Wrong input dimensions')
    pauli=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
    M=s.eye(4)
    for i in range(3):
        M+=c[i]*s.kronecker_product(pauli[i],s.eye(2))
        for j in range(3):M+=S[i,j]*s.kronecker_product(pauli[i],pauli[j])
    M/=4
    assert M==M.conjugate().T and s.trace(M)==1
    mmin=principal_minors(M)
    tau=s.trace(S.T*S); K=(tau-(c.T*c)[0])*s.eye(3)-S.T*S; k=S.T*c
    B=K+lam*s.eye(3); bmin=principal_minors(B)
    norm2=(x.T*x)[0]
    if lam<0 or norm2>1: raise ValueError('Infeasible shift or ball point')
    if B*x!=k: raise ValueError('Stationarity equation fails')
    if lam*(1-norm2)!=0: raise ValueError('Complementarity fails')
    value=tau+2*(k.T*x)[0]-(x.T*K*x)[0]
    certificate_value=tau+lam+(k.T*x)[0]
    assert value==certificate_value
    return {'name':data.get('name','input'),'status':'PASS','input':data,
      'state_rank':M.rank(),'tau':str(tau),'K':[[str(q) for q in row] for row in K.tolist()],
      'shifted_rank':B.rank(),'shifted_nullity':3-B.rank(),'x_norm_squared':str(norm2),
      'maximum_F3_squared':str(value),'violates':bool(value>1),
      'physical_principal_minors':mmin,'shifted_principal_minors':bmin,
      'stationarity':['0','0','0'],'complementarity':'0',
      'global_gap_identity':'f(x)-f(y)=(y-x)^T(K+lambda I)(y-x)+lambda(1-|y|^2)'}

EXAMPLES=[
 {'name':'counterexample_to_unconstrained_vertex','c':[0,0,'3/10'],'S':[['3/10',0,0],[0,'-1/5',0],[0,0,'3/5']],
  'x':[0,0,1],'lambda':'7/50'},
 {'name':'isotropic_hard_case_product_input','c':[0,0,'1/2'],'S':[[0,0,0],[0,0,0],[0,0,0]],
  'x':[0,0,1],'lambda':'1/4'},
 {'name':'two_pure_contacts_nonattained_invertible_orbit','c':[0,0,'4/5'],'S':[['3/5',0,0],[0,0,0],[0,0,0]],
  'x':[1,0,0],'lambda':'16/25'},
 {'name':'singular_PSD_flat_interior_maximizers','c':[0,0,0],'S':[['1/2',0,0],[0,0,0],[0,0,0]],
  'x':[0,0,0],'lambda':0},
 {'name':'rank_two_hidden_violation','c':[0,0,'16/25'],'S':[['3/5',0,0],[0,'-3/5',0],[0,0,'9/25']],
  'x':[0,0,'72/97'],'lambda':0},
 {'name':'maximally_mixed','c':[0,0,0],'S':[[0,0,0],[0,0,0],[0,0,0]],
  'x':[0,0,0],'lambda':0},
]

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('input',nargs='?',type=Path)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('exact_orbit_certificates.json'))
    args=ap.parse_args()
    inputs=json.loads(args.input.read_text()) if args.input else EXAMPLES
    if isinstance(inputs,dict):inputs=[inputs]
    results=[check(d) for d in inputs]
    args.output.write_text(json.dumps({'status':'PASS','arithmetic':'exact rational SymPy','certificates':results},indent=2)+'\n')
    for r in results:print(r['name'],r['maximum_F3_squared'],'rank',r['state_rank'],'shift nullity',r['shifted_nullity'])
