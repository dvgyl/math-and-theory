#!/usr/bin/env python3
"""Exact countercertificates to prescribed zero-pure adaptive deletion.

All decisive calculations use Python integers and fractions. Floating point
is used only for descriptive decimal output. No optimizer or external
numerical library is required to verify this certificate.
"""
from fractions import Fraction as Q
from math import factorial
from itertools import permutations, product
from collections import defaultdict
import json


class Interval:
    def __init__(self,lo,hi=None):
        self.lo=Q(lo);self.hi=Q(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,other):
        other=as_interval(other);return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,other):return self+(-as_interval(other))
    def __rsub__(self,other):return as_interval(other)+(-self)
    def __mul__(self,other):
        other=as_interval(other);v=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(min(v),max(v))
    __rmul__=__mul__
    def __pow__(self,k):
        assert self.lo>0 or k>=0
        if k==0:return Interval(1)
        if k<0:return Interval(1/self.hi,1/self.lo)**(-k)
        if self.lo>=0:return Interval(self.lo**k,self.hi**k)
        if k%2:return Interval(self.lo**k,self.hi**k)
        return Interval(0 if self.lo<=0<=self.hi else min(self.lo**k,self.hi**k),max(self.lo**k,self.hi**k))
    def text(self):return [str(self.lo),str(self.hi)]
    def decimals(self):return [float(self.lo),float(self.hi)]


def as_interval(x):return x if isinstance(x,Interval) else Interval(x)


def polynomial(M):
    n=len(M);p={(0,)*n:1}
    for row in M:
        q=defaultdict(int)
        for a,c in p.items():
            for j,v in enumerate(row):
                if not v:continue
                b=list(a);b[j]+=1;q[tuple(b)]+=c*v
        p=dict(q)
    return p


def norm(p):
    return sum(c*c*factorial(a[0])*factorial(a[1])*factorial(a[2])*factorial(a[3]) for a,c in p.items())


def deletion(p):return {a[1:]:v for a,v in p.items() if a[0]==1}


def fock_bound(q,X):
    return sum((factorial(a[0])*factorial(a[1])*factorial(a[2])*v*v)*
               (X[0]**(2*a[0]-2))*(X[1]**(2*a[1]-2)) for a,v in q.items())


def equations(q,X):
    return [sum((a[i]-1)*v*(X[0]**a[0])*(X[1]**a[1]) for a,v in q.items()) for i in range(2)]


def jacobian(q,X):
    return [[sum((a[i]-1)*a[j]*v*(X[0]**(a[0]-(j==0)))*(X[1]**(a[1]-(j==1)))
                 for a,v in q.items() if a[j]) for j in range(2)] for i in range(2)]


def matrix_product(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]


def permanent(A):return sum(__import__('functools').reduce(lambda a,b:a*b,(A[i][j] for i,j in enumerate(s)),1) for s in permutations(range(len(A))))


def check_ds(M,k):
    assert all(sum(row)==k for row in M)
    assert all(sum(col)==k for col in zip(*M))
    assert min(map(min,M))>=0


def base_certificate():
    M=[[0,0,5,3],[3,0,0,5],[2,3,3,0],[3,5,0,0]];check_ds(M,8)
    p=polynomial(M);N=norm(p);q=deletion(p)
    assert N==2276500
    assert q=={(2,1,0):225,(1,2,0):225,(1,1,1):610,(0,2,1):225,
               (2,0,1):135,(1,0,2):285,(0,1,2):135}
    f=lambda t:19*t**4+9*t**3-15*t-15
    lo=Q(1021945,10**6);hi=Q(1021946,10**6)
    assert f(lo)<0<f(hi)
    # Descartes' rule gives exactly one positive root. Capacity balance is
    # verified algebraically in the accompanying note, with D=(t,1,t^2).
    T=Interval(lo,hi)
    H=101250*T**(-4)+202500*T**(-2)+372100+72900*T**2+162450*T**4
    threshold=Q(27,64)*N
    assert H.hi<threshold
    assert H.lo>911200  # Capacity balancing can increase this deletion norm.
    return {'matrix_numerator':M,'matrix_denominator':8,'fock_norm_raw':N,
            'deletion_coefficients':[[list(a),v] for a,v in sorted(q.items())],
            'capacity_parameter_polynomial_coefficients_descending':[19,9,0,-15,-15],
            'capacity_parameter_interval':[str(lo),str(hi)],
            'root_polynomial_endpoint_values':[str(f(lo)),str(f(hi))],
            'scaled_deletion_fock_interval':H.text(),'scaled_deletion_fock_decimals':H.decimals(),
            'threshold':str(threshold),'ratio_interval':[float(H.lo/threshold),float(H.hi/threshold)],
            'unscaled_deletion_fock_norm':911200}


def unique_zero_certificate():
    # A_epsilon=(99/100) A+(1/100) B, where B_11=0,
    # B_1j=B_j1=1/3 and B_ij=2/9 for i,j>1.
    M=[[0,24,4479,2697],[2697,16,16,4471],
       [1806,2689,2689,16],[2697,4471,16,16]]
    check_ds(M,7200)
    assert sum(v==0 for row in M for v in row)==1 and M[0][0]==0
    p=polynomial(M);N=norm(p);q=deletion(p)
    assert p.get((4,0,0,0),0)==0
    assert all(p.get(tuple(4 if i==j else 0 for i in range(4)),0)>0 for j in range(1,4))
    assert len(q)==10 and min(q.values())>0
    center=[Q(979,1000),Q(1917,2000)]
    radius=[Q(1,10000),Q(1,10000)]
    X=[Interval(c-r,c+r) for c,r in zip(center,radius)]
    J0=jacobian(q,center);F0=equations(q,center)
    det=J0[0][0]*J0[1][1]-J0[0][1]*J0[1][0]
    assert det!=0
    R=[[J0[1][1]/det,-J0[0][1]/det],[-J0[1][0]/det,J0[0][0]/det]]
    JX=jacobian(q,X)
    E=[[Q(i==j)-sum(R[i][k]*JX[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    K=[]
    for i in range(2):
        shift=center[i]-sum(R[i][j]*F0[j] for j in range(2))
        bound=Interval(shift)+sum(E[i][j]*Interval(-radius[j],radius[j]) for j in range(2))
        assert X[i].lo<bound.lo<=bound.hi<X[i].hi
        K.append(bound)
    # The map x -> x-RF(x) carries X into its interior by this interval bound.
    # Brouwer gives a zero of F in X; R is invertible. Log-capacity is convex,
    # so this positive stationary point is its global minimizer. Full support
    # ensures uniqueness modulo common scaling.
    H=fock_bound(q,X);threshold=Q(27,64)*N
    assert H.hi<threshold
    c=Q(3,32);P=p[(1,1,1,1)]
    MT=[list(col) for col in zip(*M)]
    GR=permanent(matrix_product(M,MT));GC=permanent(matrix_product(MT,M));SQ=permanent(matrix_product(M,M))
    assert GR==N
    strong_row_gap=P*P-c*GR;strong_col_gap=P*P-c*GC
    gyires_gap=4*P*P-c*(GR+GC+2*SQ)
    assert strong_row_gap>0 and strong_col_gap>0 and gyires_gap>0
    return {'matrix_numerator':M,'matrix_denominator':7200,'mixture_epsilon':'1/100',
            'unique_zero_matrix_entry':[0,0],'unique_zero_pure_coordinate':0,
            'fock_norm_raw':N,'central_coefficient_raw':P,
            'deletion_coefficients':[[list(a),v] for a,v in sorted(q.items())],
            'capacity_gauge':'D=(y,z,1)',
            'capacity_box':[i.text() for i in X],
            'krawczyk_image_box':[i.text() for i in K],
            'krawczyk_image_decimals':[i.decimals() for i in K],
            'scaled_deletion_fock_interval':H.text(),'scaled_deletion_fock_decimals':H.decimals(),
            'threshold':str(threshold),'ratio_interval':[float(H.lo/threshold),float(H.hi/threshold)],
            'row_strong_gap_raw':str(strong_row_gap),'column_strong_gap_raw':str(strong_col_gap),
            'original_gyires_gap_raw':str(gyires_gap)}


def main():
    out={'status':'exact rational certificates; interval existence justified by self-map/Brouwer and log-capacity convexity',
         'base':base_certificate(),'unique_zero':unique_zero_certificate()}
    with open('round4_zero_pure_certificate.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps({'base_ratio_interval':out['base']['ratio_interval'],
                      'unique_zero_ratio_interval':out['unique_zero']['ratio_interval'],
                      'unique_zero_capacity_image':out['unique_zero']['krawczyk_image_decimals'],
                      'original_gyires_still_holds':True},indent=2))

if __name__=='__main__':main()
