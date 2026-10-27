#!/usr/bin/env python3
"""Exact independent polynomial/identity checker; no Lean claim.
Generator: subset DP and forward shears. Checker: permutation enumeration,
autocorrelation grouping, dense inverse binomial transforms, direct coverage.
"""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

import collections,itertools,json,math,sys,time
from pathlib import Path

def mul(p,q):
    out=collections.defaultdict(int)
    for x,a in p.items():
        for y,b in q.items():out[x+y]+=a*b
    return dict(out)

def independent_defect(n):
    bits=(2*n).bit_length();u=[1<<(bits*i) for i in range(n)]
    p=collections.Counter();folded=collections.Counter()
    for perm in itertools.permutations(range(n)):
        ds=[(perm[i]-i)%n for i in range(n)]
        p[sum(u[j] for j in ds)]+=1
        folded[tuple(ds.count(j)+(ds.count(n-j) if j and 2*j!=n else 0) for j in range(n//2+1))]+=1
    gram_entries=[dict(collections.Counter(u[i]+u[(i+j)%n] for i in range(n))) for j in range(n//2+1)]
    trie={}
    for sig,c in folded.items():
        node=trie
        for j in (j for j,count in enumerate(sig) for _ in range(count)):node=node.setdefault(j,{})
        node['c']=c
    gram=collections.defaultdict(int)
    def visit(node,poly):
        if 'c' in node:
            for k,v in poly.items():gram[k]+=node['c']*v
        for j,child in node.items():
            if j!='c':visit(child,mul(poly,gram_entries[j]))
    visit(trie,{0:1});sq=mul(p,p);fac=math.factorial(n)
    result={k:n**n*sq.get(k,0)-fac*gram.get(k,0) for k in set(sq)|set(gram)}
    return {k:v for k,v in result.items() if v},u,bits

def reencode(poly,old_u,old_base,new_u):
    return {sum((key//r%old_base)*new_u[i] for i,r in enumerate(old_u)):v for key,v in poly.items()}

def inverse_gap_transform(poly,n,u,bits):
    mask=(1<<bits)-1
    for j in range(1,n):
        groups={}
        for key,v in poly.items():
            e=key//u[j]&mask;f=key//u[j-1]&mask
            group=(key-e*u[j]-f*u[j-1],e+f)
            if group not in groups:groups[group]=[0]*(e+f+1)
            groups[group][e]=v
        out={}
        for (rest,t),a in groups.items():
            for h in range(t+1):
                v=sum(a[e]*math.comb(e,h)*(-1)**(e-h) for e in range(h,t+1))
                if v:out[rest+h*u[j]+(t-h)*u[j-1]]=v
        poly=out
    return poly

def permanent_integer(a):
    n=len(a);value=0
    for mask in range(1,1<<n):
        term=math.prod(sum(a[i][j] for j in range(n) if mask>>j&1) for i in range(n))
        value+=(-1)**(n-mask.bit_count())*term
    return value

def evaluate(poly,w,u,bits):
    return sum(c*math.prod(w[j]**(key//u[j]&((1<<bits)-1)) for j in range(len(w))) for key,c in poly.items())

def main(n):
    if n < 3:
        raise ValueError('Order must be at least three.')
    start=time.time();exact,u,bits=independent_defect(n)
    import circ_gap_test as primary
    d,pu,base=primary.defect(n)
    assert reencode(d,pu,base,u)==exact,'Independent original polynomials differ'
    print('independent original polynomial matches',n,len(exact),flush=True)
    reps=list(primary.affine_reps(n));units=[a for a in range(n) if math.gcd(a,n)==1]
    covered={tuple((a*x+b)%n for x in pi) for pi in reps for a in units for b in range(n)}
    assert len(reps)==math.factorial(n)//(n*len(units)) and len(set(reps))==len(reps)
    assert covered==set(itertools.permutations(range(n)))
    reports=[];global_min=None
    for idx,pi in enumerate(reps):
        candidate=primary.gap_transform(d,pu,base,pi)
        assert all(v>0 for v in candidate.values())
        g=reencode(candidate,pu,base,u)
        sorted_original={sum((key//u[pi[k]]&((1<<bits)-1))*u[k] for k in range(n)):v for key,v in exact.items()}
        assert inverse_gap_transform(g,n,u,bits)==sorted_original
        expected_zero={2*n*u[0]}|{(2*n-1)*u[0]+u[j] for j in range(1,n)}
        assert len(g)==math.comb(3*n-1,n-1)-n
        assert not (set(g)&expected_zero)
        pure=[g.get(2*n*u[j],0) for j in range(1,n)]
        m=min(g.values());global_min=m if global_min is None else min(global_min,m)
        reports.append({'permutation':pi,'positive':len(g),'zeros':n,'minimum':m,'pure_gap_coefficients':pure})
        if idx%10==0:print('verified',n,idx+1,'/',len(reps),flush=True)
    assert len(reports)==len(reps) and {tuple(r['permutation']) for r in reports}==set(reps)
    examples=[]
    for w in [[1]*n,[1]+[0]*(n-1),[1,1]+[0]*(n-2),list(range(n))]:
        C=[[w[(j-i)%n] for j in range(n)] for i in range(n)]
        G=[[sum(C[i][k]*C[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
        p=permanent_integer(C);q=permanent_integer(G);value=n**n*p*p-math.factorial(n)*q
        assert evaluate(exact,w,u,bits)==value
        examples.append({'weights':w,'permanent':p,'gram_permanent':q,'defect':value})
    result={'n':n,'status':'PASS; exact computational certificate, not Lean formalization','chambers':len(reps),'covered_orderings':len(covered),'coefficients_per_chamber':math.comb(3*n-1,n-1),'positive_coefficients_per_chamber':len(g),'minimum_coefficient':global_min,'elapsed_seconds':time.time()-start,'chamber_checks':reports,'examples':examples}
    Path(f'independent_certificate_n{n}.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ['chamber_checks','examples']}),flush=True)

if __name__=='__main__':main(int(sys.argv[1]))
