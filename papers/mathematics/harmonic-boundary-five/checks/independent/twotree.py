# Independent cross-check written for this release: minimum boundary of 2-trees and number of extremizers, small n.
import sys, os, math, warnings
warnings.filterwarnings('ignore')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check import Canon, boundary, adjl
import networkx as nx
def a_formula(n):
    if n%2==0: return 2 if n==6 else 3
    if n==7: return 7
    c,d={1:(-1126,2250),3:(-1090,1962),5:(-1126,2298),7:(-1090,1914)}[n%8]
    v=n**4-20*n**3+239*n**2+c*n+d; assert v%192==0; return v//192
N=int(sys.argv[1])
level=[nx.complete_graph(3)]
for n in range(4,N+1):
    last = (n==N)
    C=Canon(); best=None; ext=Canon()
    for G in level:
        for (u,v) in G.edges():
            H=G.copy(); H.add_edge(n-1,u); H.add_edge(n-1,v)
            if last:
                b=len(boundary(adjl(H)))
                if best is None or b<best: best=b; ext=Canon()
                if b==best: ext.add(H)
            else: C.add(H)
    if not last:
        level=C.all()
        bs=[len(boundary(adjl(G))) for G in level]; m=min(bs)
        E=sum(1 for b in bs if b==m)
        assert n<6 or (m==math.ceil(n/2)+2 and E==a_formula(n))
        print(n,'two-trees',len(level),'min b',m,'expected',(math.ceil(n/2)+2 if n>=6 else None),'extremizers',E,'formula',(a_formula(n) if n>=6 else None),flush=True)
    else:
        assert best==math.ceil(n/2)+2 and len(ext.all())==a_formula(n)
        print(n,'(no dedupe of all) min b',best,'expected',math.ceil(n/2)+2,'extremizers',len(ext.all()),'formula',a_formula(n),flush=True)
