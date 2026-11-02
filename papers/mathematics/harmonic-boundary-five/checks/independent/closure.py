# Independent closure written for this release (no nauty, no code shared with the other checkers): starting from the
# two-connected subcubic blocks with boundary <= 6 found by ears.py (file argument)
# and K2, attach rooted blocks at vertices or at subdivision points of bridges,
# keep subcubic graphs with boundary <= 6, reduce, deduplicate up to isomorphism.
import sys, os, json, warnings, time
warnings.filterwarnings('ignore')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check import boundary, adjl, reduce_graph, load_g6
import networkx as nx
from collections import Counter
t0=time.time()
K=int(sys.argv[3]) if len(sys.argv)>3 else 6
MAXD=int(sys.argv[4]) if len(sys.argv)>4 else 3
if sys.argv[1]=='all6':
    from check import graphs_upto
    lv=graphs_upto(6)
    blocks=[G for n in range(3,7) for G in lv[n] if nx.is_biconnected(G)]
else:
    blocks=[nx.from_graph6_bytes(s.encode()) for s in json.load(open(sys.argv[1]))]
blocks=[B for B in blocks if len(boundary(adjl(B)))<=K and max(d for _,d in B.degree())<=MAXD]+[nx.complete_graph(2)]
print('nonbridge blocks:',len(blocks)-1)
def inv(G):
    return (G.number_of_nodes(),G.number_of_edges(),tuple(sorted(d for _,d in G.degree())),
            tuple(sorted(tuple(sorted(Counter(nx.single_source_shortest_path_length(G,v).values()).items())) for v in G)))
store={}
def add(G):
    k=inv(G); L=store.setdefault(k,[])
    for H in L:
        if nx.is_isomorphic(G,H): return False
    L.append(G); return True
def orbits_roots(B):
    # one representative root per automorphism orbit
    reps=[]; seen=set()
    GM=nx.algorithms.isomorphism.GraphMatcher(B,B)
    autos=list(GM.isomorphisms_iter())
    for v in B:
        if v in seen: continue
        reps.append(v); seen|={a[v] for a in autos}
    return reps
seeds=[(B,r) for B in blocks for r in orbits_roots(B)]
queue=[]
for B in blocks:
    R=reduce_graph(B)
    if add(R): queue.append(R)
while queue:
    G=queue.pop()
    n=G.number_of_nodes()
    bridges=list(nx.bridges(G))
    points=[('v',v) for v in G if G.degree(v)<=MAXD-1]+[('e',e) for e in bridges]
    for kind,pt in points:
        for B,r in seeds:
            dB=B.degree(r)
            if kind=='v' and G.degree(pt)+dB>MAXD: continue
            if kind=='e' and 2+dB>MAXD: continue
            H=nx.convert_node_labels_to_integers(G)
            m=H.number_of_nodes()
            if kind=='e':
                a,b=pt; H.remove_edge(a,b); H.add_edge(a,m); H.add_edge(m,b); x=m; m+=1
            else: x=pt
            mp={v:m+i for i,v in enumerate(w for w in B if w!=r)}; mp[r]=x
            H.add_edges_from((mp[u],mp[v]) for u,v in B.edges())
            if len(boundary(adjl(H)))>K: continue
            R=reduce_graph(H)
            if add(R): queue.append(R)
allg=[G for L in store.values() for G in L]
six=[G for G in allg if len(boundary(adjl(G)))==K]
print('states with boundary <= K:',len(allg),'boundary K:',len(six),'by order',sorted(Counter(G.number_of_nodes() for G in six).items()))
cat=load_g6(sys.argv[2]); cs={}
for K in cat: cs.setdefault(inv(K),[]).append(K)
ok=len(six)==len(cat) and all(any(nx.is_isomorphic(G,K) for K in cs.get(inv(G),[])) for G in six)
print('equals the catalogue:',ok,'seconds',round(time.time()-t0))
sys.exit(0 if ok else 1)
