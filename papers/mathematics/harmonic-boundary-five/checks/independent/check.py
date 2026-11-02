# Independent cross-check written for this release (no code shared with the other checkers):
# enumerate small graphs,
# compute the Steinerberger boundary from the definition, reduce, compare with catalogues.
import sys, os, itertools, json
import networkx as nx
from networkx.algorithms.graph_hashing import weisfeiler_lehman_graph_hash as wl

def apsp(adj):
    n=len(adj); D=[]
    for s in range(n):
        d=[-1]*n; d[s]=0; q=[s]
        for x in q:
            for y in adj[x]:
                if d[y]<0: d[y]=d[x]+1; q.append(y)
        D.append(d)
    return D

def boundary(adj):
    D=apsp(adj); n=len(adj); B=[]
    for x in range(n):
        dx=len(adj[x])
        for t in range(n):
            # mean of neighbours' distances < d(x,t)  <=> sum < deg*d
            if sum(D[w][t] for w in adj[x]) < dx*D[x][t]:
                B.append(x); break
    return B

def reduce_graph(G):
    G=G.copy()
    cyc=set()
    for comp in nx.biconnected_components(G):
        if len(comp)>2: cyc|=comp
    changed=True
    while changed:
        changed=False
        for v in list(G.nodes()):
            if G.degree(v)==2 and v not in cyc:
                a,b=list(G.neighbors(v)); G.remove_node(v); G.add_edge(a,b); changed=True; break
    return nx.convert_node_labels_to_integers(G)

class Canon:
    def __init__(s): s.b={}
    def add(s,G):
        h=(G.number_of_nodes(),G.number_of_edges(),wl(G,iterations=4))
        L=s.b.setdefault(h,[])
        for H in L:
            if nx.is_isomorphic(G,H): return False
        L.append(G); return True
    def all(s): return [g for L in s.b.values() for g in L]

def load_g6(path):
    return [nx.from_graph6_bytes(l.strip()) for l in open(path,'rb') if l.strip()]

def adjl(G):
    n=G.number_of_nodes(); return [list(G.neighbors(v)) for v in range(n)]

def graphs_upto(nmax, maxdeg=None):
    levels={1:[nx.empty_graph(1)]}
    for n in range(1,nmax):
        C=Canon()
        for G in levels[n]:
            ok=[v for v in G if maxdeg is None or G.degree(v)<maxdeg]
            for k in range(0,(len(ok) if maxdeg is None else min(maxdeg,len(ok)))+1):
                for S in itertools.combinations(ok,k):
                    H=G.copy(); H.add_node(n); H.add_edges_from((n,s) for s in S); C.add(H)
        levels[n+1]=C.all()
        pass
    return levels

def last_step(levels, n, maxdeg, k, canon):
    """candidates of order n built from order n-1 (no dedupe); keep connected b=k, record kernels"""
    cnt=0
    for G in levels[n-1]:
        ok=[v for v in G if maxdeg is None or G.degree(v)<maxdeg]
        top=len(ok) if maxdeg is None else min(maxdeg,len(ok))
        for kk in range(1,top+1):
            for S in itertools.combinations(ok,kk):
                H=G.copy(); H.add_node(n-1); H.add_edges_from((n-1,s) for s in S)
                if not nx.is_connected(H): continue
                if len(boundary(adjl(H)))==k:
                    cnt+=1; canon.add(reduce_graph(H))
    return cnt

if __name__=='__main__':
    mode=sys.argv[1]; cat=sys.argv[2]; nmax=int(sys.argv[3])
    if mode=='five': k,maxdeg=5,None
    else: k,maxdeg=6,3
    kernels=load_g6(cat)
    for K in kernels:
        assert nx.is_connected(K) and len(boundary(adjl(K)))==k, 'bad kernel'
        if maxdeg: assert max(d for _,d in K.degree())<=maxdeg
        assert nx.is_isomorphic(reduce_graph(K),K)
    print(len(kernels),'kernels: all connected, boundary',k,', reduced')
    levels=graphs_upto(nmax-1,maxdeg)
    canon=Canon()
    for n in range(2,nmax):  # full lists for orders < nmax
        for G in levels[n]:
            if nx.is_connected(G) and len(boundary(adjl(G)))==k: canon.add(reduce_graph(G))
    c=last_step(levels,nmax,maxdeg,k,canon)
    found=canon.all()
    small=[K for K in kernels if K.number_of_nodes()<=nmax]
    fc=Canon(); [fc.add(g) for g in found]
    miss=[K for K in small if fc.add(K)]
    extra=[g for g in found if not any(nx.is_isomorphic(g,K) for K in small if K.number_of_nodes()==g.number_of_nodes())]
    from collections import Counter
    print('found reduced kernels by order',sorted(Counter(g.number_of_nodes() for g in found).items()))
    print('catalogue kernels by order <=',nmax,sorted(Counter(g.number_of_nodes() for g in small).items()))
    print('missing',len(miss),'extra',len(extra))
    print('PASS' if not miss and not extra else 'FAIL')
    sys.exit(0 if not miss and not extra else 1)
