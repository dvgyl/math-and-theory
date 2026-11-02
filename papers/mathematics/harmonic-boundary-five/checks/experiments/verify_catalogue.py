#!/usr/bin/env python3
"""Independent catalogue verification without nauty or orbit pruning.
Uses exact GraphMatcher after invariant bucketing. Checks all allowed attachments
with fresh shortest-path boundary computation (not the incremental formula).
"""
import json,hashlib
from pathlib import Path
from collections import defaultdict,Counter
import networkx as nx
ROOT=Path(__file__).resolve().parent

def stability(g):
    d=dict(nx.all_pairs_shortest_path_length(g))
    return {x:max(sum(d[x][y]-d[z][y] for z in g[x]) for y in g) for x in g}

def reduce_independently(g):
    g=g.copy()
    while True:
        cuts=set(nx.articulation_points(g))
        v=next((v for v in cuts if g.degree(v)==2),None)
        if v is None:return nx.convert_node_labels_to_integers(g)
        u,w=list(g[v]);assert not g.has_edge(u,w)
        g.remove_node(v);g.add_edge(u,w)

def attach(g,h,x,r):
    z=nx.disjoint_union(g,h)
    z=nx.contracted_nodes(z,x,len(g)+r,self_loops=False)
    return nx.convert_node_labels_to_integers(z)

def invariant(g):
    return len(g),g.number_of_edges(),nx.weisfeiler_lehman_graph_hash(g)

def main():
    rows=json.loads((ROOT/'reduced_kernels.json').read_text());buckets=defaultdict(list);catalogue=[];counts=Counter()
    for row in rows:
        g=nx.from_graph6_bytes(row['graph6'].encode());assert set(g.edges())==set(map(tuple,row['edges']))
        b=stability(g);k=sum(v>0 for v in b.values());assert k==row['boundary_size']<=5
        assert [b[v] for v in g]==row['beta']
        assert len(reduce_independently(g))==len(g)
        assert len(g)<=4*k-6
        assert all(len(c)==2 or nx.diameter(g.subgraph(c))<=2 for c in nx.biconnected_components(g))
        key=invariant(g);assert not any(nx.is_isomorphic(g,h) for h in buckets[key])
        buckets[key].append(g);catalogue.append((g,k));counts[k]+=1
    def present(g):
        return any(nx.is_isomorphic(g,h) for h in buckets[invariant(g)])
    seeds=[nx.path_graph(2)]+[nx.from_graph6_bytes(row['graph6'].encode()) for row in json.loads((ROOT/'small_biconnected_cores.json').read_text())]
    assert all(present(g) for g in seeds)
    seed_data=[(h,sum(v>0 for v in stability(h).values())) for h in seeds]
    attempted=0;accepted=0
    for g,k in catalogue:
        placements=[(g,x) for x in g]
        for u,v in nx.bridges(g):
            z=g.copy();x=len(z);z.remove_edge(u,v);z.add_edges_from([(u,x),(x,v)]);placements.append((z,x))
        for z,x in placements:
            for h,kh in seed_data:
                if k+kh-2>5:continue # at most the two identified boundary vertices can be lost
                for r in h:
                    zz=reduce_independently(attach(z,h,x,r));attempted+=1
                    kk=sum(v>0 for v in stability(zz).values())
                    if kk<=5:
                        accepted+=1;assert present(zz),(nx.to_graph6_bytes(zz,header=False),kk)
    result=dict(catalogue_states=len(catalogue),counts_by_boundary=dict(counts),exact_isomorphism_uniqueness=True,seed_inclusion=True,closure_placements_checked=attempted,allowed_closure_results_checked=accepted,all_closure_results_present=True,canonical_graph6_sha256=hashlib.sha256((ROOT/'all_reduced_kernels_boundary_le5.g6').read_bytes()).hexdigest())
    (ROOT/'catalogue_certificate_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
