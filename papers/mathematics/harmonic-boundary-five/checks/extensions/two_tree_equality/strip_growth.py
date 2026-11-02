#!/usr/bin/env python3
"""Exact SCC certificate and explicit five-parameter family of odd extrema.

The SCC calculation uses only the final compact grammar, not the generator.
The lower-family checks use fresh BFS distances, not local-state arithmetic.
Python standard library only.  Run from any working directory.
"""
from pathlib import Path
from collections import defaultdict, deque, Counter
from itertools import combinations
import json, argparse

ROOT = Path(__file__).resolve().parent

def frozen(x):
    return tuple(frozen(y) if isinstance(y, list) else y for y in x)

def sccs(n, edges):
    adj = [[] for _ in range(n)]
    rev = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b); rev[b].append(a)
    order = []; seen = set()
    def dfs(v):
        if v in seen: return
        seen.add(v)
        for w in adj[v]: dfs(w)
        order.append(v)
    for v in range(n): dfs(v)
    seen.clear(); out = []
    def collect(v, c):
        if v in seen: return
        seen.add(v); c.add(v)
        for w in rev[v]: collect(w, c)
    for v in reversed(order):
        if v not in seen:
            c = set(); collect(v, c); out.append(c)
    return out

def grammar_certificate():
    data = json.loads((ROOT/'extremal_grammars.json').read_text())['targets']['5']
    states = list(map(frozen, data['states']))
    index = {s: i for i, s in enumerate(states)}
    rules = [(index[frozen(d)], [index[frozen(c)] for c in cc], w, tag)
             for d, cc, w, tag, red in data['rules']]
    edges = [(cc[0], d) for d, cc, w, tag in rules if len(cc) == 1]
    comps = sccs(len(states), edges)
    comp_of = {v: i for i, c in enumerate(comps) for v in c}
    cycles = {}; edge_set = set(edges)
    for i, c in enumerate(comps):
        internal = [(cc[0], d, w, tag) for d, cc, w, tag in rules
                    if len(cc) == 1 and cc[0] in c and d in c]
        if len(c) > 1 or any((v, v) in edge_set for v in c):
            assert len(internal) == len(c)
            assert Counter(a for a,b,w,t in internal) == Counter(c)
            assert Counter(b for a,b,w,t in internal) == Counter(c)
            assert sum(w for a,b,w,t in internal) == 0
            assert sum(1+t[2]+t[3] for a,b,w,t in internal) == 2
            cycles[i] = internal
    assert len(cycles) == 6
    assert sorted(len(c) for c in cycles.values()) == [1, 1, 2, 2, 2, 2]
    assert all(tag[0] != 'triangle' for d, cc, w, tag in rules)
    assert max(s[1][0] for s in states) == 2
    roots = [(index[frozen(l)], index[frozen(r)], w, tag)
             for l, r, w, tag in data['final_rules']]
    assert max(states[l][1][0]+states[r][1][0] for l,r,w,t in roots) == 3

    # Condense the unary SCCs. Every binary rule increases leaf count, so
    # adding its dependencies still leaves an acyclic condensation graph.
    outgoing = defaultdict(set); incoming = defaultdict(set)
    for d, cc, w, tag in rules:
        for c in cc:
            a, b = comp_of[c], comp_of[d]
            if a != b:
                outgoing[a].add(b); incoming[b].add(a)
    todo = deque(i for i in range(len(comps)) if not incoming[i])
    degree = {i: len(incoming[i]) for i in range(len(comps))}
    order = []
    while todo:
        a = todo.popleft(); order.append(a)
        for b in outgoing[a]:
            degree[b] -= 1
            if degree[b] == 0: todo.append(b)
    assert len(order) == len(comps)
    slots = {}
    for j in order:
        options = [sum(slots[comp_of[c]] for c in cc)
                   for d, cc, w, tag in rules if comp_of[d] == j
                   and all(comp_of[c] != j for c in cc)]
        assert options
        slots[j] = int(j in cycles) + max(options)
    node_slots = [slots[comp_of[i]] for i in range(len(states))]
    branch_roots = [(l,r,w,t) for l,r,w,t in roots
                    if states[l][1][0]+states[r][1][0] == 3]
    assert max(node_slots[l]+node_slots[r] for l,r,w,t in branch_roots) == 5
    assert max(node_slots[i] for i,s in enumerate(states) if s[0] == 1) == 3
    # At a leaf-adjacent edge in a triangle path, the leaf side is the
    # initial triangle itself, not an arbitrary component in its state.
    cap_states = {d for d, cc, w, tag in rules if not cc}
    path_roots = [(l,r,w,t) for l,r,w,t in roots
                  if states[l][0] == states[r][0] == 1
                  and (l in cap_states or r in cap_states)]
    path_slots = max(max([node_slots[r]] if l in cap_states else [])
                     if r not in cap_states else
                     max(([node_slots[r]] if l in cap_states else [])+[node_slots[l]])
                     for l,r,w,t in path_roots)
    assert path_slots == 3
    return dict(passed=True, state_count=len(states), rule_count=len(rules),
                cyclic_components=[dict(states=sorted(comps[j]), rules=es,
                                        vertices_per_lap=2) for j,es in cycles.items()],
                maximum_cycle_slots_per_state=node_slots,
                maximum_slots_at_branch_root=5,
                maximum_slots_at_leaf_normalized_path_root=3,
                triangle_join_rules=0, maximum_internal_core_edge_multiplicity=3)

def add_vertex(g, a, b):
    x = len(g); g.append({a, b}); g[a].add(x); g[b].add(x)
    return x

def arm(a):
    """Rooted F-arm A(a), roots (degree-two low, degree-three high)."""
    g = [{1, 2}, {0, 2}, {0, 1}]
    add_vertex(g, 0, 2); add_vertex(g, 0, 2)
    w = add_vertex(g, 1, 2)
    lo, hi = w, 1
    for _ in range(a):
        t = add_vertex(g, lo, hi)
        z = add_vertex(g, hi, t)
        lo, hi = z, t
    assert len(g) == 6+2*a and (len(g[lo]), len(g[hi])) == (2, 3)
    return g, (lo, hi)

def glue(g, roots, h, other_roots, flip=False):
    """Identify the two root edges; return the first graph's root labels."""
    ans = [set(x) for x in g]
    target = roots[::-1] if flip else roots
    mapping = {other_roots[0]: target[0], other_roots[1]: target[1]}
    for v in range(len(h)):
        if v not in mapping:
            mapping[v] = len(ans); ans.append(set())
    for v, ns in enumerate(h):
        for w in ns:
            ans[mapping[v]].add(mapping[w])
    return ans, roots

def cherry(a, b):
    g, roots = arm(a); h, rs = arm(b)
    ans, roots = glue(g, roots, h, rs)
    assert tuple(len(ans[v]) for v in roots) == (3, 5)
    return ans, roots

def family(a, b, c, d, r):
    """Four F-arms and a central degree-six strip; order 19+2*sum(params)."""
    g, left = cherry(a, b)
    h, (lo, hi) = cherry(c, d)
    z = add_vertex(h, lo, hi); lo, hi = z, lo
    for _ in range(r):
        add_vertex(h, lo, hi)  # remains a degree-two ear
        z = add_vertex(h, lo, hi); lo, hi = z, lo
    assert (len(h[lo]), len(h[hi])) == (2, 4)
    ans, _ = glue(g, left, h, (lo, hi), flip=True)
    assert len(ans) == 19+2*(a+b+c+d+r)
    return ans

def bfs_boundary(g):
    n = len(g); scores = [-n*n]*n
    for v in range(n):
        ds = [-1]*n; ds[v] = 0; q = deque([v])
        while q:
            x = q.popleft()
            for y in g[x]:
                if ds[y] < 0: ds[y] = ds[x]+1; q.append(y)
        assert min(ds) >= 0
        for u in range(n):
            scores[u] = max(scores[u], len(g[u])*ds[u]-sum(ds[w] for w in g[u]))
    return scores

def core_lengths(g):
    """Recover the five parameters from the canonical pruned incidence tree."""
    keep = {v for v in range(len(g)) if len(g[v]) > 2}
    edges = [(a,b) for a in keep for b in g[a] & keep if a < b]
    triangles = [(a,b,c) for a,b in edges for c in g[a] & g[b] & keep if b<c]
    incid = defaultdict(set)
    for tri in triangles:
        t = ('t', tri)
        for e in combinations(tri, 2):
            en = ('e', e); incid[t].add(en); incid[en].add(t)
    for node in [v for v in incid if v[0] == 'e' and len(incid[v]) == 1]:
        t = next(iter(incid[node])); incid[t].remove(node); del incid[node]
    branches = [v for v in incid if len(incid[v]) == 3]
    assert len(branches) == 2 and all(v[0] == 'e' for v in branches)
    arm_lengths = []; central = None
    for branch in branches:
        local = []
        for nxt in incid[branch]:
            prev, cur, count = branch, nxt, 0
            while True:
                if cur[0] == 't': count += 1
                if len(incid[cur]) != 2: break
                nxt = next(v for v in incid[cur] if v != prev)
                prev, cur = cur, nxt
            if cur in branches:
                if central is not None: assert central == count
                central = count
            else:
                assert cur[0] == 't' and len(incid[cur]) == 1
                assert count >= 2 and count % 2 == 0
                local.append((count-2)//2)
        assert len(local) == 2
        arm_lengths.append(tuple(sorted(local)))
    assert central is not None and central >= 1
    return tuple(sorted(arm_lengths)), central-1

def compositions(total, k):
    if k == 1:
        yield (total,); return
    for a in range(total+1):
        for rest in compositions(total-a, k-1): yield (a,)+rest

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--parameter-sum', type=int, default=7)
    args = parser.parse_args()
    report = grammar_certificate(); count = 0; maxn = 0
    for total in range(args.parameter_sum+1):
        for a,b,c,d,r in compositions(total, 5):
            g = family(a,b,c,d,r); scores = bfs_boundary(g)
            assert sum(x>0 for x in scores) == (len(g)+5)//2
            assert max(len(ns) for ns in g) == 6
            assert core_lengths(g) == (tuple(sorted((tuple(sorted((a,b))),tuple(sorted((c,d)))))),r)
            count += 1; maxn = max(maxn, len(g))
    report['lower_family'] = dict(parameter_tuples_checked=count,
        maximum_order=maxn, maximum_parameter_sum=args.parameter_sum,
        order_formula='19+2*(a+b+c+d+r)',
        isomorphism_multiplicity_at_most=8,
        exact_boundary_and_recovered_parameters=True)
    (ROOT/'strip_growth_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__': main()
