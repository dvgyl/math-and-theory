#!/usr/bin/env python3
"""Exact independent checks for bipartite subcubic and Cartesian results.

Requires NetworkX.  Optional exhaustive generation:
  PYTHONPATH=/tmp/harmonic-deps python check_new_results.py --geng /path/to/geng

All boundary decisions use unnormalized integer sums of integer BFS distances.
No floating-point computation or optimization solver is used.
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
from collections import deque
from pathlib import Path

import networkx as nx


HERE = Path(__file__).resolve().parent


def exact_scores(g: nx.Graph):
    vertices = list(g)
    distances = {}
    for source in vertices:
        row = {source: 0}
        queue = deque([source])
        while queue:
            v = queue.popleft()
            for w in g[v]:
                if w not in row:
                    row[w] = row[v] + 1
                    queue.append(w)
        assert len(row) == len(vertices), "Input must be connected"
        distances[source] = row
    scores = {
        u: max(
            sum(distances[u][t] - distances[w][t] for w in g[u])
            for t in vertices
        )
        for u in vertices
    }
    return scores, distances


def cyclic_vertices(g: nx.Graph):
    bridges = {frozenset(e) for e in nx.bridges(g)}
    return {
        v
        for e in g.edges()
        if frozenset(e) not in bridges
        for v in e
    }


def reduced(g: nx.Graph):
    h = nx.convert_node_labels_to_integers(g)
    while True:
        cyclic = cyclic_vertices(h)
        removable = next((v for v in h if h.degree(v) == 2 and v not in cyclic), None)
        if removable is None:
            return nx.convert_node_labels_to_integers(h)
        u, w = list(h[removable])
        assert not h.has_edge(u, w)
        h.remove_node(removable)
        h.add_edge(u, w)


def assert_topological_theorem(g: nx.Graph):
    assert len(g) >= 2 and nx.is_connected(g)
    assert nx.is_bipartite(g) and max(dict(g.degree()).values()) <= 3
    scores, _ = exact_scores(g)
    boundary = {v for v in g if scores[v] > 0}
    cyclic = cyclic_vertices(g)
    assert boundary == cyclic | {v for v in g if g.degree(v) == 1}
    kernel = reduced(g)
    kc = cyclic_vertices(kernel)
    a = sum(int(u in kc) + int(v in kc) for u, v in nx.bridges(kernel))
    blocks = [block for block in nx.biconnected_components(kernel) if len(block) >= 3]
    exact_bound = 2 * len(boundary) - 2 - sum(len(block) - 2 for block in blocks) - a
    assert len(kernel) == exact_bound
    assert len(kernel) <= 2 * len(boundary) - 2
    assert (len(kernel) == 2 * len(boundary) - 2) == nx.is_tree(kernel)
    return boundary, kernel


def six_kernels():
    result = []
    for name, internal in [
        ("six_leaf_tree_internal_path", nx.path_graph(4)),
        ("six_leaf_tree_internal_star", nx.star_graph(3)),
    ]:
        g = internal.copy()
        for v in list(internal):
            for _ in range(3 - internal.degree(v)):
                g.add_edge(v, len(g))
        result.append((name, g))
    for name, second in [("square_adjacent_leaves", 1), ("square_opposite_leaves", 2)]:
        g = nx.cycle_graph(4)
        g.add_edges_from([(0, 4), (second, 5)])
        result.append((name, g))
    g = nx.cycle_graph(4)
    g.add_edges_from([(0, 4), (4, 5), (4, 6)])
    result.append(("square_attached_fork", g))
    g = nx.complete_bipartite_graph(2, 3)
    g.add_edge(2, 5)
    result.append(("k23_pendant_leaf", g))
    result.extend([
        ("hexagon", nx.cycle_graph(6)),
        ("ladder_2_by_3", nx.convert_node_labels_to_integers(nx.cartesian_product(nx.path_graph(2), nx.path_graph(3)))),
    ])
    g = nx.complete_bipartite_graph(3, 3)
    g.remove_edge(0, 3)
    result.append(("k33_minus_edge", g))
    result.append(("k33", nx.complete_bipartite_graph(3, 3)))
    return result


def subdivide_bridges(g, rng):
    h = g.copy()
    for u, v in list(nx.bridges(g)):
        length = rng.randint(1, 8)
        if length == 1:
            continue
        h.remove_edge(u, v)
        start = len(h)
        path = [u] + list(range(start, start + length - 1)) + [v]
        h.add_edges_from(zip(path, path[1:]))
    return h


def product_catalogue_checks():
    p2, p3 = nx.path_graph(2), nx.path_graph(3)
    k3, star = nx.complete_graph(3), nx.star_graph(3)
    expected = {
        6: [(p2, p3), (p2, k3), (p2, star)],
        9: [(p3, k3), (p3, star), (k3, k3), (k3, star), (star, star)],
    }
    catalogue = {}
    for b, pairs in expected.items():
        graphs = []
        for h, k in pairs:
            scores_h, _ = exact_scores(h)
            scores_k, _ = exact_scores(k)
            product = nx.cartesian_product(h, k)
            scores_p, _ = exact_scores(product)
            assert all(scores_p[(x, y)] == scores_h[x] + scores_k[y] for x, y in product)
            assert sum(v > 0 for v in scores_p.values()) == b
            assert not any(nx.is_isomorphic(product, other) for other in graphs)
            graphs.append(product)
        catalogue[b] = len(graphs)
    # All connected factors in the atlas, restricted to boundary at most four,
    # provide an independent small-factor adversarial check of the classifications.
    factors = []
    for g in nx.graph_atlas_g():
        if len(g) >= 2 and nx.is_connected(g):
            scores, _ = exact_scores(g)
            b = sum(v > 0 for v in scores.values())
            if b <= 4:
                factors.append((g, scores, b))
    tested = 0
    for i, (h, sh, bh) in enumerate(factors):
        for k, sk, bk in factors[i:]:
            if bh * bk > 9:
                continue
            tested += 1
            b = sum(a + c > 0 for a in sh.values() for c in sk.values())
            assert b != 7
            if b in expected:
                product = nx.cartesian_product(h, k)
                assert any(nx.is_isomorphic(product, nx.cartesian_product(a, c)) for a, c in expected[b])
    return {"catalogue_counts": catalogue, "atlas_factor_pairs": tested}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--geng", help="Optional path to nauty geng for exhaustive orders 2–10")
    parser.add_argument("--max-order", type=int, default=10)
    args = parser.parse_args()
    kernels = six_kernels()
    rng = random.Random(20261102)
    records = []
    subdivisions = 0
    for index, (name, g) in enumerate(kernels, 1):
        boundary, kernel = assert_topological_theorem(g)
        assert len(boundary) == 6 and len(kernel) == len(g)
        for _, previous in kernels[:index - 1]:
            assert not nx.is_isomorphic(g, previous)
        scores, distances = exact_scores(g)
        records.append({
            "id": index,
            "name": name,
            "order": len(g),
            "edges": sorted(sorted(e) for e in g.edges()),
            "boundary": sorted(boundary),
            "scores": [scores[v] for v in range(len(g))],
            "diameter": max(max(row.values()) for row in distances.values()),
            "graph6": nx.to_graph6_bytes(g, header=False).decode().strip(),
        })
        for _ in range(30):
            h = subdivide_bridges(g, rng)
            b, reduced_h = assert_topological_theorem(h)
            assert len(b) == 6 and nx.is_isomorphic(reduced_h, g)
            subdivisions += 1
    atlas_count = 0
    for g in nx.graph_atlas_g():
        if len(g) >= 2 and nx.is_connected(g) and nx.is_bipartite(g) and max(dict(g.degree()).values()) <= 3:
            b, k = assert_topological_theorem(g)
            if len(b) == 6:
                assert sum(nx.is_isomorphic(k, h) for _, h in kernels) == 1
            atlas_count += 1
    census = []
    if args.geng:
        for n in range(2, args.max_order + 1):
            process = subprocess.Popen([args.geng, "-cq", "-b", "-D3", str(n)], stdout=subprocess.PIPE)
            count = 0
            six_count = 0
            assert process.stdout is not None
            for line in process.stdout:
                g = nx.from_graph6_bytes(line.strip())
                b, k = assert_topological_theorem(g)
                if len(b) == 6:
                    assert sum(nx.is_isomorphic(k, h) for _, h in kernels) == 1
                    six_count += 1
                count += 1
            assert process.wait() == 0
            census.append({"order": n, "total": count, "boundary_six": six_count})
    grid = nx.grid_2d_graph(3, 3)
    grid_scores, _ = exact_scores(grid)
    assert grid_scores[(1, 1)] == 0 and (1, 1) in cyclic_vertices(grid)
    theta = nx.Graph()
    for path in ([0, 1], [0, 2, 3, 4, 1], [0, 5, 6, 7, 1]):
        theta.add_edges_from(zip(path, path[1:]))
    theta_scores, _ = exact_scores(theta)
    assert not nx.is_bipartite(theta) and nx.is_biconnected(theta)
    assert theta_scores[0] == theta_scores[1] == 0
    assert sum(v > 0 for v in theta_scores.values()) == 6
    assert cyclic_vertices(theta) == set(theta)
    result = {
        "status": "all exact checks passed",
        "kernels": len(kernels),
        "bridge_subdivision_trials": subdivisions,
        "atlas_graphs": atlas_count,
        "exhaustive_bipartite_subcubic": census,
        "cartesian": product_catalogue_checks(),
        "degree_four_counterexample": {"graph": "3 by 3 grid", "central_score": 0},
        "nonbipartite_counterexample": {"graph": "theta with lengths 1,4,4", "terminal_scores": [0, 0], "boundary_size": 6},
    }
    (HERE / "bipartite_six_kernels.json").write_text(json.dumps(records, indent=2) + "\n")
    (HERE / "new_results_verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
