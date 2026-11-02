#!/usr/bin/env python3
"""Exact boundary and block certificate for a connected simple graph.

Usage: python3 check_graph.py data/sharp14.json
Input JSON: {"n": number_of_vertices, "edges": [[u,v], ...]}.
Only the Python standard library is required. Vertices are 0,...,n-1.
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "structure"))
from check_block_theorems import adjacency, distances, blocks  # noqa: E402


def exact_data(n, edges):
    if n < 2:
        raise ValueError("This research uses connected graphs with at least two vertices.")
    if any(len(e) != 2 or min(e) < 0 or max(e) >= n or e[0] == e[1] for e in edges):
        raise ValueError("Edges must join two distinct vertices in 0,...,n-1.")
    normalized = {tuple(sorted(e)) for e in edges}
    if len(normalized) != len(edges):
        raise ValueError("Duplicate undirected edges are not permitted.")
    a = adjacency(n, sorted(normalized))
    ds = [distances(a, u) for u in range(n)]
    if any(x < 0 for row in ds for x in row):
        raise ValueError("Graph must be connected.")
    scores = [[sum(ds[u][v] - ds[w][v] for w in a[u]) for v in range(n)] for u in range(n)]
    beta = [max(row) for row in scores]
    boundary = [u for u in range(n) if beta[u] > 0]
    by_vertex = [[] for _ in a]
    block_rows = []
    cyclic = set()
    for ei, bedges in enumerate(blocks(a)):
        vertices = sorted({u for edge in bedges for u in edge})
        local = {u: i for i, u in enumerate(vertices)}
        ba = adjacency(len(vertices), [(local[u], local[v]) for u, v in bedges])
        bd = [distances(ba, u) for u in range(len(vertices))]
        bb = [max(sum(bd[u][v] - bd[w][v] for w in ba[u]) for v in range(len(vertices)))
              for u in range(len(vertices))]
        for u in vertices:
            by_vertex[u].append((bb[local[u]], len(ba[local[u]])))
        if len(vertices) > 2:
            cyclic.update(vertices)
        block_rows.append({"id": ei, "vertices": vertices,
                           "edges": [list(e) for e in bedges],
                           "boundary_size": sum(x > 0 for x in bb),
                           "beta_by_vertex": dict(zip(map(str, vertices), bb)),
                           "diameter": max(map(max, bd))})
    cuts = []
    for u, incident in enumerate(by_vertex):
        predicted = max(b - len(a[u]) + degree for b, degree in incident)
        assert predicted == beta[u], ("block stability formula", u)
        if len(incident) > 1:
            t = len(incident)
            c = sum(b > 0 for b, _ in incident)
            indicator = int(beta[u] > 0)
            defect = 2 * (t - 1) - c + indicator
            assert defect >= t - 2 >= 0
            cuts.append({"vertex": u, "incident_blocks": t, "local_boundary_count": c,
                         "global_boundary_indicator": indicator, "defect": defect})
    excess = sum(row["boundary_size"] - 2 for row in block_rows)
    defect_sum = sum(row["defect"] for row in cuts)
    assert len(boundary) == 2 + excess + defect_sum
    suppressed = [u for u in range(n) if len(a[u]) == 2 and u not in cyclic]
    kernel_order = n - len(suppressed)
    nonbridge = [row for row in block_rows if len(row["vertices"]) > 2]
    interior_sum = sum(len(row["vertices"]) - row["boundary_size"] for row in block_rows)
    assert kernel_order <= 4 * len(boundary) - 6 + interior_sum
    diameter_two_blocks = all(row["diameter"] <= 2 for row in nonbridge)
    cactus = all(len(row["edges"]) == len(row["vertices"]) for row in nonbridge)
    if diameter_two_blocks or cactus:
        assert kernel_order <= 4 * len(boundary) - 6
    return {"n": n, "m": len(edges), "boundary_size": len(boundary),
            "boundary": boundary, "beta": beta,
            "maximizing_witness": [row.index(max(row)) for row in scores],
            "distances": ds, "blocks": block_rows, "cut_vertices": cuts,
            "budget": {"block_excess": excess, "cut_defect": defect_sum,
                       "identity_verified": True},
            "suppressed_vertices": suppressed, "reduced_order": kernel_order,
            "intrinsic_block_interiors": interior_sum,
            "all_blocks_diameter_at_most_two": diameter_two_blocks,
            "cactus": cactus}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("graph", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    graph = json.loads(args.graph.read_text())
    result = exact_data(graph["n"], graph["edges"])
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
