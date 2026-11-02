#!/usr/bin/env python3
"""Independent full-vertex/full-bridge closure of the subcubic catalogue.

Uses standard-library graph routines and nauty only for exact isomorphism.
No automorphism orbit pruning and no import of the catalogue generator.
The glued-root stability formula is independently checked by fresh BFS
at every degree-admissible attachment, including rejected attachments.
"""

from argparse import ArgumentParser
from collections import Counter, deque
from pathlib import Path
import json
import subprocess
import time


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'six_boundary'


def decode(code):
    raw = code.encode() if isinstance(code, str) else code
    n = raw[0] - 63
    assert 2 <= n <= 62
    g = [set() for _ in range(n)]
    bit = 0
    for j in range(1, n):
        for i in range(j):
            if ((raw[1 + bit // 6] - 63) >> (5 - bit % 6)) & 1:
                g[i].add(j)
                g[j].add(i)
            bit += 1
    return g


def encode(g):
    values, word, filled = [len(g) + 63], 0, 0
    for j in range(1, len(g)):
        for i in range(j):
            word = (word << 1) | int(i in g[j])
            filled += 1
            if filled == 6:
                values.append(word + 63)
                word = filled = 0
    if filled:
        values.append((word << (6 - filled)) + 63)
    return bytes(values)


def bfs(g, source):
    d = [-1] * len(g)
    d[source] = 0
    queue = deque([source])
    while queue:
        v = queue.popleft()
        for w in g[v]:
            if d[w] < 0:
                d[w] = d[v] + 1
                queue.append(w)
    assert min(d) >= 0
    return d


def scores(g):
    d = [bfs(g, v) for v in range(len(g))]
    return [max(len(g[u]) * d[u][t] - sum(d[w][t] for w in g[u])
                for t in range(len(g))) for u in range(len(g))]


def root_score(g, u):
    center = bfs(g, u)
    adjacent = [bfs(g, w) for w in g[u]]
    return max(len(g[u]) * center[t] - sum(row[t] for row in adjacent)
               for t in range(len(g)))


def bridges_and_blocks(g):
    clock = 0
    discovery, low, stack, bridges, blocks = {}, {}, [], [], []
    def visit(u, parent):
        nonlocal clock
        discovery[u] = low[u] = clock
        clock += 1
        for v in g[u]:
            if v == parent:
                continue
            if v not in discovery:
                stack.append((u, v))
                visit(v, u)
                low[u] = min(low[u], low[v])
                if low[v] > discovery[u]:
                    bridges.append((u, v))
                if low[v] >= discovery[u]:
                    vertices = set()
                    while True:
                        e = stack.pop()
                        vertices.update(e)
                        if e == (u, v):
                            break
                    blocks.append(vertices)
            elif discovery[v] < discovery[u]:
                stack.append((u, v))
                low[u] = min(low[u], discovery[v])
    visit(0, None)
    assert len(discovery) == len(g) and not stack
    return bridges, blocks


def induced(g, vertices):
    vertices = sorted(vertices)
    mapping = {v: i for i, v in enumerate(vertices)}
    return [{mapping[w] for w in g[v] if w in mapping} for v in vertices]


def attach(g, h, vertex, root):
    result = [set(ns) for ns in g]
    mapping = {root: vertex}
    for v in range(len(h)):
        if v != root:
            mapping[v] = len(result)
            result.append(set())
    for v, ns in enumerate(h):
        for w in ns:
            result[mapping[v]].add(mapping[w])
    return result


def canonical(codes, labelg):
    codes = list(codes)
    if not codes:
        return []
    result = subprocess.run([labelg, '-q'], input=b'\n'.join(codes) + b'\n',
                            capture_output=True, check=True)
    answer = result.stdout.splitlines()
    assert len(answer) == len(codes)
    return answer


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--labelg', required=True)
    args = parser.parse_args()
    started = time.monotonic()
    rows = json.loads((SOURCE / 'connected_subcubic_kernels.json').read_text())
    core_rows = json.loads((SOURCE / 'subcubic_core_palette.json').read_text())
    known = {r['graph6'].encode() for r in rows}
    assert len(rows) == len(known) == 264
    assert set(canonical(known, args.labelg)) == known
    palette = {r['graph6'].encode() for r in core_rows}
    prepared = [(decode(r['graph6']), scores(decode(r['graph6']))) for r in core_rows]
    candidates, block_codes, attempts = set(), set(), Counter()
    counts = Counter()
    for row in rows:
        g = decode(row['graph6'])
        beta = scores(g)
        assert beta == row['scores']
        boundary = sum(x > 0 for x in beta)
        assert boundary == row['boundary_size'] <= 6
        assert len(g) == row['order'] <= 4 * boundary - 6
        assert max(map(len, g)) <= 3
        counts[boundary, len(g)] += 1
        bridges, blocks = bridges_and_blocks(g)
        bridge_edges = {frozenset(e) for e in bridges}
        assert all(len(ns) != 2 or any(frozenset((v, w)) not in bridge_edges for w in ns)
                   for v, ns in enumerate(g))
        block_codes.update(encode(induced(g, vertices)) for vertices in blocks)
        for x in range(len(g)):
            for h, core_beta in prepared:
                core_boundary = sum(v > 0 for v in core_beta)
                for root in range(len(h)):
                    if len(g[x]) + len(h[root]) > 3:
                        continue
                    if len(h) == 2 and len(g[x]) == 1:
                        attempts['suppressed_bridge_subdivisions'] += 1
                        continue
                    glued = attach(g, h, x, root)
                    predicted = max(beta[x] - len(h[root]), core_beta[root] - len(g[x]))
                    assert root_score(glued, x) == predicted
                    attempts['all_vertex_root_attachments_with_fresh_root_BFS'] += 1
                    new_boundary = boundary + core_boundary - int(beta[x] > 0) \
                        - int(core_beta[root] > 0) + int(predicted > 0)
                    if new_boundary <= 6:
                        assert len(glued) <= 18
                        candidates.add(encode(glued))
                        attempts['attachments_retained'] += 1
        for a, b in bridges:
            g2 = [set(ns) for ns in g]
            branch, leaf = len(g2), len(g2) + 1
            g2[a].remove(b)
            g2[b].remove(a)
            g2.extend(({a, b, leaf}, {branch}))
            g2[a].add(branch)
            g2[b].add(branch)
            new_boundary = sum(x > 0 for x in scores(g2))
            assert new_boundary == boundary + 1
            attempts['all_bridge_branchings_with_full_BFS'] += 1
            if new_boundary <= 6:
                candidates.add(encode(g2))
                attempts['bridge_branchings_retained'] += 1
    assert set(canonical(block_codes, args.labelg)) <= palette
    images = set(canonical(sorted(candidates), args.labelg))
    assert images <= known
    assert palette <= known
    # Each non-palette state is explicitly reached from a smaller catalogue
    # state. This gives a well-founded generation certificate as well as closure.
    assert known <= images | palette
    base = HERE.parents[1]
    experiments = base / 'experiments'
    if not experiments.is_dir():
        experiments = base / 'five_boundary_research' / 'experiments'
    old = json.loads((experiments /
                      'reduced_kernels.json').read_text())
    old_subcubic = [r['graph6'].encode() for r in old if max(map(len, decode(r['graph6']))) <= 3]
    original_set = set(canonical(old_subcubic, args.labelg))
    new_low = {r['graph6'].encode() for r in rows if r['boundary_size'] <= 5}
    assert original_set == new_low
    report = {
        'all_passed': True, 'kernels_at_most_six': len(known),
        'kernels_exactly_six': sum(r['boundary_size'] == 6 for r in rows),
        'maximum_reduced_order': max(r['order'] for r in rows),
        'order_eighteen_kernels': sum(r['order'] == 18 for r in rows),
        'core_palette_size': len(palette), 'original_at_most_five_catalogue_matches': len(new_low),
        'attempts': dict(attempts), 'distinct_labeled_retained_candidates': len(candidates),
        'distinct_canonical_retained_candidates': len(images),
        'counts_by_boundary_and_order': {f'{b},{n}': count for (b, n), count in sorted(counts.items())},
        'all_core_blocks_in_proved_palette': True,
        'every_nonseed_reached_from_smaller_catalogue_graph': True,
        'seconds': round(time.monotonic() - started, 3),
        'scope': 'Exact full-vertex/full-bridge finite closure, fresh graph scores, root-gluing checks, reducedness, and exact nauty isomorphism. The mathematical core/order bounds and block-generation induction are separate proofs.',
    }
    (HERE / 'subcubic_kernel_closure_independent_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
