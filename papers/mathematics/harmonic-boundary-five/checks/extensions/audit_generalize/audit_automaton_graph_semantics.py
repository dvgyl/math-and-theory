#!/usr/bin/env python3
"""Reconstruct accepted automaton walks as graphs, then check fresh BFS scores.

The graph realization, degree accounting, state orientation, and boundary
calculation are independent of the automaton's local update implementation.
The generator supplies only its proposed finite transitions.  This is a
finite semantic audit, not a substitute for the all-order coverage proof.
"""

from collections import Counter, defaultdict, deque
from copy import deepcopy
from pathlib import Path
import importlib.util
import json
import random
import time


DIRECTORY = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    'audited_automaton', DIRECTORY.parent / 'two_tree_equality' / 'path_core_automaton.py')
AUTOMATON = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUTOMATON)


def edge(a, b):
    return tuple(sorted((a, b)))


class Realization:
    def __init__(self):
        self.adj = []
        self.triangles = []
        self.multiplicities = {}
        self.live = None
        self.weight = 0

    def vertex(self):
        self.adj.append(set())
        return len(self.adj) - 1

    def join(self, a, b):
        self.adj[a].add(b)
        self.adj[b].add(a)

    def ears(self, a, b, count):
        for _ in range(count):
            c = self.vertex()
            self.join(c, a)
            self.join(c, b)

    def requirement(self, v):
        requirements = [2 + t for e, t in self.multiplicities.items() if v in e]
        for triangle in self.triangles:
            if v not in triangle:
                continue
            a, b = (x for x in triangle if x != v)
            if self.multiplicities[edge(a, b)] >= 2:
                requirements.append(2 + self.multiplicities[edge(v, a)]
                                    + self.multiplicities[edge(v, b)])
        return max(requirements)

    def orient(self, a, b, expected):
        key = lambda v: (len(self.adj[v]), min(7, self.requirement(v)))
        a, b = sorted((a, b), key=key)
        computed = (*key(a), *key(b), self.multiplicities[edge(a, b)])
        assert computed == expected, (computed, expected)
        self.live = a, b

    @classmethod
    def initial(cls, entry):
        state, weight, (qa, qb, q) = entry
        x = cls()
        a, u, v = (x.vertex() for _ in range(3))
        for b, c in ((a, u), (a, v), (u, v)):
            x.join(b, c)
        x.triangles.append((a, u, v))
        for b, c, ears, final in ((a, u, qa, 1 + qa), (a, v, qb, 1 + qb),
                                  (u, v, q, 2 + q)):
            x.ears(b, c, ears)
            x.multiplicities[edge(b, c)] = final
        x.weight = weight
        x.orient(u, v, state)
        return x

    def step(self, q1, q2, continuation, weight, expected=None):
        x = deepcopy(self)
        a, b = x.live
        c = x.vertex()
        x.join(a, c)
        x.join(b, c)
        x.triangles.append((a, b, c))
        x.ears(a, c, q1)
        x.ears(b, c, q2)
        x.multiplicities[edge(a, c)] = 1 + q1 + (continuation == 1)
        x.multiplicities[edge(b, c)] = 1 + q2 + (continuation == 2)
        x.weight += weight
        if continuation:
            x.orient(a if continuation == 1 else b, c, expected)
        else:
            x.live = None
        return x

    def check_final(self, stats):
        assert self.live is None
        n = len(self.adj)
        assert sum(map(len, self.adj)) == 4 * n - 6
        distances = []
        for source in range(n):
            d = [-1] * n
            d[source] = 0
            queue = deque([source])
            while queue:
                v = queue.popleft()
                for w in self.adj[v]:
                    if d[w] == -1:
                        d[w] = d[v] + 1
                        queue.append(w)
            assert min(d) == 0
            distances.append(d)
        boundary = []
        for v in range(n):
            beta = max(sum(distances[v][target] - distances[w][target]
                           for w in self.adj[v]) for target in range(n))
            if beta > 0:
                boundary.append(v)
                assert len(self.adj[v]) <= 4
            else:
                assert 5 <= len(self.adj[v]) <= 6
        assert 2 * len(boundary) - n == self.weight
        degree_two = {v for v in range(n) if len(self.adj[v]) == 2}
        retained = set(range(n)) - degree_two
        assert retained == {v for tri in self.triangles for v in tri}
        assert all(not (self.adj[v] & degree_two) for v in degree_two)
        stats['completed_graphs'] += 1
        stats['max_order'] = max(stats['max_order'], n)
        stats['max_core_triangles'] = max(stats['max_core_triangles'], len(self.triangles))
        if self.weight == 4:
            stats['equality_walks'] += 1
            assert n % 2 == 0 and len(boundary) == n // 2 + 2


def main():
    started = time.monotonic()
    states, initial, transitions, terminal = AUTOMATON.build()
    outgoing, endings = defaultdict(list), defaultdict(list)
    for s, t, w, details in transitions:
        outgoing[s].append((t, w, details))
    for s, w, details in terminal:
        endings[s].append((w, details))
    stats = Counter()
    frontier = [(s, Realization.initial(entry)) for entry in initial for s in [entry[0]]]
    for depth in range(6):
        next_frontier = []
        for state, graph in frontier:
            for w, (q1, q2) in endings[state]:
                graph.step(q1, q2, 0, w).check_final(stats)
            if depth < 5:
                for dest, w, (q1, q2, cont) in outgoing[state]:
                    next_frontier.append((dest, graph.step(q1, q2, cont, w, dest)))
        frontier = next_frontier
    stats['exhaustive_completed_walks_through_five_ordinary_steps'] = stats['completed_graphs']
    good = {s for s, choices in endings.items() if choices}
    changed = True
    while changed:
        changed = False
        for s, t, w, details in transitions:
            if t in good and s not in good:
                good.add(s)
                changed = True
    rng = random.Random(20261102)
    usable_initial = [x for x in initial if x[0] in good]
    for _ in range(100):
        entry = rng.choice(usable_initial)
        state, graph = entry[0], Realization.initial(entry)
        for _ in range(rng.randint(20, 100)):
            choices = [x for x in outgoing[state] if x[0] in good]
            if not choices:
                break
            dest, w, (q1, q2, cont) = rng.choice(choices)
            graph = graph.step(q1, q2, cont, w, dest)
            state = dest
        while not endings[state]:
            dest, w, (q1, q2, cont) = next(x for x in outgoing[state] if x[0] in good)
            graph = graph.step(q1, q2, cont, w, dest)
            state = dest
        w, (q1, q2) = rng.choice(endings[state])
        graph.step(q1, q2, 0, w).check_final(stats)
    stats['long_random_walks'] = 100
    report = {'all_passed': True, 'counts': dict(stats), 'seed': 20261102,
              'seconds': round(time.monotonic() - started, 3),
              'scope': 'Fresh graph realizations and exact all-pairs BFS boundary scores; finite audit of automaton semantics, not an all-order proof.'}
    (DIRECTORY / 'automaton_graph_semantics_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
