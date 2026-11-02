#!/usr/bin/env python3
"""Audit deterministic cycle parameters in the odd equality grammar."""

from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent


def freeze(x):
    return tuple(map(freeze, x)) if isinstance(x, list) else x


def main():
    data = json.loads((HERE.parent / 'two_tree_equality' / 'extremal_grammars.json').read_text())
    odd = data['targets']['5']
    states = list(map(freeze, odd['states']))
    ids = {s: i for i, s in enumerate(states)}
    rules = list(map(freeze, odd['rules']))
    roots = list(map(freeze, odd['final_rules']))
    adjacency = defaultdict(set)
    for dest, children, weight, tag, reduced in rules:
        if len(children) == 1:
            adjacency[ids[dest]].add(ids[children[0]])
    counter = 0
    stack, on_stack, number, low, components = [], set(), {}, {}, []

    def visit(v):
        nonlocal counter
        number[v] = low[v] = counter
        counter += 1
        stack.append(v)
        on_stack.add(v)
        for w in adjacency[v]:
            if w not in number:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], number[w])
        if low[v] == number[v]:
            part = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                part.append(w)
                if w == v:
                    break
            components.append(tuple(sorted(part)))

    for v in range(len(states)):
        if v not in number:
            visit(v)
    component = {v: c for c, part in enumerate(components) for v in part}
    cyclic = {c for c, part in enumerate(components)
              if len(part) > 1 or part[0] in adjacency[part[0]]}
    exits, internal = defaultdict(list), defaultdict(list)
    for rule in rules:
        dest, children, weight, tag, reduced = rule
        c = component[ids[dest]]
        cs = tuple(component[ids[child]] for child in children)
        if len(cs) == 1 and cs[0] == c:
            internal[c].append(rule)
        else:
            assert c not in cs
            exits[c].append(cs)
    cycles = []
    for c in cyclic:
        counts = Counter(ids[r[0]] for r in internal[c])
        assert counts == Counter({v: 1 for v in components[c]})
        added = []
        for dest, children, weight, tag, reduced in internal[c]:
            assert tag[0] == 'extend' and reduced == 0
            added.append(1 + tag[2] + tag[3])
        cycles.append({'states': components[c], 'rules': len(internal[c]),
                       'vertices_per_full_cycle': sum(added)})

    @lru_cache(None)
    def parameters(c):
        assert exits[c]
        return int(c in cyclic) + max(sum(parameters(d) for d in child_components)
                                     for child_components in exits[c])

    def state_parameters(s):
        return parameters(component[ids[s]])

    general_max = max(state_parameters(a) + state_parameters(b) for a, b, w, tag in roots)
    branch_roots = [r for r in roots if r[0][1][0] + r[1][1][0] == 3]
    branch_max = max(state_parameters(a) + state_parameters(b) for a, b, w, tag in branch_roots)
    leaf_states = {dest for dest, children, w, tag, reduced in rules if not children}
    path_parameters = []
    for a, b, w, tag in roots:
        if a[0] == b[0] == 1:
            if a in leaf_states:
                path_parameters.append(state_parameters(b))
            if b in leaf_states:
                path_parameters.append(state_parameters(a))
    path_max = max(path_parameters)
    assert not any(tag[0] == 'triangle' for dest, children, w, tag, reduced in rules)
    max_k = max(s[1][0] for s in states)
    max_root_degree = max(a[1][0] + b[1][0] for a, b, w, tag in roots)
    assert max_k == 2 and max_root_degree == 3
    assert general_max == 6 and branch_max == 5 and path_max == 3
    report = {
        'all_passed': True,
        'cyclic_unary_components': sorted(cycles, key=lambda x: x['states']),
        'all_cyclic_components_are_deterministic': True,
        'maximum_parameters_for_arbitrary_root': general_max,
        'maximum_parameters_with_root_at_a_trivalent_core_edge': branch_max,
        'maximum_parameters_for_path_core_rooted_next_to_an_end': path_max,
        'maximum_pending_core_triangles': max_k,
        'maximum_terminal_core_edge_degree': max_root_degree,
        'triangle_join_rules': 0,
        'scope': 'Finite deterministic-cycle audit supporting an O(n^4) upper bound once the proved graph-grammar correspondence and the stated root choice are applied. This checker does not claim an isomorphism counting formula or a matching lower bound.',
    }
    (HERE / 'grammar_growth_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
