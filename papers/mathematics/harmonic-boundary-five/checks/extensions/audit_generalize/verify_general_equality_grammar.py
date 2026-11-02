#!/usr/bin/env python3
"""Independent closure and proof-certificate audit of the equality grammar.

No generator is imported. Local requirements are reconstructed from a
generic triangle whose one pending edge is a symbolic variable t>=2.
All raw productions, unary transitions, and terminal gluings are regenerated.
Exact potentials, rank-decreasing attainment certificates, productivity,
and the final slack-pruned grammars are then checked independently.
"""

from collections import Counter, defaultdict, deque
from itertools import product
from pathlib import Path
import json
import time


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'two_tree_equality'
NEG = -10**9


def frozen(value):
    return tuple(map(frozen, value)) if isinstance(value, list) else value


def canonical(k, x, y):
    def cap(z):
        d, a, b = z
        return d, min(a, 9), min(b, 7)
    a, b = sorted((cap(x), cap(y)))
    return k, *a, *b


def orientations(state):
    k, a, b = state[0], state[1:4], state[4:7]
    yield k, a, b
    if a != b:
        yield k, b, a


def endpoint_requirement(endpoint, multiplicity):
    return max(endpoint[1], endpoint[2] + multiplicity)


def classify(degree, requirement):
    if degree < requirement:
        return 1 if 3 <= degree <= 5 else None
    return -1 if 5 <= degree <= 8 else None


def triangle_requirements(edges, vertex):
    """Return A,B for max(A,B+t), from the distance-free local formula.

    Edge entries are positive integers, except one None denoting t>=2.
    The routine treats all three vertices uniformly. It does not use any
    of the generator's operation-specific requirement formulas.
    """
    a, b = (x for x in range(3) if x != vertex)
    incident = (edges[vertex][a], edges[vertex][b])
    constant, linear = NEG, NEG
    for value in incident:
        if value is None:
            linear = max(linear, 2)
        else:
            constant = max(constant, 2 + value)
    opposite = edges[a][b]
    if opposite is None or opposite >= 2:
        unknown = sum(value is None for value in incident)
        assert unknown <= 1
        amount = 2 + sum(value for value in incident if value is not None)
        if unknown:
            linear = max(linear, amount)
        else:
            constant = max(constant, amount)
    return constant, linear


def new_initial():
    for a, b in product(range(9), repeat=2):
        degree = 2 + a + b
        if not 3 <= degree <= 5:
            continue
        matrix = [[0, 1 + a, 1 + b], [1 + a, 0, None], [1 + b, None, 0]]
        forgotten, linear = triangle_requirements(matrix, 0)
        assert linear == NEG and classify(degree, forgotten) == 1
        r1, r2 = triangle_requirements(matrix, 1), triangle_requirements(matrix, 2)
        yield canonical(1, (2 + a, *r1), (2 + b, *r2)), a + b + 1, ('leaf', a, b)


def new_extensions(state):
    for side, (k, u, v) in enumerate(orientations(state)):
        for old_ears in range(9):
            du = u[0] + old_ears + 1
            if du > 7:
                continue
            old_mult = k + 1 + old_ears
            for closed_ears in range(9):
                dv = v[0] + old_ears + closed_ears + 1
                dw = 2 + closed_ears
                if dv > 8 or dw > 7:
                    continue
                closed_mult = 1 + closed_ears
                matrix = [[0, old_mult, None], [old_mult, 0, closed_mult],
                          [None, closed_mult, 0]]
                req_u = triangle_requirements(matrix, 0)
                req_v = triangle_requirements(matrix, 1)
                req_w = triangle_requirements(matrix, 2)
                assert req_v[1] == NEG
                sg = classify(dv, max(endpoint_requirement(v, old_mult), req_v[0]))
                if sg is None:
                    continue
                next_u = (du, max(endpoint_requirement(u, old_mult), req_u[0]), req_u[1])
                next_w = (dw, *req_w)
                yield canonical(1, next_u, next_w), old_ears + closed_ears + sg, \
                    ('extend', side, old_ears, closed_ears, sg, dv)


def new_merges(left, right):
    for side1, (k1, u, w1) in enumerate(orientations(left)):
        for side2, (k2, v, w2) in enumerate(orientations(right)):
            for ears1 in range(9):
                du = u[0] + ears1 + 1
                if du > 7:
                    continue
                mult1 = k1 + 1 + ears1
                for ears2 in range(9):
                    dv = v[0] + ears2 + 1
                    dw = w1[0] + w2[0] + ears1 + ears2
                    if dv > 7 or dw > 8:
                        continue
                    mult2 = k2 + 1 + ears2
                    matrix = [[0, None, mult1], [None, 0, mult2], [mult1, mult2, 0]]
                    req_u = triangle_requirements(matrix, 0)
                    req_v = triangle_requirements(matrix, 1)
                    req_w = triangle_requirements(matrix, 2)
                    assert req_w[1] == NEG
                    sg = classify(dw, max(endpoint_requirement(w1, mult1),
                                          endpoint_requirement(w2, mult2), req_w[0]))
                    if sg is None:
                        continue
                    x = (du, max(endpoint_requirement(u, mult1), req_u[0]), req_u[1])
                    y = (dv, max(endpoint_requirement(v, mult2), req_v[0]), req_v[1])
                    yield canonical(1, x, y), ears1 + ears2 + sg, \
                        ('triangle', side1, side2, ears1, ears2, sg, dw)
            degree1, degree2 = u[0] + v[0] - 1, w1[0] + w2[0] - 1
            if degree1 <= 7 and degree2 <= 7 and k1 + k2 <= 3:
                x = (degree1, max(u[1], v[1]), max(u[2], v[2]))
                y = (degree2, max(w1[1], w2[1]), max(w1[2], w2[2]))
                yield canonical(k1 + k2, x, y), 0, ('edge', side1, side2)


def new_finishes(left, right):
    for side1, (k1, u, v) in enumerate(orientations(left)):
        for side2, (k2, a, b) in enumerate(orientations(right)):
            if k1 + k2 > 4:
                continue
            for ears in range(9):
                degrees = u[0] + a[0] - 1 + ears, v[0] + b[0] - 1 + ears
                if max(degrees) > 8:
                    continue
                mult = k1 + k2 + ears
                required = (max(endpoint_requirement(u, mult), endpoint_requirement(a, mult)),
                            max(endpoint_requirement(v, mult), endpoint_requirement(b, mult)))
                signs = tuple(classify(d, r) for d, r in zip(degrees, required))
                if None not in signs:
                    yield ears + sum(signs), ('finish', side1, side2, ears, *signs, *degrees)


def consume(counter, item):
    assert counter[item] > 0, ('missing independently regenerated item', item)
    counter[item] -= 1
    if not counter[item]:
        del counter[item]


def main():
    started = time.monotonic()
    raw = json.loads((SOURCE / 'all_equality_grammar.json').read_text())
    compact = json.loads((SOURCE / 'extremal_grammars.json').read_text())
    layers = {r['leaves']: {tuple(s['state']) for s in r['states']} for r in raw['layers']}
    mu = {(r['leaves'], tuple(s['state'])): s['minimum_weight']
          for r in raw['layers'] for s in r['states']}
    assert mu == {(r['leaves'], tuple(r['state'])): r['minimum_weight']
                  for r in compact['all_minimum_potentials']}
    productions = Counter(map(frozen, raw['all_productions']))
    extensions = Counter(map(frozen, raw['all_extensions']))
    finals = Counter(map(frozen, raw['final_rules']))
    counts = Counter()
    for state, weight, tag in new_initial():
        assert state in layers[1]
        consume(productions, (1, state, (), weight, tag))
        counts['initial_productions'] += 1
    for leaves in (2, 3):
        for l1 in range(1, leaves):
            l2 = leaves - l1
            for s in layers[l1]:
                for t in layers[l2]:
                    for dest, weight, tag in new_merges(s, t):
                        assert dest in layers[leaves]
                        consume(productions, (leaves, dest, ((l1, s), (l2, t)), weight, tag))
                        counts['binary_productions'] += 1
    assert not productions
    for leaves, states in layers.items():
        for s in states:
            for dest, weight, tag in new_extensions(s):
                assert dest in states
                consume(extensions, (leaves, s, dest, weight, tag))
                counts['unary_productions'] += 1
    assert not extensions
    minimum_completion = 10**9
    for l1 in range(1, 4):
        for l2 in range(l1, 4):
            if l1 + l2 > 4:
                continue
            for s in layers[l1]:
                for t in layers[l2]:
                    for weight, tag in new_finishes(s, t):
                        total = mu[l1, s] + mu[l2, t] + weight
                        minimum_completion = min(minimum_completion, total)
                        assert total >= 4
                        counts['all_valid_terminal_gluings'] += 1
                        if total <= 5:
                            consume(finals, (l1, s, l2, t, weight, tag, total))
                            counts['terminal_gluings_with_minimum_weight_at_most_five'] += 1
    assert not finals and minimum_completion == 4

    rules = set()
    for leaves, dest, children, weight, tag in map(frozen, raw['all_productions']):
        rules.add(((leaves, dest), children, weight, tag))
    for leaves, source, dest, weight, tag in map(frozen, raw['all_extensions']):
        rules.add(((leaves, dest), ((leaves, source),), weight, tag))
    budget_rules = set()
    for dest, children, weight, tag in rules:
        reduced = sum(mu[c] for c in children) + weight - mu[dest]
        assert reduced >= 0
        counts['potential_inequalities'] += 1
        if reduced > 1:
            continue
        for budgets in product(range(2), repeat=len(children)):
            budget = reduced + sum(budgets)
            if budget <= 1:
                new_dest = (*dest, budget)
                new_children = tuple((*c, b) for c, b in zip(children, budgets))
                budget_rules.add((new_dest, new_children, weight, tag, reduced))

    certificates = {frozen(x['state']): x for x in compact['productivity_certificates']}
    assert len(certificates) == len(compact['productivity_certificates'])
    actual_cost = {}
    for state, proof in sorted(certificates.items(), key=lambda item: item[1]['rank']):
        rule = frozen(proof['rule'])
        assert rule in budget_rules and rule[0] == state
        dest, children, weight, tag, reduced = rule
        assert proof['rank'] == 1 + max((certificates[c]['rank'] for c in children), default=-1)
        assert all(c in actual_cost for c in children)
        cost = sum(actual_cost[c] for c in children) + weight
        assert cost == mu[state[:2]] + state[2]
        actual_cost[state] = cost
    assert all((*s, 0) in certificates for s in mu)
    by_dest = defaultdict(set)
    for rule in budget_rules:
        if all(c in certificates for c in rule[1]):
            assert rule[0] in certificates
            by_dest[rule[0]].add(rule)

    target_reports = {}
    for target in (4, 5):
        roots = []
        for l1, s, l2, t, weight, tag, total in map(frozen, raw['final_rules']):
            for b1, b2 in product(range(2), repeat=2):
                left, right = (l1, s, b1), (l2, t, b2)
                if total + b1 + b2 == target and left in certificates and right in certificates:
                    roots.append((left, right, weight, tag))
        reachable = {x for left, right, weight, tag in roots for x in (left, right)}
        queue = deque(reachable)
        accepted = set()
        while queue:
            state = queue.popleft()
            for rule in by_dest[state]:
                accepted.add(rule)
                for child in rule[1]:
                    if child not in reachable:
                        reachable.add(child)
                        queue.append(child)
        recorded = compact['targets'][str(target)]
        assert Counter(roots) == Counter(map(frozen, recorded['final_rules']))
        assert reachable == set(map(frozen, recorded['states']))
        assert accepted == set(map(frozen, recorded['rules']))
        interior, boundary = [], [2]
        for dest, children, weight, tag, reduced in accepted:
            if tag[0] == 'leaf':
                boundary.append(2 + tag[1] + tag[2])
            elif tag[0] in ('extend', 'triangle'):
                (boundary if tag[-2] == 1 else interior).append(tag[-1])
        for left, right, weight, tag in roots:
            for sign, degree in ((tag[4], tag[6]), (tag[5], tag[7])):
                (boundary if sign == 1 else interior).append(degree)
        assert max(interior) == recorded['maximum_interior_degree']
        assert max(boundary) == recorded['maximum_boundary_degree']
        tied = [x for x in reachable if x[1][1:4] == x[1][4:7]]
        assert not tied
        target_reports[target] = {
            'states': len(reachable), 'productions': len(accepted), 'terminal_choices': len(roots),
            'maximum_interior_degree': max(interior), 'maximum_boundary_degree': max(boundary),
            'equal_endpoint_summary_states': len(tied),
        }
    report = {
        'all_passed': True, 'counts': dict(counts),
        'state_counts_by_leaf_number': {l: len(s) for l, s in layers.items()},
        'minimum_valid_completion_weight': minimum_completion,
        'rank_checked_productivity_certificates': len(certificates),
        'all_minimum_potentials_attained': True,
        'productive_set_is_exact_least_fixed_point': True,
        'targets': target_reports, 'seconds': round(time.monotonic() - started, 3),
        'scope': 'Independent exhaustive finite closure, potential, attainment, and pruning verification. Generic symbolic triangle requirements replace the generator formulas. The graph-to-incidence-tree reduction remains a separate mathematical proof.',
    }
    (HERE / 'general_equality_grammar_independent_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
