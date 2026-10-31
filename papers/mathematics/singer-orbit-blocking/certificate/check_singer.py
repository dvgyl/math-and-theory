#!/usr/bin/env python3
"""Exact standard-library checks for Singer-orbit blocking sets in PG(2,13).

Usage:  python3 -I check_singer.py WITNESS.json

The script rebuilds PG(2,13) from the field F_13[t]/(t^3 + t + 6), checks the Singer cycle,
the fixed-point-free subgroup H of order three and the reduction of H-invariant sets to 61
orbit variables, checks the 21-point witness and its conjugacy to the Blokhuis-Brouwer-Wilbrink
set, and runs an exhaustive search showing that no H-invariant set meets every line in between
one and four points. It prints a JSON summary and exits with status 1 on any failure.
"""
import json
import sys
from itertools import product

Q = 13


def fail(message):
    print(json.dumps({"status": "FAIL", "reason": message}))
    sys.exit(1)


def check(condition, message):
    if not condition:
        fail(message)


def mul(a, b):
    """Multiply coefficient triples (1, t, t^2) modulo t^3 + t + 6."""
    c = [0] * 5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % Q
    for k in (4, 3):  # t^k = t^(k-3) * (-t - 6)
        c[k - 2] = (c[k - 2] - c[k]) % Q
        c[k - 3] = (c[k - 3] - 6 * c[k]) % Q
        c[k] = 0
    return tuple(c[:3])


def normalize(v):
    lead = next(x for x in v if x % Q)
    inv = pow(lead, Q - 2, Q)
    return tuple(x * inv % Q for x in v)


def mat_vec(m, v):
    return tuple(sum(m[i][j] * v[j] for j in range(3)) % Q for i in range(3))


def mat_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) % Q for j in range(3)] for i in range(3)]


def geometry():
    theta = (0, 1, 0)
    powers = [(1, 0, 0)]
    for _ in range(Q ** 3 - 2):
        powers.append(mul(powers[-1], theta))
    check(mul(powers[-1], theta) == (1, 0, 0), "theta^2196 != 1")
    check(len(set(powers)) == Q ** 3 - 1, "theta is not primitive")
    points = [normalize(p) for p in powers[:183]]
    check(len(set(points)) == 183, "the 183 powers are not distinct points")
    all_points = {normalize(v) for v in product(range(Q), repeat=3) if any(v)}
    check(set(points) == all_points, "the powers of theta miss a point")
    index = {p: i for i, p in enumerate(points)}
    # theta^183 is a scalar, so multiplication by theta has projective order 183.
    check(normalize(powers[183]) == (1, 0, 0), "theta^183 is not a scalar")
    lines = sorted(all_points)
    incidence = {w: frozenset(index[p] for p in points
                              if sum(a * b for a, b in zip(w, p)) % Q == 0) for w in lines}
    check(all(len(s) == 14 for s in incidence.values()), "a line does not have 14 points")
    base = sorted(index[p] for p in points if p[0] == 0)
    expected = [1, 2, 4, 17, 24, 29, 43, 77, 83, 87, 120, 138, 155, 176]
    check(base == expected, f"base line {base}")
    translates = {frozenset((d + t) % 183 for d in base) for t in range(183)}
    check(translates == set(incidence.values()), "line translates differ from coordinate lines")
    # H = <sigma^61>: fixed-point-free of order three.
    check(all((i + 61) % 183 != i for i in range(183)), "sigma^61 has a fixed point")
    return points, index, base, incidence


def orbit_rows(base):
    rows = []
    for t in range(61):
        r = [0] * 61
        for d in base:
            r[(d + t) % 61] += 1
        rows.append(r)
    for t in range(61):
        check(sorted(rows[t]) == [0] * 48 + [1] * 12 + [2], "unexpected row weights")
        for u in range(61):
            dot = sum(a * b for a, b in zip(rows[t], rows[u]))
            check(dot == (16 if t == u else 3), "M M^T != 13 I + 3 J")
    return rows


def witness_checks(witness, points, index, incidence):
    orbits = witness["orbits"]
    selected = {j + 61 * k for j in orbits for k in range(3)}
    check(len(selected) == 21, "the witness does not have 21 points")
    coords = sorted(points[i] for i in selected)
    check(coords == sorted(tuple(p) for p in witness["points"]), "witness coordinates differ")
    check(all((i + 61) % 183 in selected for i in selected), "witness is not H-invariant")
    sizes = {}
    for s in incidence.values():
        k = len(s & selected)
        sizes[k] = sizes.get(k, 0) + 1
    check(0 not in sizes, "witness is not blocking")
    check(max(sizes) == 5, "witness maximum intersection is not five")
    check(sizes == {1: 126, 2: 36, 4: 9, 5: 12}, f"intersection distribution {sizes}")
    for i in selected:
        check(any(len(s & selected) == 1 and i in s for s in incidence.values()),
              "a witness point has no tangent")
    # Conjugacy to the Blokhuis-Brouwer-Wilbrink set.
    cubes_m1 = [a for a in range(1, Q) if pow(a, 3, Q) == Q - 1]
    cubes_1 = [a for a in range(1, Q) if pow(a, 3, Q) == 1]
    bbw = {(1, 0, 0), (0, 1, 0), (0, 0, 1)}
    for a in cubes_m1:
        bbw |= {(1, a, 0), (0, 1, a), (a, 0, 1)}
    bbw |= {(b, c, 1) for b in cubes_1 for c in cubes_1}
    bbw = {normalize(p) for p in bbw}
    check(len(bbw) == 21, "BBW set does not have 21 points")
    A = [[0, 12, 0], [0, 0, 4], [12, 0, 0]]
    A3 = mat_mul(A, mat_mul(A, A))
    check(A3 == [[4, 0, 0], [0, 4, 0], [0, 0, 4]], "A^3 != 4I")
    check(all(pow(x, 3, Q) != 4 for x in range(Q)), "4 is a cube")
    check({normalize(mat_vec(A, p)) for p in bbw} == bbw, "BBW set is not A-invariant")
    K = [[1, 7, 8], [0, 10, 1], [0, 4, 12]]
    # Multiplication by theta^61 in the basis 1, theta, theta^2.
    t61 = [[0] * 3 for _ in range(3)]
    p61 = (1, 0, 0)
    for _ in range(61):
        p61 = mul(p61, (0, 1, 0))
    for j, e in enumerate([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
        col = mul(p61, e)
        for i in range(3):
            t61[i][j] = col[i]
    check(mat_mul(K, [[7 * x % Q for x in row] for row in A]) == mat_mul(t61, K), "K(7A) != T K")
    image = {normalize(mat_vec(K, p)) for p in bbw}
    check(image == set(coords), "K does not map the BBW set onto the witness")
    return {"points": 21, "orbits": orbits, "intersection_distribution": dict(sorted(sizes.items())),
            "tangent_at_every_point": True, "bbw_conjugator_checked": True}


def exhaustive_search(rows):
    """Depth-first search with unit propagation over the 61 orbit variables, orbit 0 chosen."""
    members = [[j for j in range(61) if rows[t][j]] for t in range(61)]
    nodes = 0

    def propagate(value):
        changed = True
        while changed:
            changed = False
            for t in range(61):
                ones = sum(rows[t][j] for j in members[t] if value[j] == 1)
                free = [j for j in members[t] if value[j] is None]
                if ones > 4 or (ones == 0 and not free):
                    return False
                if ones == 0 and len(free) == 1:
                    value[free[0]] = 1
                    changed = True
                for j in free:
                    if value[j] is None and ones + rows[t][j] > 4:
                        value[j] = 0
                        changed = True
        return True

    def search(value):
        nonlocal nodes
        nodes += 1
        if not propagate(value):
            return None
        best = None
        for t in range(61):
            if all(value[j] != 1 for j in members[t]):
                free = [j for j in members[t] if value[j] is None]
                if best is None or len(free) < len(best):
                    best = free
        if best is None:
            return value
        excluded = []
        for j in best:
            child = list(value)
            child[j] = 1
            for e in excluded:
                child[e] = 0
            found = search(child)
            if found is not None:
                return found
            excluded.append(j)
        return None

    start = [None] * 61
    start[0] = 1
    solution = search(start)
    check(solution is None, "found an H-invariant set with all intersections in [1, 4]")
    return nodes


def main():
    if len(sys.argv) != 2:
        fail("usage: check_singer.py WITNESS.json")
    with open(sys.argv[1]) as stream:
        witness = json.load(stream)
    points, index, base, incidence = geometry()
    rows = orbit_rows(base)
    report = witness_checks(witness, points, index, incidence)
    nodes = exhaustive_search(rows)
    print(json.dumps({"status": "PASS", "points": 183, "lines": 183, "base_line": base,
                      "orbit_rows": 61, "witness": report,
                      "cap_four_search": {"result": "no solution", "nodes": nodes}},
                     indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
