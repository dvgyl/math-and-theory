#!/usr/bin/env python3
"""Independent finite audit of the unlabelled odd two-tree counting proof.

Only the previously independently certified compact state table is read.
No counting/generation code is imported.  We allow all ear multiplicities
0..6 (larger values violate a root degree bound immediately), compute
the final degrees and triangle requirements directly, and compare the
complete accepted lists with the claimed canonical cases.
"""

import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "two_tree_equality" / "compact_odd_grammar.json"


def status(degree, requirement):
    if 3 <= degree <= 5 and requirement > degree:
        return 1
    if 5 <= degree <= 6 and requirement <= degree:
        return -1
    return None


def requirement(endpoint, multiplicity):
    _, a, b = endpoint
    return max(a, b + multiplicity)


def unpack(row):
    k, *r = row["root_state"]
    return k, (tuple(r[:3]), tuple(r[3:])), row["weight"]


def main():
    raw = SOURCE.read_bytes()
    rows = {s["id"]: s for s in json.loads(raw)["states"]}
    states = {i: unpack(s) for i, s in rows.items()}
    assert [i for i in rows if rows[i]["leaves"] == 1] == list(range(10))
    edge, triangle, branch, double_branch = [], [], [], []
    tested = {"edge": 0, "triangle": 0, "branch": 0, "double_branch": 0}

    for i in range(10):
        k, ends, weight = states[i]
        assert k == 1
        for flip, q in itertools.product(range(2), range(7)):
            tested["edge"] += 1
            m = 2 + q
            deg = [ends[j][0] + ends[j ^ flip][0] - 1 + q for j in range(2)]
            req = [max(requirement(ends[j], m), requirement(ends[j ^ flip], m))
                   for j in range(2)]
            signs = [status(d, r) for d, r in zip(deg, req)]
            if None not in signs and 2 * weight + q + sum(signs) == 5:
                edge.append((i, flip, q, *signs))

        # At a triangle center, two identical components meet in u.
        # q ears lie on each old root; r ears lie on the third edge.
        for shared, q, r in itertools.product(range(2), range(7), range(7)):
            tested["triangle"] += 1
            eu, ev = ends[shared], ends[1 - shared]
            m = 2 + q
            du, dv = 2 * eu[0] + 2 * q, ev[0] + q + 1 + r
            ru = requirement(eu, m)
            if r > 0:
                # The central triangle is active opposite u iff r>0.
                ru = max(ru, 2 + m + m)
            # The edge opposite v is an old root of multiplicity >=2.
            rv = max(requirement(ev, m), 2 + m + (1 + r))
            su, sv = status(du, ru), status(dv, rv)
            if su is not None and sv is not None:
                if 2 * weight + 2 * q + r + su + 2 * sv == 5:
                    triangle.append((i, shared, q, r, su, sv))

    def check_three(ids, flips, q):
        comps = [states[i] for i in ids]
        assert all(c[0] == 1 for c in comps)
        m = 3 + q
        ds, rs = [], []
        for j in range(2):
            eps = [c[1][j ^ f] for c, f in zip(comps, flips)]
            ds.append(sum(e[0] for e in eps) - 2 + q)
            rs.append(max(requirement(e, m) for e in eps))
        signs = [status(d, r) for d, r in zip(ds, rs)]
        if None in signs:
            return None
        if sum(c[2] for c in comps) + q + sum(signs) != 5:
            return None
        return tuple(ds), tuple(rs), tuple(signs)

    for ids in itertools.combinations_with_replacement(range(10), 3):
        for flips, q in itertools.product(itertools.product(range(2), repeat=3), range(7)):
            tested["branch"] += 1
            result = check_three(ids, flips, q)
            if result is not None:
                aa = [j for j, i in enumerate(ids) if i in (0, 1)]
                bb = [j for j, i in enumerate(ids) if i in (3, 4, 6)]
                assert len(aa) == 2 and len(bb) == 1, (ids, flips, q, result)
                assert flips[aa[0]] == flips[aa[1]] != flips[bb[0]]
                assert q == 0 and result[0] == (6, 6) and result[2] == (-1, -1)
                branch.append((ids, flips, q))

    continuing = [i for i, row in rows.items()
                  if row["leaves"] == 2 and states[i][0] == 1]
    for a, b in itertools.combinations_with_replacement(range(10), 2):
        for c, flips, q in itertools.product(continuing,
                                            itertools.product(range(2), repeat=3),
                                            range(7)):
            tested["double_branch"] += 1
            result = check_three((a, b, c), flips, q)
            if result is not None:
                assert a in (0, 1) and b in (0, 1) and c == 12
                assert flips[0] == flips[1] != flips[2]
                assert q == 0 and result[0] == (6, 6) and result[2] == (-1, -1)
                double_branch.append(((a, b, c), flips, q))

    expected_edge = [(i, 0, 1, 1, -1) for i in (0, 1)]
    expected_edge += [(i, 1, 1, -1, -1) for i in (3, 4, 6)]
    expected_triangle = [(i, 1, 0, 0, -1, 1) for i in (0, 1)]
    expected_triangle += [(i, 0, 0, 0, 1, -1) for i in (3, 4)]
    expected_triangle += [(i, 0, 1, 0, -1, -1) for i in (3, 4, 6)]
    assert sorted(edge) == sorted(expected_edge), edge
    assert sorted(triangle) == sorted(expected_triangle), triangle
    assert len(branch) == 18 and len(double_branch) == 6
    report = {
        "status": "PASS",
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "checked_cases": tested,
        "edge_center_cases": edge,
        "triangle_center_cases": triangle,
        "one_branch_cases_including_root_flip": len(branch),
        "two_branch_cases_including_root_flip": len(double_branch),
        "all_third_edge_ear_multiplicities_forced_zero": True,
        "scope": "Exact finite center/branch equations; canonical isomorphism semantics audited separately."
    }
    dest = HERE / "odd_count_centers_audit.json"
    dest.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
