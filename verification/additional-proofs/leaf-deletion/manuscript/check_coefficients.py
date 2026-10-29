#!/usr/bin/env python3
"""Exact finite check for the leaf-deletion witness; standard library only."""
import json

if not __debug__:
    raise SystemExit("Optimization disables certificate checks; rerun without optimization.")


def power(a, n):
    # Coefficients are in ascending degree order; a[0] = 1.
    assert a[0] == 1 and n > 0
    q = [1]
    for j in range(1, (len(a) - 1) * n + 1):
        s = sum(((n + 1) * i - j) * a[i] * q[j - i]
                for i in range(1, min(j, len(a) - 1) + 1))
        t, r = divmod(s, j)
        assert r == 0
        q.append(t)
    return q


def at(a, j):
    return a[j] if 0 <= j < len(a) else 0


def check(a, m):
    assert len(a) == 6622 and a[-1] == 1
    assert all(t >= 0 for t in a)
    assert all(a[j] <= a[j + 1] for j in range(m))
    # Include the last coefficient versus the following zero.
    assert all(at(a, j + 1) <= a[j] for j in range(m, len(a)))
    assert a[m - 1] < a[m] and a[m + 1] < a[m]
    assert a[m] > 0


def main():
    f = power([1, 10, 45, 120, 210, 252, 210, 120, 46, 11, 1], 662)
    g = power([1, 10, 45, 120, 210, 252, 210, 120, 45, 11, 1], 662)
    h = power([1, 1], 5958)
    assert (len(f), len(g), len(h)) == (6621, 6621, 5959)
    p = [at(f, j - 1) + at(g, j) - at(h, j) for j in range(6622)]
    q = [at(f, j - 1) + at(f, j) + at(g, j) for j in range(6622)]
    check(p, 3314)
    check(q, 3315)
    assert p[0] == 0 and p[1] > 0 and q[0] == 2
    assert sum(p) == 1026**662 + 1025**662 - 2**5958
    assert sum(q) == 2 * 1026**662 + 1025**662
    print(json.dumps({"status": "PASS", "inner_modes": [3314, 3315],
                      "graph_modes": [3976, 3978], "graph_orders": [7283, 7284],
                      "both_unimodal": True, "initial_zeros": [663, 663]}, indent=2))


if __name__ == "__main__":
    main()
