#!/usr/bin/env python3
"""Exact standard-library checks of the 64-point spectral tile in F_2^9.

Vectors of F_2^9 are integers 0..511 (bit j is coordinate j + 1, so x + 64 i encodes (x, i)
in F_2^6 x F_2^3); addition is XOR and the character pairing is the parity of popcount(u & x).
The set E is rebuilt from the subspace bases in Table 1 of the manuscript and compared with
construction.json. Every complement of E is then enumerated twice: by a clique search on the
allowed shifts, and by an exact-cover search that uses no difference-set criterion.
"""
import json
from itertools import combinations, product
from pathlib import Path

BASES = [(11, 22, 37), (7, 26, 43), (14, 23, 35), (13, 22, 39),
         (7, 26, 43), (11, 21, 39), (15, 19, 38), (11, 23, 38)]
C = [0, 1, 2, 4, 8, 16, 32, 63]
G = range(512)


def span(basis):
    out = {0}
    for b in basis:
        out |= {x ^ b for x in out}
    return out


def chi(u, x):
    return -1 if bin(u & x).count('1') % 2 else 1


def tiles(a, b):
    return len({x ^ y for x in a for y in b}) == len(a) * len(b) == 512


def subspaces(n, k):
    """All k-dimensional subspaces of F_2^n, once each, via reduced row echelon form."""
    for pivots in combinations(range(n), k):
        free = [[j for j in range(p) if j not in pivots] for p in pivots]
        for bits in product(*[range(1 << len(f)) for f in free]):
            yield [(1 << p) | sum(1 << j for t, j in enumerate(f) if bits[r] >> t & 1)
                   for r, (p, f) in enumerate(zip(pivots, free))]


def main():
    spaces = [span(b) for b in BASES]
    assert all(len(s) == 8 for s in spaces)
    E = sorted(x + 64 * i for i, s in enumerate(spaces) for x in s)
    spectrum = sorted(c + 64 * w for w in range(8) for c in C)
    T = sorted(C)
    data = json.loads((Path(__file__).resolve().parent / 'construction.json').read_text())
    assert E == sorted(data['E']) and spectrum == sorted(data['spectrum'])
    assert T == sorted(data['nonlinear_complement'])
    assert len(set(E)) == len(set(spectrum)) == 64

    pairs = list(combinations(spectrum, 2))
    assert all(sum(chi(a ^ b, x) for x in E) == 0 for a, b in pairs)
    assert tiles(E, T)
    Eset = set(E)
    assert not [v for v in G if v and all(x ^ v in Eset for x in E)]

    sums = {x ^ y for x in E for y in E}
    allowed = sorted(set(G) - sums)
    D = sorted({a ^ b for a, b in combinations(C, 2)})
    assert allowed == D and len(D) == 28
    assert {bin(d).count('1') for d in D} == {1, 2, 5, 6}

    # The allowed-shift graph is the line graph of K_8 on C.
    label = {a ^ b: frozenset((a, b)) for a, b in combinations(C, 2)}
    for x, y in combinations(D, 2):
        assert ((x ^ y) in label) == (len(label[x] & label[y]) == 1)

    # Clique search: complements containing 0 are 0 together with 7 pairwise-adjacent shifts.
    cliques = []

    def extend(chosen, candidates):
        if len(chosen) == 8:
            cliques.append(frozenset(chosen))
            return
        for i, c in enumerate(candidates):
            rest = [d for d in candidates[i + 1:] if c ^ d in label]
            if len(chosen) + 1 + len(rest) >= 8:
                extend(chosen + [c], rest)

    extend([0], D)
    stars = {frozenset(c ^ t for t in C) for c in C}
    assert set(cliques) == stars
    translates = {frozenset(t ^ g for t in T) for g in G}
    by_clique = {frozenset(b ^ g for b in B) for B in cliques for g in G}
    assert by_clique == translates and len(translates) == 512

    # Exact cover: partitions of G into translates E + b, with no difference criterion.
    full = (1 << 512) - 1
    mask = {b: sum(1 << (e ^ b) for e in E) for b in G}
    found = set()

    def cover(covered, chosen):
        if covered == full:
            found.add(frozenset(chosen))
            return
        free = ~covered & full
        g = (free & -free).bit_length() - 1
        for e in E:
            b = g ^ e
            if not mask[b] & covered:
                cover(covered | mask[b], chosen + [b])

    cover(0, [])
    assert found == translates
    assert all(not [v for v in G if v and all(b ^ v in B for b in B)] for B in found)

    count = 0
    for rows in subspaces(9, 3):
        count += 1
        assert any(h in sums and h for h in span(rows))
    assert count == 788035
    print(json.dumps({
        'status': 'PASS', 'points': len(E), 'spectrum_pairs': len(pairs),
        'allowed_shifts': len(D), 'complements': len(found), 'periodic_complements': 0,
        'three_dimensional_subspaces_checked': count}, indent=2))


if __name__ == '__main__':
    main()
