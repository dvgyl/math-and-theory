#!/usr/bin/env python3
"""Independent direct triple-of-hyperedges checker and certificate validator.

Freeness enumerates triples of hyperedges and intersection representatives;
it does not import verify.py or use the own-pair structural theorem.
"""
import argparse
import itertools as it
import json
from pathlib import Path


def validate_input(data):
    n, raw = data.get("n"), data.get("edges")
    if type(n) is not int or n < 0 or not isinstance(raw, list):
        raise ValueError("invalid input header")
    es = []
    for e in raw:
        if (not isinstance(e, list) or len(e) != 3
            or any(type(v) is not int or v < 0 or v >= n for v in e)
            or len(set(e)) != 3):
            raise ValueError("invalid hyperedge")
        es.append(tuple(sorted(e)))
    if len(es) != len(set(es)):
        raise ValueError("duplicate hyperedge")
    return n, tuple(sorted(es))


def edge_triple_triangle(edges):
    sets = [frozenset(e) for e in edges]
    for i, j, k in it.combinations(range(len(sets)), 3):
        for x in sets[i] & sets[j]:
            for y in sets[j] & sets[k]:
                if x == y:
                    continue
                for z in sets[k] & sets[i]:
                    if z != x and z != y:
                        return {"edge_ids": [i, j, k], "intersections": [x, y, z]}
    return None


def check(data, certificate):
    n, edges = validate_input(data)
    if certificate.get("n") != n or certificate.get("m") != len(edges):
        raise ValueError("certificate parameters disagree")
    if certificate.get("canonical_edges") != [list(e) for e in edges]:
        raise ValueError("edge ID order disagrees")
    triangle = edge_triple_triangle(edges)
    if triangle is not None:
        raise ValueError("input is not Berge-triangle-free")
    expected = set(it.combinations(range(n), 3)) - set(edges)
    seen = set()
    for item in certificate.get("augmentation_certificates", []):
        raw_added = item.get("added")
        core = item.get("core")
        ids = item.get("old_edge_ids")
        if not isinstance(raw_added, list) or len(raw_added) != 3:
            raise ValueError("bad added triple")
        added = tuple(raw_added)
        if added not in expected or added in seen:
            raise ValueError("unexpected or duplicated addition")
        if (not isinstance(core, list) or len(core) != 3 or len(set(core)) != 3
            or any(type(v) is not int or not 0 <= v < n for v in core)):
            raise ValueError("invalid core")
        if (not isinstance(ids, list) or len(ids) != 2 or ids[0] == ids[1]
            or any(type(i) is not int or not 0 <= i < len(edges) for i in ids)):
            raise ValueError("invalid old edge IDs")
        x, w, y = core
        if not ({x, w} <= set(edges[ids[0]]) and {w, y} <= set(edges[ids[1]])
                and {x, y} <= set(added)):
            raise ValueError("certificate incidence failure")
        seen.add(added)
    if seen != expected:
        raise ValueError("certificate omits a missing triple")
    return {"n": n, "m": len(edges), "free": True, "saturated": True,
            "augmentations_independently_checked": len(seen)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(json.loads(args.input.read_text()),
                           json.loads(args.certificate.read_text())), sort_keys=True))


if __name__ == "__main__":
    main()
