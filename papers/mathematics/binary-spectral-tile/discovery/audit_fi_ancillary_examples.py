#!/usr/bin/env python3
"""Exact priority screen of public Ferguson--Iosevich JSON examples.

This is a literature/provenance check, not part of the central Lean proof.
Input is the public arXiv:2610.30712v1 source archive, fetched separately.
Every distinct 64-element integer array contained in [0,512) is interpreted
as a subset of F_2^9.  An explicit 3D subspace avoiding its nonzero
differences certifies a linear complement and rules out affine equivalence
to our tile without any linear complement.
"""
from pathlib import Path
import hashlib
import json
import tarfile


def find_cube(allowed):
    allowed_set = set(allowed)
    for index, a in enumerate(allowed):
        for b in allowed[index + 1:]:
            ab = a ^ b
            if ab not in allowed_set:
                continue
            plane = {0, a, b, ab}
            for c in allowed:
                if (c not in plane and (c ^ a) in allowed_set
                        and (c ^ b) in allowed_set and (c ^ ab) in allowed_set):
                    return [a, b, c]
    return None


def main():
    base = Path(__file__).resolve().parent
    source = base / "fi_2610.30712v1_source.tar"
    models = {}
    json_files = 0
    failures = []
    with tarfile.open(source) as archive:
        for member in archive.getmembers():
            if not member.isfile() or not member.name.endswith(".json"):
                continue
            json_files += 1
            try:
                data = json.load(archive.extractfile(member))
            except (ValueError, UnicodeError) as error:
                failures.append([member.name, str(error)])
                continue

            def walk(value, path):
                if isinstance(value, list):
                    if (len(value) == 64
                            and all(type(y) is int and 0 <= y < 512 for y in value)
                            and len(set(value)) == 64):
                        key = tuple(sorted(value))
                        models.setdefault(key, []).append([member.name, path])
                    else:
                        for i, child in enumerate(value):
                            walk(child, path + [i])
                elif isinstance(value, dict):
                    for key, child in value.items():
                        walk(child, path + [key])

            walk(data, [])

    results = []
    for points, locations in models.items():
        differences = {x ^ y for x in points for y in points}
        allowed = sorted(set(range(512)) - differences)
        basis = find_cube(allowed)
        if basis is not None:
            a, b, c = basis
            subgroup = {0, a, b, c, a ^ b, a ^ c, b ^ c, a ^ b ^ c}
            assert len(subgroup) == 8
            assert subgroup.intersection(differences) == {0}
            assert len({x ^ y for x in points for y in subgroup}) == 512
        results.append({
            "points": points, "locations": locations,
            "allowed_size": len(allowed), "linear_basis": basis,
        })

    report = {
        "source_url": "https://arxiv.org/src/2610.30712v1",
        "archive_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "json_files": json_files, "parse_failures": failures,
        "unique_64_point_arrays": len(results),
        "without_linear_complement": [
            result for result in results if result["linear_basis"] is None],
        "with_linear_complement": [
            {key: result[key] for key in ("locations", "allowed_size", "linear_basis")}
            for result in results if result["linear_basis"] is not None],
    }
    target = base / "FI_ANCILLARY_64_AUDIT.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{json_files} JSON files; {len(failures)} parse failures; "
          f"{len(results)} distinct 64-point arrays; "
          f"{len(report['without_linear_complement'])} without linear complement")
    for result in report["without_linear_complement"]:
        print(result["locations"])


if __name__ == "__main__":
    main()
