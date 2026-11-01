#!/usr/bin/env python3
"""Exact checks of the finite real q-permanent certificate.

Default mode uses only the Python standard library and the frozen files in this
directory. It checks

1. the ordered row word of the order-896 witness: the orbit-file hash, the
   expansion against the expanded row file, nonzero rows, the coordinate cap 32,
   the largest Gram diagonal 2490 and two nonzero 3x3 row minors (rank three);
2. the frozen exact integers: 1000 U > 1001 C(896,2) per(B), T >= U, the
   parity-component sums and D_1(B)/per(B) < -5012/25;
3. the independent modular record crt_residues.json: every modulus is a prime,
   their product exceeds C(n,2) n! prod_i B_ii, which bounds per(B) and every
   exterior parity-class norm, and the residues determine per(B), U and T
   exactly; these must equal the frozen integers;
4. the explicit regularization parameters M, H, Q, q1 = 1 - 2/Q, q2 = 1 - 1/Q
   against the compressed parameter record;
5. the order-1024 alternative: its hash and 250 U > 251 C(1024,2) per(B).

With --recompute it also compiles and runs, with g++, the GMP orbit-recurrence
program exact_orbits.cpp on both witnesses and compares every reported integer
with the frozen reports, and the ordinary-row modular program row_residues.cpp
on a sample of the recorded primes (--primes K; --primes all repeats the whole
record, about forty CPU minutes on one core). Build products go to a temporary
directory; no file in this directory is modified.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import math
import subprocess
import sys
import tempfile

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ORBITS = "witness896_cap32_orbits.txt"
ORBITS_SHA = "7220026a9fb5b2d9e62ef46b9b7196b2ff768b4841f71ccb45275ee445987751"
ROWS_SHA = "ab5efca3dcae41b29182df2e5d12d932a97beb13405368d3e4283d41c5a32cbf"
ORBITS_1024 = "witness1024_cap32_orbits.txt"
ORBITS_1024_SHA = "46b08a9f061f6bdddfb712ecc7943ff41a19de9082435520f8be16274dac6e44"
PARITY = [(0, 1), (0, 2), (1, 2)]


def fail(message):
    raise SystemExit("FAIL: " + message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_orbits(path):
    lines = [line.split() for line in path.read_text().splitlines() if line.strip()]
    count = int(lines[0][0])
    types = [tuple(map(int, line)) for line in lines[1:]]
    if len(types) != count or any(len(t) not in (3, 4) for t in types):
        fail(f"malformed orbit file {path.name}")
    return types


def expand(types):
    """Inner-to-outer wrapping: W -> (-a,b,c)^k (-a,-b,c)^k W (a,b,c)^k (a,-b,c)^k."""
    word = []
    for t in types:
        a, b, c = t[:3]
        k = t[3] if len(t) == 4 else 1
        if min(a, b, c) < 0 or k < 1:
            fail("orbit types must be nonnegative with positive multiplicity")
        word = [(-a, b, c)] * k + [(-a, -b, c)] * k + word + [(a, b, c)] * k + [(a, -b, c)] * k
    return word


def det3(u, v, w):
    return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0])
            + u[2] * (v[0] * w[1] - v[1] * w[0]))


def is_prime(m):
    if m < 2:
        return False
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if m % q == 0:
            return m == q
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):  # deterministic below 3.3e24
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def crt(residues, moduli):
    value, modulus = 0, 1
    for r, p in zip(residues, moduli):
        t = (r - value) * pow(modulus, -1, p) % p
        value += modulus * t
        modulus *= p
    return value, modulus


def check_rows(report):
    types = read_orbits(HERE / ORBITS)
    if sha256(HERE / ORBITS) != ORBITS_SHA:
        fail("primary orbit file hash")
    rows = expand(types)
    n = len(rows)
    lines = (HERE / "witness896_cap32_rows.txt").read_text().splitlines()
    if sha256(HERE / "witness896_cap32_rows.txt") != ROWS_SHA:
        fail("expanded row file hash")
    if int(lines[0]) != n or lines[1].split() != ["1", "1", "1"]:
        fail("row file header")
    if [tuple(map(int, line.split())) for line in lines[2:]] != rows:
        fail("row file differs from the orbit expansion")
    diag = [sum(x * x for x in v) for v in rows]
    minors = {"0,1,894": det3(rows[0], rows[1], rows[894]),
              "416,417,476": det3(rows[416], rows[417], rows[476])}
    if n != 896 or len(types) != 224 or min(diag) <= 0:
        fail("order, type count or nonzero rows")
    if max(abs(x) for v in rows for x in v) != 32 or max(diag) != 2490:
        fail("coordinate cap or largest diagonal")
    if minors != {"0,1,894": 480, "416,417,476": 1012}:
        fail("rank minors")
    report["rows"] = {"order": n, "orbit_types": len(types), "orbit_sha256": ORBITS_SHA,
                      "rows_match_expansion": True, "maximum_absolute_coordinate": 32,
                      "maximum_gram_diagonal": 2490, "rank_minors": minors, "rank": 3}
    return rows, diag


def check_exact(report):
    data = json.loads((HERE / "witness896_cap32_exact.json").read_text())
    n = data["order"]
    P = int(data["permanent"])
    U = int(data["averaged_wedge_norm_squared"])
    T = int(data["wedge_norm_squared"])
    parts = [int(x) for x in data["parity_component_norms"]]
    C = n * (n - 1) // 2
    if n != 896 or P <= 0 or not data["actual_wedge_included"] or len(parts) != 5:
        fail("exact report shape")
    if sum(parts[:3]) != U or sum(parts) != T or T < U:
        fail("parity components")
    if int(data["twice_derivative_upper_bound"]) != C * P - T:
        fail("reported twice derivative")
    if not 1000 * U > 1001 * C * P:
        fail("the integer comparison 1000 U > 1001 C(n,2) per(B)")
    bound = Fraction(C * P - U, 2 * P)  # D_1/per <= (C P - U)/(2P)
    if not bound < Fraction(-5012, 25):
        fail("derivative bound")
    exact_ratio = Fraction(C * P - T, 2 * P)
    report["exact"] = {"permanent_digits": len(str(P)), "U_digits": len(str(U)),
                       "comparison_1000U_gt_1001_C_per": True, "T_ge_U": True,
                       "D1_over_per_lt": "-5012/25",
                       "D1_over_per_exact_preview": f"{float(exact_ratio):.6f}"}
    return P, U, T


def check_crt(report, rows, diag, P, U, T, path):
    record = json.loads(path.read_text())
    n = len(rows)
    primes = [int(entry["p"]) for entry in record["residues"]]
    if record["rows_sha256"] != ROWS_SHA or len(set(primes)) != len(primes):
        fail("modular record header or repeated modulus")
    if not all((1 << 30) < p < (1 << 31) and is_prime(p) for p in primes):
        fail("modulus is not a prime in (2^30, 2^31)")
    bound = n * (n - 1) // 2 * math.factorial(n) * math.prod(diag)
    values = {}
    columns = ["per"] + [f"G{a}{b}_parity{e:03b}" for a, b in PARITY for e in range(8)]
    for k, name in enumerate(columns):
        value, modulus = crt([int(entry["values"][k]) for entry in record["residues"]], primes)
        values[name] = value
    if modulus <= bound:
        fail("the product of the moduli does not exceed the a priori bound")
    U_crt = values["G01_parity011"] + values["G02_parity000"] + values["G12_parity110"]
    T_crt = sum(v for k, v in values.items() if k != "per")
    nonzero = sorted(k for k, v in values.items() if k != "per" and v)
    if values["per"] != P or U_crt != U or T_crt != T:
        fail("modular reconstruction differs from the frozen exact integers")
    report["independent_row_residues"] = {
        "primes": len(primes), "modulus_bits": modulus.bit_length(),
        "a_priori_bound_bits": bound.bit_length(),
        "per_U_T_reconstructed_and_equal": True,
        "nonzero_parity_classes": nonzero}


def check_parameters(report, diag):
    n = len(diag)
    M = 10**4 * n**3
    H = M * max(diag) + 1
    Q = 4 * math.factorial(n) * n**4 * H**n
    data = json.loads(gzip.decompress(
        (HERE / "witness896_cap32_positive_definite_parameters.json.gz").read_bytes()))
    expected = {"M": str(M), "H_absolute_entry_bound": str(H), "Q": str(Q),
                "q1": {"numerator": str(Q - 2), "denominator": str(Q)},
                "q2": {"numerator": str(Q - 1), "denominator": str(Q)}}
    if any(data[k] != v for k, v in expected.items()) or data["row_file_sha256"] != ROWS_SHA:
        fail("regularization parameters")
    if not 0 < Q - 2 < Q - 1 < Q or M != 7193231360000 or H != 17911146086400001:
        fail("parameter ordering")
    report["regularization_parameters"] = {"M": str(M), "H": str(H),
                                           "Q_decimal_digits": len(str(Q)),
                                           "q1": "1 - 2/Q", "q2": "1 - 1/Q", "match_record": True}


def check_1024(report):
    if sha256(HERE / ORBITS_1024) != ORBITS_1024_SHA:
        fail("order-1024 orbit file hash")
    rows = expand(read_orbits(HERE / ORBITS_1024))
    data = json.loads((HERE / "witness1024_cap32_exact.json").read_text())
    n = data["order"]
    P, U = int(data["permanent"]), int(data["averaged_wedge_norm_squared"])
    C = n * (n - 1) // 2
    if n != 1024 or len(rows) != 1024 or max(abs(x) for v in rows for x in v) > 32 or P <= 0:
        fail("order-1024 witness shape")
    if not 250 * U > 251 * C * P:
        fail("order-1024 comparison 250 U > 251 C(n,2) per(B)")
    report["order_1024_alternative"] = {"comparison_250U_gt_251_C_per": True}


def recompute(report, rows, sample, record_path):
    record = json.loads(record_path.read_text())
    with tempfile.TemporaryDirectory() as work:
        work = Path(work)
        gmp = "/lib/x86_64-linux-gnu/libgmp.so.10"
        subprocess.run(["g++", "-O3", "-std=c++17", str(HERE / "exact_orbits.cpp"), gmp,
                        "-o", str(work / "exact_orbits")], check=True)
        for orbit, frozen in [(ORBITS, "witness896_cap32_exact.json"),
                              (ORBITS_1024, "witness1024_cap32_exact.json")]:
            out = work / "result.json"
            subprocess.run([str(work / "exact_orbits"), str(HERE / orbit), str(out)],
                           check=True, capture_output=True)
            new, old = json.loads(out.read_text()), json.loads((HERE / frozen).read_text())
            keys = ["order", "permanent", "averaged_wedge_norm_squared", "wedge_norm_squared",
                    "twice_derivative_upper_bound", "parity_component_norms"]
            if any(new[k] != old[k] for k in keys):
                fail(f"GMP recomputation differs from {frozen}")
        subprocess.run(["g++", "-O3", "-std=c++17", str(HERE / "row_residues.cpp"),
                        "-o", str(work / "row_residues")], check=True)
        (work / "rows.txt").write_text("".join(f"{x} {y} {z}\n" for x, y, z in rows))
        entries = record["residues"]
        if sample != "all":
            k = max(1, min(int(sample), len(entries)))
            entries = [entries[(i * (len(entries) - 1)) // max(1, k - 1)] for i in range(k)]
        subprocess.run([str(work / "row_residues"), str(work / "rows.txt"), str(work / "res.txt"),
                        *[str(e["p"]) for e in entries]], check=True)
        lines = (work / "res.txt").read_text().split("\n")
        for entry, line in zip(entries, lines):
            fields = line.split()
            if int(fields[0]) != int(entry["p"]) or [int(x) for x in fields[2:]] != [int(x) for x in entry["values"]]:
                fail(f"row residues differ at p = {entry['p']}")
    report["recomputed"] = {"gmp_orbit_recurrence_896_and_1024": "match",
                            "row_residue_primes_recomputed": len(entries)}


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--recompute", action="store_true")
    parser.add_argument("--primes", default="4")
    args = parser.parse_args()
    report = {"scope": "Exact integer certificate of the order-896 rank-three Gram witness"}
    rows, diag = check_rows(report)
    P, U, T = check_exact(report)
    check_crt(report, rows, diag, P, U, T, HERE / "crt_residues.json")
    check_parameters(report, diag)
    check_1024(report)
    if args.recompute:
        recompute(report, rows, args.primes, HERE / "crt_residues.json")
    report["status"] = "PASS"
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
