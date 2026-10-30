#!/usr/bin/env python3
"""Generate and independently reload/check the fixed MAT-C rational witness.

Only the Python standard library is used. Every matrix entry and arithmetic
operation is rational, using fractions.Fraction. No floating-point arithmetic,
numerical tolerance, optimizer, or external computer-algebra package is used.

Run:
    python3 exact_certificate.py
    python3 exact_certificate.py --output-dir /path/to/output
    python3 exact_certificate.py --verify-only /path/to/C11_NMF109.json

The emitted factors certify rank_+(C tensor C) <= 109. They do not certify that
the nonnegative rank of C tensor C equals 109. The seed lower-bound conditions
and ordinary ranks are checked separately; the explanation of how the former
exclude width three is included in the result record.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from time import perf_counter_ns
from typing import Any


Q = Fraction
Matrix = list[list[Fraction]]
EPSILON = Q(1, 11491200)
ETA = Q(1, 15120)
BETA = 1 + EPSILON / 7
CERTIFICATE_FILENAME = "C11_NMF109.json"
RESULT_FILENAME = "EXACT_CERTIFICATE_RESULT.json"
SCHEMA = "mat-c-rational-nmf109-v1"


def require(condition: bool, message: str) -> None:
    """Use explicit exceptions so python -O cannot disable verification."""
    if not condition:
        raise ValueError(message)


def shape(a: Matrix) -> tuple[int, int]:
    require(bool(a), "This fixed certificate never uses an empty matrix.")
    width = len(a[0])
    require(width > 0, "A matrix has no columns.")
    require(all(len(row) == width for row in a), "Ragged matrix.")
    require(
        all(isinstance(x, Fraction) for row in a for x in row),
        "Every matrix entry must be a Fraction.",
    )
    return len(a), width


def zero(rows: int, cols: int) -> Matrix:
    return [[Q(0) for _ in range(cols)] for _ in range(rows)]


def identity(size: int) -> Matrix:
    return [[Q(int(i == j)) for j in range(size)] for i in range(size)]


def ones(rows: int, cols: int) -> Matrix:
    return [[Q(1) for _ in range(cols)] for _ in range(rows)]


def scale(c: Fraction, a: Matrix) -> Matrix:
    return [[c * x for x in row] for row in a]


def add(a: Matrix, b: Matrix) -> Matrix:
    require(shape(a) == shape(b), "Addition dimensions disagree.")
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def outer(a: list[Fraction], b: list[Fraction]) -> Matrix:
    return [[x * y for y in b] for x in a]


def kronecker(a: Matrix, b: Matrix) -> Matrix:
    ar, ac = shape(a)
    br, bc = shape(b)
    return [
        [a[i][j] * b[k][ell] for j in range(ac) for ell in range(bc)]
        for i in range(ar)
        for k in range(br)
    ]


def matmul(a: Matrix, b: Matrix) -> tuple[Matrix, dict[str, int]]:
    rows, width = shape(a)
    width_b, cols = shape(b)
    require(width == width_b, "Product dimensions disagree.")
    result = zero(rows, cols)
    products = 0
    for i in range(rows):
        for k in range(width):
            aik = a[i][k]
            if aik == 0:
                continue
            for j in range(cols):
                bkj = b[k][j]
                if bkj != 0:
                    result[i][j] += aik * bkj
                    products += 1
    dense = rows * width * cols
    return result, {
        "scalar_products_in_dense_formula": dense,
        "nonzero_scalar_products_evaluated": products,
        "zero_scalar_products_skipped_exactly": dense - products,
    }


def encode_matrix(a: Matrix) -> list[list[str]]:
    shape(a)
    return [[str(x) for x in row] for row in a]


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def matrix_digest(a: Matrix) -> str:
    return hashlib.sha256(canonical_json(encode_matrix(a))).hexdigest()


class Checks:
    def __init__(self) -> None:
        self.equalities: list[dict[str, Any]] = []
        self.nonnegativity: list[dict[str, Any]] = []
        self.scalar: list[dict[str, Any]] = []
        self.ranks: list[dict[str, Any]] = []

    def equal(
        self, name: str, a: Matrix, b: Matrix, extra: dict[str, Any] | None = None
    ) -> None:
        dims = shape(a)
        require(dims == shape(b), f"{name}: dimensions disagree.")
        for i, (ar, br) in enumerate(zip(a, b)):
            for j, (x, y) in enumerate(zip(ar, br)):
                require(x == y, f"{name}: mismatch at ({i}, {j}): {x} != {y}")
        record = {
            "name": name,
            "shape": list(dims),
            "entries_checked": dims[0] * dims[1],
            "passed": True,
        }
        if extra:
            record.update(extra)
        self.equalities.append(record)

    def product(self, name: str, a: Matrix, b: Matrix, expected: Matrix) -> None:
        actual, stats = matmul(a, b)
        stats["inner_dimension"] = shape(a)[1]
        self.equal(name, actual, expected, stats)

    def nonnegative(self, name: str, a: Matrix, strict: bool = False) -> None:
        dims = shape(a)
        minimum = min(x for row in a for x in row)
        for i, row in enumerate(a):
            for j, x in enumerate(row):
                require(x > 0 if strict else x >= 0, f"{name}: bad sign at ({i}, {j})")
        self.nonnegativity.append(
            {
                "name": name,
                "shape": list(dims),
                "entries_checked": dims[0] * dims[1],
                "relation": "> 0" if strict else ">= 0",
                "minimum_entry": str(minimum),
                "passed": True,
            }
        )

    def relation(self, name: str, left: Fraction | int, op: str, right: Fraction | int) -> None:
        if op == "=":
            result = left == right
        elif op == "<=":
            result = left <= right
        elif op == "<":
            result = left < right
        elif op == ">":
            result = left > right
        else:
            raise ValueError(f"Unknown relation {op}")
        require(result, f"{name}: {left} {op} {right} failed.")
        self.scalar.append(
            {"name": name, "left": str(left), "relation": op, "right": str(right), "passed": True}
        )

    def rank(self, name: str, a: Matrix, expected: int) -> None:
        reduced = [row[:] for row in a]
        rows, cols = shape(reduced)
        pivots: list[int] = []
        pivot_row = 0
        for col in range(cols):
            candidate = next((i for i in range(pivot_row, rows) if reduced[i][col] != 0), None)
            if candidate is None:
                continue
            reduced[pivot_row], reduced[candidate] = reduced[candidate], reduced[pivot_row]
            pivot = reduced[pivot_row][col]
            reduced[pivot_row] = [x / pivot for x in reduced[pivot_row]]
            for i in range(rows):
                if i == pivot_row:
                    continue
                multiplier = reduced[i][col]
                if multiplier:
                    reduced[i] = [
                        x - multiplier * y for x, y in zip(reduced[i], reduced[pivot_row])
                    ]
            pivots.append(col)
            pivot_row += 1
            if pivot_row == rows:
                break
        require(len(pivots) == expected, f"{name}: rank is {len(pivots)}, expected {expected}.")
        require(
            all(x == 0 for row in reduced[len(pivots):] for x in row),
            f"{name}: invalid zero rows in reduced echelon form.",
        )
        for i, col in enumerate(pivots):
            require(
                all(reduced[j][col] == int(i == j) for j in range(rows)),
                f"{name}: invalid pivot column {col}.",
            )
        self.ranks.append(
            {
                "name": name,
                "shape": [rows, cols],
                "method": "Fraction Gaussian elimination to reduced row echelon form",
                "rank": len(pivots),
                "pivot_columns_zero_based": pivots,
                "rref": encode_matrix(reduced),
                "rref_sha256": matrix_digest(reduced),
                "passed": True,
            }
        )

    def record(self) -> dict[str, Any]:
        return {
            "matrix_equalities": self.equalities,
            "entry_sign_checks": self.nonnegativity,
            "scalar_relations": self.scalar,
            "ordinary_rank_checks": self.ranks,
            "totals": {
                "matrix_equalities": len(self.equalities),
                "matrix_equality_entries_checked": sum(x["entries_checked"] for x in self.equalities),
                "entry_sign_checks": sum(x["entries_checked"] for x in self.nonnegativity),
                "scalar_relations": len(self.scalar),
                "ordinary_rank_checks": len(self.ranks),
                "nonzero_scalar_products_evaluated": sum(
                    x.get("nonzero_scalar_products_evaluated", 0) for x in self.equalities
                ),
            },
            "all_passed": True,
        }


def seed_and_block() -> tuple[Matrix, Matrix, Matrix]:
    a = [
        [Q(17), Q(17), Q(1), Q(1)],
        [Q(1), Q(17), Q(17), Q(1)],
        [Q(1), Q(1), Q(17), Q(17)],
        [Q(17), Q(1), Q(1), Q(17)],
    ]
    b = add(ones(7, 7), scale(EPSILON, identity(7)))
    c = zero(11, 11)
    for i in range(4):
        for j in range(4):
            c[i][j] = a[i][j]
    for i in range(7):
        for j in range(7):
            c[4 + i][4 + j] = b[i][j]
    return a, b, c


def check_ranks_and_seed(a: Matrix, b: Matrix, c: Matrix, checks: Checks) -> None:
    checks.rank("rank(A) = 3", a, 3)
    checks.rank("rank(B) = 7", b, 7)
    checks.rank("rank(C) = 10", c, 10)
    checks.product("A times alternating kernel vector is zero", a, [[Q(1)], [Q(-1)], [Q(1)], [Q(-1)]], zero(4, 1))
    leading_minor = (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )
    checks.relation("leading 3 by 3 minor of A", leading_minor, "=", 4608)
    for i in range(4):
        checks.relation(f"seed diagonal ({i},{i})", a[i][i], "=", 17)
        for j in range(4):
            if i != j:
                checks.relation(f"seed cross product ({i},{j})", a[i][j] * a[j][i], "<=", 17)
    checks.relation("seed width-three obstruction: 17 squared > 3 squared times 17", Q(17) ** 2, ">", 3 ** 2 * 17)
    binv = add(scale(1 / EPSILON, identity(7)), scale(-1 / (EPSILON * (EPSILON + 7)), ones(7, 7)))
    checks.product("explicit B inverse times B", binv, b, identity(7))
    checks.product("B times explicit B inverse", b, binv, identity(7))
    checks.relation("block minimum-width deduction: 4 + 7", 4 + 7, "=", 11)
    checks.relation("conjectured comparison product: 11 times 10", 11 * 10, "=", 110)
    checks.relation("certified strict comparison", 109, "<", 110)


def build_certificate() -> tuple[dict[str, Any], dict[str, Any]]:
    checks = Checks()
    a, b, c = seed_and_block()
    p = [[Q(int(j == (i + 1) % 4)) for j in range(4)] for i in range(4)]
    s = add(identity(4), p)
    u_matrix = add(identity(4), scale(Q(1, 36), ones(4, 4)))
    v_matrix = add(scale(Q(16), s), scale(Q(1, 10), ones(4, 4)))
    r_seed = [row[:3] for row in a]
    t_seed = [[Q(int(i == j)) for j in range(3)] + [Q((1, -1, 1)[i])] for i in range(3)]
    w = [[Q(int(i == j)) for j in range(6)] for i in range(6)] + [[Q(-1)] * 6]
    z = [[Q(int(i == j)) - Q(1, 7) for j in range(7)] for i in range(6)]
    e = add(identity(7), scale(Q(-1, 7), ones(7, 7)))
    r_hat = kronecker(r_seed, w)
    t_hat = kronecker(t_seed, z)
    f = kronecker(a, e)
    u = [u_matrix[i][0] for i in range(4) for _ in range(7)]
    v = [BETA * v_matrix[0][j] for j in range(4) for _ in range(7)]
    r_sums = [sum(row, Q(0)) for row in r_hat]
    t_sums = [sum((t_hat[k][j] for k in range(18)), Q(0)) for j in range(28)]
    h = [
        [u[i] + ETA * r_hat[i][k] for k in range(18)] + [u[i] - ETA * r_sums[i]]
        for i in range(28)
    ]
    g = [
        [v[j] / 19 + (EPSILON / ETA) * (t_hat[k][j] - t_sums[j] / 19) for j in range(28)]
        for k in range(18)
    ] + [[v[j] / 19 - (EPSILON / ETA) * t_sums[j] / 19 for j in range(28)]]

    checks.product("U V = A", u_matrix, v_matrix, a)
    checks.product("seed rank-three R T = A", r_seed, t_seed, a)
    checks.product("W Z = I7 - J7/7", w, z, e)
    checks.product("Rhat That = A tensor (I7 - J7/7)", r_hat, t_hat, f)
    checks.equal("B = beta J7 + epsilon E", b, add(scale(BETA, ones(7, 7)), scale(EPSILON, e)))
    checks.equal("sum of G rows equals v", [[sum((g[k][j] for k in range(19)), Q(0)) for j in range(28)]], [v])
    checks.equal("G row differences equal epsilon/eta times That", [[g[k][j] - g[18][j] for j in range(28)] for k in range(18)], scale(EPSILON / ETA, t_hat))
    checks.product("H G = u v + epsilon F", h, g, add(outer(u, v), scale(EPSILON, f)))
    checks.relation("abs(Rhat) bound", max(abs(x) for row in r_hat for x in row), "<=", 17)
    checks.relation("abs(Rhat row sums) bound", max(abs(x) for x in r_sums), "<=", 210)
    checks.relation("abs(That) bound", max(abs(x) for row in t_hat for x in row), "<=", 1)
    checks.relation("abs(That column sums) bound", max(abs(x) for x in t_sums), "<=", 18)
    checks.relation("epsilon/eta", EPSILON / ETA, "=", Q(1, 760))

    # The first three columns are original rank-one terms 1, 2 and 3;
    # the last nineteen replace term 0 and carry the centered perturbation.
    lab = [[u_matrix[i // 7][k] for k in (1, 2, 3)] + h[i] for i in range(28)]
    rab = [[BETA * v_matrix[k][j // 7] for j in range(28)] for k in (1, 2, 3)] + g
    ab = kronecker(a, b)
    checks.product("width-22 cross factorization of A tensor B", lab, rab, ab)

    # A tensor B uses (i,a) -> 7*i+a; B tensor A uses (a,i) -> 4*a+i.
    swap = [7 * i + alpha for alpha in range(7) for i in range(4)]
    lba = [lab[swap[row]][:] for row in range(28)]
    rba = [[row[swap[col]] for col in range(28)] for row in rab]
    ba = kronecker(b, a)
    checks.product("width-22 permuted factorization of B tensor A", lba, rba, ba)

    laa, raa = kronecker(u_matrix, u_matrix), kronecker(v_matrix, v_matrix)
    aa = kronecker(a, a)
    lbb, rbb = identity(49), kronecker(b, b)
    checks.product("width-16 factorization of A tensor A", laa, raa, aa)
    checks.product("width-49 factorization of B tensor B", lbb, rbb, kronecker(b, b))

    l_global, r_global = zero(121, 109), zero(109, 121)
    blocks = [
        ("AA", [11 * i + j for i in range(4) for j in range(4)], laa, raa),
        ("AB", [11 * i + 4 + alpha for i in range(4) for alpha in range(7)], lab, rab),
        ("BA", [11 * (4 + alpha) + i for alpha in range(7) for i in range(4)], lba, rba),
        ("BB", [11 * (4 + alpha) + 4 + beta for alpha in range(7) for beta in range(7)], lbb, rbb),
    ]
    all_pair_indices = [index for _, indices, _, _ in blocks for index in indices]
    require(sorted(all_pair_indices) == list(range(121)), "Block pair indices do not partition the square.")
    block_metadata = []
    start = 0
    for name, indices, left, right in blocks:
        height, width = shape(left)
        require(height == len(indices) and shape(right) == (width, height), f"Bad {name} dimensions.")
        for row, global_row in enumerate(indices):
            for k in range(width):
                l_global[global_row][start + k] = left[row][k]
                r_global[start + k][global_row] = right[k][row]
        block_metadata.append({"name": name, "factor_column_start_zero_based": start, "width": width, "global_pair_indices_zero_based": indices})
        start += width
    checks.relation("sum of four block factor widths", start, "=", 109)
    checks.product("global L R = C tensor C; every one of 14641 entries", l_global, r_global, kronecker(c, c))

    for name, matrix, strict in [
        ("A", a, True), ("B", b, True), ("C", c, False),
        ("U", u_matrix, True), ("V", v_matrix, True),
        ("simplex H", h, True), ("simplex G", g, True),
        ("cross AB left", lab, True), ("cross AB right", rab, True),
        ("cross BA left", lba, True), ("cross BA right", rba, True),
        ("AA left", laa, True), ("AA right", raa, True),
        ("BB left", lbb, False), ("BB right", rbb, True),
        ("global L", l_global, False), ("global R", r_global, False),
    ]:
        checks.nonnegative(name, matrix, strict)
    check_ranks_and_seed(a, b, c, checks)

    matrices = {"C": c, "L": l_global, "R": r_global}
    certificate = {
        "schema": SCHEMA,
        "description": "Exact rational nonnegative factors for the square of the fixed 11 by 11 MAT-C matrix.",
        "arithmetic": "Canonical fractions p/q (or integers), with positive denominator; no floating point.",
        "matrix_hash_encoding": "SHA-256 of UTF-8 compact JSON of the matrix of canonical rational strings, separators=(',', ':').",
        "parameters": {"t": 6, "epsilon": str(EPSILON), "eta": str(ETA), "beta": str(BETA)},
        "indexing": {
            "C": "Indices 0..3 are A; indices 4..10 are B.",
            "tensor_square": "Pair (i,j) has row or column index 11*i+j, with 0 <= i,j < 11.",
            "Lean_Option_Fin_6": "some i maps to i for 0 <= i < 6; none maps to 6.",
            "Lean_Fin_3_times_Fin_6": "Pair (k,a) maps to 6*k+a for 0 <= k < 3, 0 <= a < 6.",
            "Lean_Option_perturbation_index": "some (k,a) maps to 6*k+a in 0..17; none maps to the final simplex column/row 18.",
            "cross_factor_order": "Original terms 1,2,3 precede simplex terms 0..18, for 22 total terms.",
        },
        "shapes": {name: list(shape(matrix)) for name, matrix in matrices.items()},
        "factor_column_blocks": block_metadata,
        "factorization_identity": "L R = C tensor C",
        "square_nonnegative_rank_upper_bound": 109,
        "square_nonnegative_rank_exact_value": None,
        "limitation": "Width 109 is an upper bound. This certificate contains no claim that a smaller factorization is impossible and no novelty claim.",
        "matrix_sha256": {name: matrix_digest(matrix) for name, matrix in matrices.items()},
        **{name: encode_matrix(matrix) for name, matrix in matrices.items()},
    }
    return certificate, checks.record()


def decode_matrix(value: Any, name: str, dims: tuple[int, int]) -> Matrix:
    require(isinstance(value, list) and len(value) == dims[0], f"{name}: bad row count.")
    result: Matrix = []
    for i, row in enumerate(value):
        require(isinstance(row, list) and len(row) == dims[1], f"{name}: bad column count at row {i}.")
        parsed = []
        for j, entry in enumerate(row):
            require(isinstance(entry, str), f"{name}: entry ({i},{j}) is not a rational string.")
            x = Q(entry)
            require(str(x) == entry, f"{name}: noncanonical rational string at ({i},{j}).")
            parsed.append(x)
        result.append(parsed)
    return result


def verify_emitted_certificate(path: Path) -> dict[str, Any]:
    """Reload serialized factors and verify them without regenerating the factors."""
    raw = path.read_bytes()
    document = json.loads(raw)
    require(document.get("schema") == SCHEMA, "Unrecognized certificate schema.")
    require(document.get("square_nonnegative_rank_upper_bound") == 109, "Incorrect upper-bound metadata.")
    require(document.get("square_nonnegative_rank_exact_value") is None, "An exact square nonnegative rank was claimed.")
    require(document.get("parameters") == {"t": 6, "epsilon": str(EPSILON), "eta": str(ETA), "beta": str(BETA)}, "Incorrect parameter metadata.")
    shapes = {"C": (11, 11), "L": (121, 109), "R": (109, 121)}
    require(document.get("shapes") == {name: list(dims) for name, dims in shapes.items()}, "Incorrect shape metadata.")
    matrices = {name: decode_matrix(document.get(name), name, dims) for name, dims in shapes.items()}
    for name, matrix in matrices.items():
        require(document["matrix_sha256"][name] == matrix_digest(matrix), f"{name}: matrix SHA-256 mismatch.")
    c, left, right = matrices["C"], matrices["L"], matrices["R"]
    expected_a, expected_b, expected_c = seed_and_block()
    checks = Checks()
    checks.equal("reloaded C equals the specified fixed witness", c, expected_c)
    for name, matrix in matrices.items():
        checks.nonnegative(f"reloaded {name}", matrix)
    checks.product("reloaded L R = reloaded C tensor reloaded C; all 14641 entries", left, right, kronecker(c, c))
    a = [row[:4] for row in c[:4]]
    b = [row[4:] for row in c[4:]]
    checks.equal("reloaded seed A", a, expected_a)
    checks.equal("reloaded full-rank block B", b, expected_b)
    check_ranks_and_seed(a, b, c, checks)
    return {
        "certificate_file": str(path.resolve()),
        "certificate_file_sha256": hashlib.sha256(raw).hexdigest(),
        "certificate_size_bytes": len(raw),
        "canonical_rational_entries_parsed": sum(rows * cols for rows, cols in shapes.values()),
        "matrix_sha256": {name: matrix_digest(matrix) for name, matrix in matrices.items()},
        "checks": checks.record(),
        "all_passed": True,
    }


def deduction_record() -> dict[str, Any]:
    return {
        "ordinary_rank_A": 3,
        "ordinary_rank_B": 7,
        "ordinary_rank_C": 10,
        "nonnegative_rank_A": 4,
        "nonnegative_rank_B": 7,
        "nonnegative_rank_C": 11,
        "square_nonnegative_rank_upper_bound": 109,
        "square_nonnegative_rank_exact_value": None,
        "comparison_product": 110,
        "strict_gap_from_comparison_product": 1,
        "lower_bound_proof_conditions_checked": {
            "number_of_seed_diagonals": 4,
            "putative_factor_width": 3,
            "each_seed_diagonal": "17",
            "all_twelve_ordered_distinct_pair_cross_products_at_most": "17",
            "diagonal_squared": "289",
            "width_squared_times_cross_bound": "153",
        },
        "lower_bound_mathematical_argument": [
            "If A had a nonnegative factorization of width at most three, pad to three. Each diagonal 17 has a rank-one summand at least 17/3. Four diagonal positions force two to choose the same summand. Its rank-one identity then gives (17/3)^2 <= A_ij*A_ji <= 17, contradicting 289 > 153. Thus rank_+(A) >= 4; a width-four factorization is explicitly checked.",
            "The checked ordinary rank of B is seven. Ordinary rank is a lower bound for nonnegative factor width, and the trivial factorization I7*B gives width seven. Thus rank_+(B) = 7.",
            "For a block diagonal nonnegative matrix, a nonzero nonnegative rank-one summand cannot contribute to both diagonal blocks: that would force a positive cross-block entry. Classifying summands by the block they support proves nonnegative-rank additivity. Therefore rank_+(C) = 4+7 = 11.",
            "The reloaded nonnegative factors L (121 by 109) and R (109 by 121) satisfy L*R = C tensor C entry by entry. Therefore rank_+(C tensor C) <= 109 < 110 = rank_+(C)*rank(C).",
        ],
        "verification_scope": "The script verifies exact certificate conditions and products. The lower-bound deductions use the elementary mathematical arguments recorded above. This is independent rational computation, not a claim of running or auditing Lean.",
        "novelty": "Not assessed by this certificate generator/checker.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--verify-only", type=Path, help="Reload and verify an existing certificate without regenerating factors or writing files.")
    args = parser.parse_args()
    start = perf_counter_ns()
    if args.verify_only is not None:
        verified = verify_emitted_certificate(args.verify_only)
        print(json.dumps({
            "status": "PASS",
            "mode": "verify-only",
            "certificate_file": verified["certificate_file"],
            "certificate_file_sha256": verified["certificate_file_sha256"],
            "canonical_rational_entries_parsed": verified["canonical_rational_entries_parsed"],
            "checks": verified["checks"]["totals"],
            "square_nonnegative_rank_upper_bound": 109,
            "square_nonnegative_rank_exact_value": None,
            "elapsed_nanoseconds": perf_counter_ns() - start,
        }, indent=2, sort_keys=True))
        return

    args.output_dir.mkdir(parents=True, exist_ok=True)
    certificate, construction = build_certificate()
    certificate_path = args.output_dir / CERTIFICATE_FILENAME
    certificate_path.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    reloaded = verify_emitted_certificate(certificate_path)
    result = {
        "schema": "mat-c-rational-nmf109-check-result-v1",
        "status": "PASS",
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "generator_file": str(Path(__file__).resolve()),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python_version": sys.version,
        "python_executable": sys.executable,
        "construction_source_correspondence": {
            "mathematical_formulas": "audits/F1_ADVERSARIAL_MATH.md, Sections 1-5",
            "contrast_and_parameters": "lean/MatCKronecker/CrossData.lean: contrastLeft, contrastRight, centeredIdentity, crossRankLeft, crossRankRight, crossEpsilon, crossEta",
            "baseline_and_cross_factors": "lean/MatCKronecker/CrossFactors.lean: crossU, crossV, otherLeft, otherRight, correctedTerm",
            "simplex_formulas": "lean/MatCKronecker/SimplexFactorization.lean: simplexLeft, simplexRight",
            "index_correspondence": "Recorded in the certificate indexing field. This checker evaluates the same formulas over rational numbers; it does not extract executable code or a proof from Lean.",
        },
        "arithmetic": "Python standard-library fractions.Fraction exclusively for matrix arithmetic; no floats, tolerances or external modules.",
        "construction_checks": construction,
        "reload_verification": reloaded,
        "mathematical_deductions": deduction_record(),
        "elapsed_nanoseconds": perf_counter_ns() - start,
    }
    result_path = args.output_dir / RESULT_FILENAME
    result_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": "PASS",
        "certificate_file": str(certificate_path.resolve()),
        "certificate_file_sha256": reloaded["certificate_file_sha256"],
        "certificate_size_bytes": reloaded["certificate_size_bytes"],
        "result_file": str(result_path.resolve()),
        "construction_checks": construction["totals"],
        "reload_checks": reloaded["checks"]["totals"],
        "ordinary_ranks": {"A": 3, "B": 7, "C": 10},
        "square_nonnegative_rank_upper_bound": 109,
        "square_nonnegative_rank_exact_value": None,
        "elapsed_nanoseconds": result["elapsed_nanoseconds"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
