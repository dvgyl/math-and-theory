# Supporting records for the complete Gyires preprint

I collect the supporting arguments and certificates for the [Gyires preprint](../../paper.pdf) here. They cover structured matrix inequalities and related polynomial bounds. Its principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, and the exceptional-vector theorem have complete Lean proofs. The other principal matrix claims have ordinary proofs and specified exact certificates. The rank-two theorem has a complete Lean proof for orders 2 through 8. The general order-seven circulant result and rank-two orders 9 through 15 remain incomplete in Lean. I make no claim of novelty, independent human expert review, or peer review.

The [result map](source-map.md) lists the completed results, exact limitations, and unresolved claims. The [file record](provenance.json) lists the programs and mathematical reports. The collection integrity manifest gives their SHA-256 hashes. A completed reduction does not establish an unresolved target inequality.

Appendix A contains additional exact counterexamples, reductions, and two alternative transfer proofs. Appendix B states the scope and limits of finite computational observations. The [scientific data](exploratory-data/README.md) preserve the associated numerical records. These observations are separate from the exact theorem certificates.

The completed matrix results include circulants of orders five through seven, all-order permutation polynomials, all-order four-block matrices, one exceptional column or row, and rank-at-most-two matrices through order fifteen. The manuscript also contains the structural, scalar, deletion, balancing, local polynomial, and counting arguments. Exact obstructions refute only their stated auxiliary assertions.

## Reproduce the exact checks

Copy `certificates/*.py` into an empty working directory. Run the commands there with Python 3. The checks use Python 3.14.6. Programs that use assertions reject `python -O` and `PYTHONOPTIMIZE`. The scripts write JSON reports into the working directory or beside the copied script. Compare their mathematical fields with the files in `results/`. Timing fields can change.

Run these commands for orders six and seven.

```text
python3 circ_gap_test.py 6 all
python3 circ_gap_test.py 7 all
python3 independent_certificate_check.py 6
python3 independent_certificate_check.py 7
```

The two independent constructions cover 60 chambers in order six and 120 chambers in order seven. The complete certificate covers 5,022,480 coefficient positions. Confirm both full chamber counts and zero negative coefficients. The programs return a nonzero exit code when a mathematical check fails or the requested coverage is incomplete.

Run these commands for rank two.

```text
python3 rank2_bernstein.py --first 2 --last 15
python3 rank2_bernstein_fraction_check.py --first 2 --last 6
python3 rank2_identity_audit.py
python3 rank2_boundary_audit.py
python3 rank2_identity_check.py
python3 check_closure_examples.py
```

The full certificate covers 33,607 whole parameter intervals and 3,524,206 coefficient positions. The independent rational construction checks orders two through six. The direct identity checks are finite implementation checks. The written reduction and exhaustive interval certificate prove the stated range through order fifteen.

Run the cubic deletion commands in this order. The second command reads the first report.

```text
python3 deletion_n3_certificate.py
python3 deletion_n3_crosscheck.py
python3 deletion_n3_independent_audit.py
```

Confirm that the primary report contains all 120 chambers and no negative coefficients. The full independent report covers all 720 sorting orders. The three constructions agree on the coefficient counts, minima, and equality cases.

The following commands check exact identities and limitations.

```text
python3 configuration_check.py
python3 check_local_polynomial.py
python3 localization_obstruction.py
python3 check_obstructions.py
python3 zero_pure_certificate.py
python3 combinatorial_exact_checks.py
python3 boundary_exact.py
python3 average_fock_capacity_obstruction.py
python3 verify_manuscript_bounds.py
```

The configuration check enumerates every labeled stub matching in seven small cases. It checks the formula implementation. The general counting proof is in the manuscript. The local check uses rational arithmetic for the stated tangent identities. The obstruction checks use integers and rational intervals for their decisive comparisons.

The symbolic cubic check requires SymPy. The checked version is 1.14.0.

```text
python3 check_cubic_symbolic.py
```

The program `local_check.py` uses NumPy and SciPy. It is a numerical diagnostic. It is not part of any exact certificate and does not prove a neighborhood theorem.

The order-five formal and exact records remain in [verification](../../verification/README.md). The all-order permutation certificate remains in the [all-order extension record](../extensions/README.md).

## Check publication coverage

From the repository root, run:

```sh
python3 verification/check_gyires_certificates.py
python3 -m unittest discover -s verification -p 'test_certificate*.py'
```

The first command checks the exact finite ranges used in the paper. The tests check failure handling with invalid inputs, corrupt coefficients, missing chambers, and partial reports. A `running` or `sampled` rank-two report is not a completed certificate. These checks do not provide Lean proofs of the matrix reductions.

See the [authorship and autonomous AI disclosure](../../../../../AUTHORSHIP.md).
