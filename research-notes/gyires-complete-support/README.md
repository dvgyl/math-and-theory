# Supporting records for the complete Gyires preprint

The [continuous preprint](../../preprints/gyires-circulant-five/paper.pdf) contains the completed arguments from the supplied Gyires research materials. Its principal order-five claims have complete Lean proofs. The broader claims have ordinary proofs and specified exact certificates. Their Lean verification remains incomplete. No novelty, independent human expert review, or peer review is claimed.

The [source map](source-map.md) lists the completed results, subsumed arguments, exact limitations, and open claims. The [provenance manifest](provenance.json) records source and output hashes. The `sources/` directory preserves 41 historical text files byte for byte. Their `.txt` suffix identifies them as source records. Historical claims do not override the current manuscript. In particular, reductions and exploratory checks do not establish the unrestricted conjecture.

The completed matrix results include circulants of orders five through seven, all-order permutation polynomials, all-order four-block matrices, one exceptional column or row, and rank-at-most-two matrices through order fifteen. The manuscript also contains the structural, scalar, deletion, balancing, local polynomial, and counting arguments. Exact obstructions refute only their stated auxiliary assertions.

## Reproduce the exact checks

Copy `certificates/*.py` into an empty working directory. Run the commands there with Python 3. The recorded audit used Python 3.14.6. Do not use `python -O`, because the checks use assertions. The scripts write JSON reports into the working directory or beside the copied script. Compare their mathematical fields with the files in `results/`. Timing fields can change.

Run these commands for orders six and seven.

```text
python3 circ_gap_test.py 6 all
python3 circ_gap_test.py 7 all
python3 independent_certificate_check.py 6
python3 independent_certificate_check.py 7
```

The two independent constructions cover 60 chambers in order six and 120 chambers in order seven. The complete certificate covers 5,022,480 coefficient positions. Confirm both full chamber counts and zero negative coefficients. The primary program can stop on a negative result without a nonzero exit code.

Run these commands for rank two.

```text
python3 round6_rank2_bernstein.py --first 2 --last 15
python3 round6_rank2_bernstein_fraction_check.py --first 2 --last 6
python3 round6_rank2_identity_audit.py
python3 round6_rank2_boundary_audit.py
python3 round4_rank2_identity_check.py
python3 check_closure_examples.py
```

The full certificate covers 33,607 whole parameter intervals and 3,524,206 coefficient positions. The independent rational construction checks orders two through six. The direct identity checks are finite implementation checks. The written reduction and exhaustive interval certificate prove the stated range through order fifteen.

Run the cubic deletion commands in this order. The second command reads the first report.

```text
python3 round3_deletion_n3_certificate.py
python3 round3_deletion_n3_review.py
python3 round3_deletion_n3_independent_audit.py
```

Confirm that the primary report contains all 120 chambers and no negative coefficients. The full independent report covers all 720 sorting orders. All three regenerated reports match the supplied mathematical records.

The following commands check exact identities and limitations.

```text
python3 configuration_check.py
python3 check_local_polynomial.py
python3 round4_localization_obstruction.py
python3 check_obstructions.py
python3 round4_zero_pure_certificate.py
python3 round5_combinatorial_exact_checks.py
python3 round6_boundary_exact.py
python3 round6_average_fock_capacity_obstruction.py
python3 verify_manuscript_bounds.py
```

The configuration check enumerates every labeled stub matching in seven small cases. It checks the formula implementation. The general counting proof is in the manuscript. The local check uses rational arithmetic for the stated tangent identities. The obstruction checks use integers and rational intervals for their decisive comparisons.

The symbolic cubic check requires SymPy. The recorded version was 1.14.0.

```text
python3 check_cubic_symbolic.py
```

The historical `round4_local_check.py` uses NumPy and SciPy. It is a numerical diagnostic. It is not part of any exact certificate and does not prove a neighborhood theorem.

The order-five formal and exact records remain in [verification](../../verification/gyires-circulant-five/README.md). The all-order permutation certificate remains in the [earlier extension record](../gyires-extensions/README.md). The [preprint review](../../preprints/gyires-circulant-five/review.md) states the scope of the independent AI reviews.
