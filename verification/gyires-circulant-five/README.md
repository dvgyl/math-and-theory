# Verification of the order-five, four-block, and exceptional-vector Gyires results

The Lean library proves the order-five circulant theorem, its equality cases, and the sharp sorted-gap margin 484. The library also proves the all-order four-block theorem, its three contractions, margin, and equality case. It also proves both strong Gram bounds and Gyires's inequality for one exceptional column or row, with equality exactly at the uniform matrix. The Comparator configuration selects eighteen principal declarations. The [formal guide](../../lean/docs/gyires-circulant-five.md) maps these declarations to the [manuscript](../../preprints/gyires-circulant-five/paper.pdf).

The broader matrix and polynomial arguments have [separate certificate documentation](../../research-notes/gyires-complete-support/README.md). The principal higher-order circulant, permutation-polynomial, and finite rank-two theorems remain incomplete in Lean. The general supporting modules are included in the [whole-library audit](../README.md).

## Reproduce the formal checks

From `lean/`, run:

```sh
lake build MathAndTheory Solutions
lake env lean Audit.lean
lake env lean -j1 ../verification/gyires-circulant-five/AxiomAudit.lean > ../verification/gyires-circulant-five/axiom-audit.log
python3 ../verification/gyires-circulant-five/check_axioms.py ../verification/gyires-circulant-five/axiom-audit.log
```

The family audit checks 108 listed statements and their proof dependencies. The whole-library audit also checks the general supporting modules. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce the coefficient check

From the repository root, run:

```sh
python3 verification/gyires-circulant-five/scan_sources.py
python3 verification/gyires-circulant-five/check_coefficients.py --output verification/gyires-circulant-five/coefficient-results.json
```

The integer checker covers all 120 orderings and 120,120 coefficient positions. There are 119,520 positive coefficients and 600 zero coefficients. It checks the constant 484 and the witness `(1,1,0,0,0)`.

The checker uses the Python standard library. It reconstructs permanents from their permutation definition. It does not read Lean files or coefficient tables. Forward and inverse binomial transforms check the change to sorted gaps. This finite computation supplements the formal proof.

## Mathematical scope

The Challenge uses Mathlib's matrix, permanent, circulant, and doubly stochastic definitions. An explicit transpose theorem handles the two conventions for circulant indices. The order-five formal statements concern nonnegative circulant matrices. The four-block specifications use actual row and column vector counts for arbitrary doubly stochastic matrices. The exceptional-vector specifications require n ≥ 2 and state directly that all but one row or column are identical. All specifications write the constant `n! / n^n` explicitly.

The coefficient counts and minimum-coefficient statistics are exact computational results. The principal inequalities, equality cases, and sharp margin are Lean theorems. The formal proof uses `ring` and `positivity`; it does not use `native_decide`.

The source attribution and license are in [PROVENANCE.md](../../lean/MathAndTheory/Mathematics/GyiresCirculant5/PROVENANCE.md). See [AUTHORSHIP.md](../../AUTHORSHIP.md) for the AI-assistance disclosure. This preprint has not been peer reviewed.
