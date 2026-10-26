# Verify the diagonal-concavity family

The principal result is a complete analytic classification for the parameter `M>0`. The independent program checks the exact algebra and one strict midpoint violation. The [Lean guide](../../lean/docs/diagonal-concavity.md) maps the analytic claims to their proofs.

## Reproduce the computation

From the repository root, run:

```sh
python3 verification/diagonal-concavity/scripts/verify.py
```

The program uses only the Python standard library. It writes JSON to standard output and raises an assertion failure if a check fails.

It constructs each elementary symmetric polynomial by enumerating subsets. It differentiates the subset products directly. It does not import the manuscript's derivative coefficients.

The checks are:

- The diagonal curvature identity at 21 rational grid points: three values of `M` and seven values of the diagonal coordinate `t`.
- The directional curvature identity at three values of `M`.
- Exact values `933/64`, `121/4`, and `3597/64` at the two endpoints and midpoint of the `M=2` witness.
- Rational fourth-power bounds that certify a strict midpoint violation without floating-point roots.

The diagonal expression has degree at most two in `M` and at most six in `t`. The grid therefore determines its polynomial coefficients. The directional expression has degree at most two in `M`. Its three values determine those coefficients. These degree bounds explain the grid sizes; the test is not a random numerical sample.

## Reproduce the formal checks

Install the toolchain in `lean/lean-toolchain` and obtain the pinned dependencies. From the repository root, run:

```sh
cd lean
lake exe cache get
lake build MathAndTheory.Mathematics.DiagonalConcavity Solutions.DiagonalConcavity
lake env lean Solutions/DiagonalConcavity.lean
```

The last command prints the axiom list for `ConcavityChallenge.result`. It contains only `propext`, `Classical.choice`, and `Quot.sound`. The target uses Mathlib's `ConcaveOn` predicate and the real fourth root. The proved source also connects its coordinate sums to `Multiset.esymm`.

In an environment with `bwrap` and the kernels bundled with Lean 4.35.0, run this command from `lean/`:

```sh
bash scripts/verify-comparator.sh comparator/diagonal-concavity.json
```

The [Challenge](../../lean/Challenges/DiagonalConcavity.lean) states both parameter equivalences. The [Solution](../../lean/Solutions/DiagonalConcavity.lean) proves the same statement. The Challenge's permitted proof hole is a specification and is excluded from the proved library.

See the [central verification record](../README.md) for the recorded Comparator and review status. A successful compilation is not itself evidence that the independent kernel replay has completed.

## Limits

The exact program checks the algebraic identities and finite midpoint certificate. It does not, by itself, prove a statement about every point of an open domain. The Lean development supplies the derivative, positivity, and concavity arguments for that universal conclusion.

The result concerns the stated one-parameter family in four variables. It does not classify arbitrary coefficients or higher dimensions. Verification does not establish historical priority or expert peer review. This paper has not been peer reviewed.
