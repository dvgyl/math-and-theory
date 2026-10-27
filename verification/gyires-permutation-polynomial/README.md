# Gyires's inequality for permutation polynomials

This package gives a Lean proof for every matrix A=aI+bQ+cQ², where Q is a finite permutation matrix and a,b,c are nonnegative real numbers. Put c_n=n!/n^n. The theorem proves

    c_n per(AAᵀ) ≤ per(A)²,
    c_n per(AᵀA) ≤ per(A)²,
    c_n per(A²) ≤ per(A)²,
    c_n [per(AAᵀ)+per(AᵀA)+2 per(A²)] ≤ 4 per(A)².

Here `per` is the permanent. It is the sum, over all permutations, of the products formed by taking one entry from each row and column. The theorem uses Mathlib's permanent, matrix product, transpose, and permutation matrix. It requires no normalization of the row sums. If a+b+c=1, the matrix is doubly stochastic.

The formal statements include zero weights, fixed points, arbitrary cycle lengths, and the empty dimension. For n=0, the definitions give c_0=1 and permanent 1 for the empty matrix. For the canonical cyclic permutation of order n≥23, at least one positive weight makes all four inequalities strict. The theorem does not cover arbitrary sums of three unrelated permutation matrices or all circulants. It does not give a general equality classification for this matrix family.

## Proof structure

The proof computes the actual cyclic permanent and its Gram permanent by finite transfer matrices. A positive root gives a lower bound for the cyclic permanent. Exact polynomial identities prove the cycle bounds for orders 3–22. A weighted trace estimate proves them for every order at least 23. Explicit formulas cover orders 0–2.

Every finite permutation is a disjoint union of cycles. The permanent product formula and the dimension-constant inequality combine the cycle bounds. A permanent Cauchy–Schwarz comparison then gives the bound for the original matrix square A².

[THEOREMS.md](THEOREMS.md) maps these statements to the source. The 405 source modules are listed in [sources.json](sources.json). The final theorem has no assumption that the cycle inequalities hold.

## Reproduce the checks

Install Python 3.11 or later and the Lean toolchain manager `elan`. The package pins Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The dependency revisions are in `lake-manifest.json`.

Run these commands from this directory:

```sh
python3 check_package.py
lake exe cache get
python3 verify.py
```

The cache command retrieves dependency build files. The verifier checks each dependency checkout against `lake-manifest.json`. It also records the exact dependency object hashes. Dependency build files and the installed Lean toolchain are external prerequisites.

The verifier compiles all 405 project modules in a fresh `.verification/build` directory. It uses one compiler at a time. Each compiler uses Lean's 2 GiB memory setting and a ten-minute time limit. The verifier also stops a compiler if its sampled process-group memory exceeds 2 GiB. It removes inherited Lean search paths. Its search path contains only the new project build, the locked dependency libraries, and the selected toolchain. Existing project objects in `.lake/build/lib/lean` cause a failure.

The same command checks the final ten axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Missing reports, unexpected axioms, warnings, compiler errors, and incomplete module coverage cause a nonzero exit. The command writes `complete: true` to `.verification/result.json` only after every check passes.

To use a limited work period, run `python3 verify.py --max-seconds 600`. If the command stops, run `python3 verify.py --resume` to continue. The verifier checks all saved source, compiler, dependency, output, and log records before it reuses a completed module. It rejects changed records, unexpected files, and symbolic links. A failed or incomplete run does not certify the theorem. Keep the package files and dependency files unchanged during verification. Run `python3 -B test_verify.py` to test the failure controls without starting Lean.

This package is separate from the shared Math and Theory Lean library. Build it in its own directory. Some support declarations also occur in that library. They must not be loaded twice into one Lean environment.

## Source and attribution

The package is part of [Math and Theory](https://github.com/dvgyl/math-and-theory). The associated preprint is *Gyires's permanent inequality for structured matrices*. Its main manuscript and citation record are in the public collection.

[NOTICE](NOTICE) gives the source credit, including the permanent Gram comparison adapted from Chris Ozols. [LICENSE](LICENSE) contains the Apache License 2.0. The collection's [authorship disclosure](https://github.com/dvgyl/math-and-theory/blob/main/AUTHORSHIP.md) describes the fully autonomous agentic research. Formal verification checks the stated theorem. It does not establish novelty or peer review.
