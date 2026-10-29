# Permanent contractions for rank-two doubly stochastic matrices

This package proves the rank-two contractions for every real doubly stochastic matrix of order n with 2 ≤ n ≤ 8. A doubly stochastic matrix has nonnegative entries. Each row sum and each column sum is one. The rank is the dimension of the row space. The theorem assumes rank at most two.

Put d=per(A) and c=n!/n^n. The permanent is the sum, over all permutations, of the products that select one entry from each row and column. The package proves

    per(AAᵀ) ≤ d,  per(AᵀA) ≤ d,  per(A²) ≤ d,
    0 ≤ 4d(d-c) ≤ 4d²-c[per(AAᵀ)+per(AᵀA)+2per(A²)],
    c per(AAᵀ) ≤ d².

Equality in the combined Gyires inequality holds exactly when every entry is 1/n. Zero entries are allowed. The statement uses Mathlib's actual matrix rank, doubly stochastic set, permanent, matrix product, and transpose. It does not assume a matrix factorization or a coefficient certificate.

The verified range in this package ends at order 8. The broader manuscript claim through order 15 is not certified by this package. Orders zero and one are outside this package's main statement.

## Proof

The proof first derives a parameter representation from the rank condition. It treats the uniform matrix separately. In the other case, both parameter vectors lie in [0,1] and have the same sum t, with 0<t<n.

The permanent has an exact expansion in elementary symmetric polynomials. The normalized Gram-minus-permanent difference is a separately convex function of two Bernoulli-sum laws. Its maximum occurs at parameter vectors whose entries strictly between zero and one are equal. Exact integer polynomial checks cover every resulting profile pair in the stated dimension range. The checks use Lean's kernel. A permanent Cauchy–Schwarz comparison supplies the A² bound.

[THEOREMS.md](THEOREMS.md) gives the source map. [sources.json](sources.json) lists the 160 source modules and their hashes.

## Reproduce the checks

Install Python 3.11 or later and the Lean toolchain manager `elan`. Run these commands in this directory:

```sh
python3 check_package.py
lake exe cache get
python3 verify.py
```

The package pins Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The dependency revisions are fixed in `lake-manifest.json`. The cache command retrieves dependency build files. The verifier checks the dependency revisions and records the exact dependency object hashes.

The verifier compiles all project modules in a fresh `.verification/build` directory. It clears inherited Lean search paths and permits only the new project build, the locked dependency libraries, and the selected toolchain. It uses one compiler, an 8 GiB memory limit, and a ten-minute limit per source. It rejects stale project outputs, changed files, symbolic links, incomplete coverage, warnings, and compiler errors.

The same command checks the final theorem's axiom report. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. A failure or incomplete run returns a nonzero exit code. The result has `complete: true` only after every required check passes.

Use `python3 verify.py --max-seconds 600` to limit one work period. Use `python3 verify.py --resume` to continue a saved run. The verifier checks the saved source, compiler, dependency, output, and log hashes before it reuses a module. Run `python3 -B test_verify.py` to test the failure controls without starting Lean.

Build this package in its own directory. Some support declarations also occur in the shared Math and Theory Lean library. They must not be loaded twice in one Lean environment.

## Source and authorship

This package is part of [Math and Theory](https://github.com/dvgyl/math-and-theory). The associated preprint is *Gyires's permanent inequality for structured matrices*. [NOTICE](NOTICE) gives source credit. [LICENSE](LICENSE) contains the Apache License 2.0.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.

The repository's [authorship statement](https://github.com/dvgyl/math-and-theory/blob/main/AUTHORSHIP.md) gives the full disclosure. Formal verification checks the stated theorem. It does not establish novelty or expert or peer review.
